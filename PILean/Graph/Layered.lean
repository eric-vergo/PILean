/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Graph.Layout
import PILean.Graph.Layering
import PILean.Graph.Ordering
import PILean.Graph.Coordinates
import PILean.Graph.Simplex
import PILean.Graph.Compound
import PILean.Sort

/-!
# The layered layout

`Graph.layout` draws a directed graph in layers (Sugiyama, Tagawa and Toda; Gansner et al.), in
five phases, each with its work bounded by its input:

1. **Cycle removal** (`elsPositions`, `PILean.Graph.Layering`): edges that point backwards in a
   greedy order are reversed for the layout; self-loops are set aside.
2. **Layers** (`assignLayers`): the layers of least total edge span by network simplex
   (`PILean.Graph.Simplex`), balanced, and relaxed by `fixLayers` so that every edge points to a
   deeper layer. When an edge has a label, the layers
   are doubled so that the label has a layer of its own half-way along its edge.
3. **Crossing reduction** (`orderLayers`, `PILean.Graph.Ordering`): long edges are cut into
   chains of dummy nodes; weighted-median sweeps and transposition from a depth-first and a
   breadth-first start, counting crossings in `O(E log V)` per round.
4. **Coordinates** (`assignBreadth`, `refineBreadth`, `simplexBreadth`,
   `PILean.Graph.Coordinates`): Brandes and Köpf's four alignments, balanced, which keep the
   chains of long edges straight, refined, then improved by network simplex on the weighted
   horizontal length of the edges within a bound on the work; node widths come from the labels
   measured with the style's text engine.
5. **Edges**: straight through the band of each layer they cross, as cubic curves across the
   gaps that leave and enter perpendicular to the layers, or as horizontal runs on tracks of
   their own where a step goes far sideways (`stationPieces`), so that no edge passes near a
   node it does not end at (`clearanceProblems`); or as horizontal and vertical segments with
   rounded corners (`Routing.orthogonal`); reversed edges are drawn in their own direction;
   edges meet a node's side at points spread by `portStep`; directed edges end in an arrowhead
   at the target's outline; labels sit on plates at the middle of their edges; self-loops are
   small loops beside the node.

Everything is computed in a frame whose first coordinate runs across the layers and the second
along them, and mapped to the picture at the end (swapped for `Direction.leftToRight`).
Positions are whole pixels.

**Clusters** (`PILean.Graph.Compound`) keep their nodes together in every layer between border
nodes whose coordinates are one per side, so that a cluster's box holds exactly its nodes and
the boxes of two clusters nest or are apart (`PILean.Graph.Check.clusterProblems` states the
condition; the tests check it). Their layers are pulled together first (`compactGroups`), and
gaps grow where cluster sides and titles need room.

The number of dummy nodes is the sum of the spans of the edges, at most `E × (L - 1)` for `L`
layers; when the real and dummy nodes together would be more than
`LayeredOptions.maxLayoutNodes`, long edges get no dummy nodes and are drawn straight between
their ends. With that cap, the work allowed to the two network simplex phases
(`layerWork`, `coordinateWork`) and the sweeps, every phase's work is bounded by a function of
the numbers of nodes and edges that is at most `O((V + E) log (V + E))` times the sweeps, plus
the two work budgets.

## References

* Sugiyama, Tagawa, Toda, *Methods for visual understanding of hierarchical system structures*,
  IEEE Transactions on Systems, Man, and Cybernetics 11 (1981).
* Gansner, Koutsofios, North, Vo, *A technique for drawing directed graphs*, IEEE Transactions
  on Software Engineering 19 (1993).
* Eades, Lin, Smyth, *A fast and effective heuristic for the feedback arc set problem*,
  Information Processing Letters 47 (1993).
* Barth, Jünger, Mutzel, *Simple and efficient bilayer cross counting*, Journal of Graph
  Algorithms and Applications 8 (2004).
* Brandes, Köpf, *Fast and simple horizontal coordinate assignment*, Graph Drawing 2001,
  Lecture Notes in Computer Science 2265.
* Sander, *Layout of compound directed graphs*, Technical Report A/03/96, Universität des
  Saarlandes (1996).

## Main definitions

* `Graph.layout`, `Plan`, `layoutPlan`, `stationPieces`, `routeOne`, `routeAll`.
-/

namespace PILean.Graph

/-- What the routing of the edges needs from the earlier phases, all in the layers' frame. -/
structure Plan where
  /-- The direction of the layers. -/
  dir : Direction
  /-- How edges are drawn. -/
  routing : Routing
  /-- Whether the graph is directed. -/
  directedGraph : Bool
  /-- The box of every real node. -/
  frameBoxes : Array Box
  /-- The outline of every real node. -/
  shapes : Array NodeShape
  /-- For every valid edge, its chain of nodes (real and dummy) from the upper end to the lower;
  empty for a self-loop. -/
  chains : Array (Array Nat)
  /-- For every valid edge, whether it is drawn against the direction of the layers. -/
  reversed : Array Bool
  /-- The centre of every node (dummy nodes included) across the layers. -/
  across : Array Float
  /-- The centre of every node's layer along the layers. -/
  along : Array Float
  /-- Where every edge leaves the upper node, relative to the node's centre. -/
  startOffset : Array Float
  /-- Where every edge enters the lower node, relative to the node's centre. -/
  endOffset : Array Float
  /-- The size of the plate of every edge label in the frame (across, along). -/
  plates : Array (Float × Float)
  /-- For orthogonal routes: for every edge and each step of its chain, where the horizontal run
  lies between the two levels (a fraction), so that runs in one gap use different tracks. -/
  runs : Array (Array Float) := #[]
  /-- The half thickness of every node's layer along the layers (the band the layer's boxes
  stay in), dummy nodes included. -/
  band : Array Float := #[]
  /-- The box of every cluster that has nodes, in the frame, with the cluster's number; `none`
  when the graph has no cluster with nodes (the boxes are then not computed here). -/
  clusterFrames : Option (Array (Nat × Box)) := none

/-- The vertical offset of a node's boundary at the horizontal offset `off` from its centre
(the half-height, less where an ellipse curves in). -/
def boundaryOffset (box : Box) (shape : NodeShape) (off : Float) : Float :=
  match shape with
  | .ellipse =>
    let r := min 0.95 (off.abs / max 1 (box.width / 2))
    box.height / 2 * (1 - r * r).sqrt
  | _ => box.height / 2

/-- The phases one to four: the plan for routing the edges. -/
def layoutPlan (g : Graph) (o : LayeredOptions) (st : Style) : Plan := Id.run do
  let n := g.nodes.size
  let ve := g.validEdges
  let m := ve.size
  let lr := o.direction == .leftToRight
  let dims := g.nodes.map (nodeSize st o)
  let nb := dims.map fun (w, h) => if lr then h else w
  let nt := dims.map fun (w, h) => if lr then w else h
  let plateFrame := fun (s : String) =>
    let (w, h) := plateSize st s
    if lr then (h, w) else (w, h)
  -- room beside nodes with self-loops
  let mut loopExtra : Array Float := Array.replicate n 0
  for (_, e) in ve do
    if e.src == e.dst then
      let extra := 18 + (if e.label.isEmpty then 0 else (plateFrame e.label).1 + 4)
      loopExtra := loopExtra.modify e.src (max · extra)
  -- phases 1 and 2
  let pairs : Array (Nat × Nat) := ve.filterMap fun (_, e) =>
    if e.src != e.dst then some (e.src, e.dst) else none
  let pos := elsPositions n pairs
  let lay0 := assignLayers pos n pairs.toList o.layerWork (ClusterTree.of g).nodeCluster
  let hasLabels := ve.any fun (_, e) => e.src != e.dst && !e.label.isEmpty
  let lay := if hasLabels then lay0.map (· * 2) else lay0
  let oriented : Array (Option (Nat × Nat)) := ve.map fun (_, e) =>
    if e.src == e.dst then none
    else if before pos e.src e.dst then some (e.src, e.dst) else some (e.dst, e.src)
  let reversed : Array Bool := ve.map fun (_, e) => e.src != e.dst && !before pos e.src e.dst
  let (chains, layerAll) := buildChains lay oriented o.maxLayoutNodes
  let size := layerAll.size
  -- phase 3
  let (up, down) := chainNeighbours size chains
  let tree := ClusterTree.of g
  let clustered := tree.nodeCluster.any (·.isSome)
  -- the block of every real and dummy node: a dummy node stands in the innermost cluster that
  -- holds both ends of its edge
  let block : Array (Option Nat) := Id.run do
    let mut b : Array (Option Nat) := (Array.range size).map fun v => tree.nodeCluster.getD v none
    if clustered then
      for c in chains do
        if c.size ≥ 3 then
          let l := tree.lca (tree.nodeCluster.getD (c.getD 0 0) none)
            (tree.nodeCluster.getD (c.getD (c.size - 1) 0) none)
          for j in [1:c.size - 1] do b := b.setIfInBounds (c.getD j 0) l
    return b
  let order0 := orderLayers layerAll up down o.sweeps
  let bs : Borders := if clustered then addBorders tree layerAll up down block
    else { layerAll, up, down, block, part := Array.replicate size .node,
           span := #[], firstBorders := #[] }
  let order := if clustered then reduceClustered tree bs order0 up down o.sweeps else order0
  let total := bs.layerAll.size
  -- sizes: nodes, label plates (border nodes have no width)
  let mut bw : Array Float := (Array.range total).map fun v =>
    if v < n then nb.getD v 0 + loopExtra.getD v 0 else 0
  let mut thick : Array Float := Array.replicate order.size 0
  for v in [0:n] do
    thick := thick.modify (layerAll.getD v 0) (max · (nt.getD v 0))
  let mut plates : Array (Float × Float) := Array.replicate m (0, 0)
  for k in [0:m] do
    let c := chains.getD k #[]
    let e := (ve.getD k (0, default)).2
    if !e.label.isEmpty then
      let (pb, pt) := plateFrame e.label
      plates := plates.setIfInBounds k (pb, pt)
      if c.size ≥ 3 then
        let mid := c.getD ((c.size - 1) / 2) 0
        bw := bw.setIfInBounds mid pb
        thick := thick.modify (layerAll.getD mid 0) (max · pt)
  -- phase 4
  let labelRoom := 12 + st.noteSize * 1.2
  let pad : Float := 12
  let base := separation n bw o.nodeGap o.edgeGap 0 #[]
  let sep := borderSeparation bs base bw pad (pad + if lr then labelRoom else 0) 12 16
  let x0 := assignBreadth total n order bs.up bs.down sep bw
  let x1 := refineBreadth total n chains order bs.up bs.down sep bw x0 o.refine
  let toHalf := fun (f : Float) => Int.ofNat (f * 2).ceil.toUInt64.toNat
  let extra : Array (Nat × Nat × Int × Int) := (Array.range g.clusters.size).filterMap fun c =>
    (bs.firstBorders.getD c none).map fun (lv, rv) =>
      let need := if lr then 2 * pad
        else st.text.measure (g.clusters.getD c default).name st.noteSize + 2 * pad
      (lv, rv, toHalf need, 1)
  let x := if clustered then
      simplexBreadth total n chains order sep bw x1 8 o.coordinateWork (borderVariable bs) extra
    else simplexBreadth total n chains order sep bw x1 8 o.coordinateWork
  let gap := if hasLabels then o.layerGap / 2 else o.layerGap
  -- room above and below the nodes for the clusters' sides and titles (nested clusters that
  -- start or end in the same layer stack)
  let k := g.clusters.size
  let mut topExtra : Array Float := Array.replicate k 0
  let mut bottomExtra : Array Float := Array.replicate k 0
  for i in [0:k] do
    let c := k - 1 - i
    if let some (a, b) := bs.span.getD c none then
      let t := topExtra.getD c 0 + pad + (if lr then 0 else labelRoom)
      let u := bottomExtra.getD c 0 + pad
      topExtra := topExtra.setIfInBounds c t
      bottomExtra := bottomExtra.setIfInBounds c u
      if let some p := tree.parent.getD c none then
        if let some (pa, pb) := bs.span.getD p none then
          if pa == a then topExtra := topExtra.modify p (max · t)
          if pb == b then bottomExtra := bottomExtra.modify p (max · u)
  let mut topNeed : Array Float := Array.replicate order.size 0
  let mut bottomNeed : Array Float := Array.replicate order.size 0
  for c in [0:k] do
    if let some (a, b) := bs.span.getD c none then
      if tree.parent.getD c none |>.all (fun p => (bs.span.getD p none).all (·.1 != a)) then
        topNeed := topNeed.modify a (max · (topExtra.getD c 0))
      if tree.parent.getD c none |>.all (fun p => (bs.span.getD p none).all (·.2 != b)) then
        bottomNeed := bottomNeed.modify b (max · (bottomExtra.getD c 0))
  -- the horizontal runs of each gap get tracks (greedy interval colouring): every step of an
  -- orthogonal route that moves sideways, and every step of a curve that moves sideways more
  -- than eight times the gap (drawn as a run half-way down the gap, so that it keeps
  -- away from the boxes above and below); a value below zero marks a step without a run
  let mut runs : Array (Array Float) := chains.map fun c => Array.replicate (c.size - 1) (-1)
  let mut tracks : Array Nat := Array.replicate order.size 0
  let mut gaps : Array (Array (Float × Float × Nat × Nat)) := Array.replicate order.size #[]
  for k in [0:m] do
    let c := chains.getD k #[]
    for j in [0:c.size - 1] do
      let a := (x.getD (c.getD j 0) 0).round
      let b := (x.getD (c.getD (j + 1) 0) 0).round
      let run := if o.routing == .orthogonal then (a - b).abs > 0.5
        else (a - b).abs > 8 * gap
      if run then
        gaps := gaps.modify (layerAll.getD (c.getD j 0) 0) (·.push (min a b, max a b, k, j))
  for li in [0:gaps.size] do
    let segs := gaps.getD li #[]
    -- a run going right must lie below every overlapping run going right that starts further
    -- right (otherwise that one's way down crosses it), and a run going left below every
    -- overlapping one going left that starts further left; the runs going right take the
    -- upper tracks, those going left the lower ones
    let place := fun (rightward : Bool) => Id.run do
      let idx := ((Array.range segs.size).filter fun i =>
        let (_, _, k, j) := segs.getD i (0, 0, 0, 0)
        let c := chains.getD k #[]
        let goesRight := x.getD (c.getD (j + 1) 0) 0 ≥ x.getD (c.getD j 0) 0
        goesRight == rightward).sortStable fun i i' =>
          let (lo, hi, _, _) := segs.getD i (0, 0, 0, 0)
          let (lo', hi', _, _) := segs.getD i' (0, 0, 0, 0)
          if rightward then lo > lo' || (lo == lo' && hi < hi')
          else hi < hi' || (hi == hi' && lo > lo')
      let mut placed : Array (Float × Float × Nat) := #[]
      let mut out : Array (Nat × Nat) := #[]
      let mut depth := 0
      for i in idx do
        let (lo, hi, _, _) := segs.getD i (0, 0, 0, 0)
        let t := placed.foldl (fun t (plo, phi, pt) =>
          if plo < hi + 6 && lo < phi + 6 then max t (pt + 1) else t) 0
        placed := placed.push (lo, hi, t)
        out := out.push (i, t)
        depth := max depth (t + 1)
      return (out, depth)
    let (rs, rd) := place true
    let (ls, ld) := place false
    let total := rd + ld
    tracks := tracks.setIfInBounds li total
    for (i, t) in rs ++ ls.map (fun (i, t) => (i, t + rd)) do
      let (_, _, k, j) := segs.getD i (0, 0, 0, 0)
      runs := runs.modify k fun r =>
        r.setIfInBounds j ((t.toFloat + 1) / (total.toFloat + 1))
  let mut levels : Array Float := Array.replicate order.size 0
  let mut t : Float := 0
  let mut prev : Float := 0
  for l in [0:order.size] do
    let th := thick.getD l 0
    -- a gap with many runs grows (up to `sidewaysGap` times) to keep them three pixels apart
    let g := if l == 0 then gap
      else min (o.sidewaysGap * gap) (max gap ((tracks.getD (l - 1) 0 + 1).toFloat * 3 + 16))
    let g := if l == 0 then g
      else max g (bottomNeed.getD (l - 1) 0 + topNeed.getD l 0 + 12)
    t := if l == 0 then th / 2 + topNeed.getD 0 0 else t + prev / 2 + g + th / 2
    prev := th
    levels := levels.setIfInBounds l t.round
  let across := (Array.range size).map fun v =>
    if v < n then (x.getD v 0 - loopExtra.getD v 0 / 2).round else (x.getD v 0).round
  let along := layerAll.map fun l => levels.getD l 0
  let frameBoxes := (Array.range n).map fun v =>
    let cb := across.getD v 0
    let lv := along.getD v 0
    let hb := nb.getD v 0 / 2
    let ht := nt.getD v 0 / 2
    (⟨cb - hb, lv - ht, cb + hb, lv + ht⟩ : Box)
  -- where the edges meet the nodes' sides
  let mut outs : Array (Array (Float × Nat)) := Array.replicate n #[]
  let mut ins : Array (Array (Float × Nat)) := Array.replicate n #[]
  for k in [0:m] do
    let c := chains.getD k #[]
    if c.size ≥ 2 then
      outs := outs.modify (c.getD 0 0) (·.push (across.getD (c.getD 1 0) 0, k))
      ins := ins.modify (c.getD (c.size - 1) 0)
        (·.push (across.getD (c.getD (c.size - 2) 0) 0, k))
  let spread := fun (groups : Array (Array (Float × Nat))) =>
    Id.run do
      let mut off : Array Float := Array.replicate m 0
      for v in [0:n] do
        let ps := (groups.getD v #[]).sortStable fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)
        let cnt := ps.size
        -- spread over the node's side, keeping clear of its rounded corners
        let step := min o.portStep ((nb.getD v 0 - 16) / max 1 (cnt.toFloat - 1))
        for j in [0:cnt] do
          off := off.setIfInBounds (ps.getD j (0, 0)).2 ((j.toFloat - (cnt.toFloat - 1) / 2) * step)
      return off
  let band := layerAll.map fun l => thick.getD l 0 / 2
  let clusterFrames : Option (Array (Nat × Box)) :=
    if !clustered then none
    else some <| (Array.range k).filterMap fun c =>
      match bs.span.getD c none, bs.firstBorders.getD c none with
      | some (a, b), some (lv, rv) =>
        some (c, ⟨(x.getD lv 0).round, levels.getD a 0 - thick.getD a 0 / 2 - topExtra.getD c 0,
          (x.getD rv 0).round, levels.getD b 0 + thick.getD b 0 / 2 + bottomExtra.getD c 0⟩)
      | _, _ => none
  return { dir := o.direction, routing := o.routing, directedGraph := g.directed, frameBoxes,
           shapes := g.nodes.map (·.shapeOf), chains, reversed, across, along,
           startOffset := spread outs, endOffset := spread ins, plates, runs, band,
           clusterFrames }

/-- The vertices of the orthogonal route through the points: at each step across the layers a
horizontal run at the given fraction of the way between the two levels. -/
def orthVertices (pts : Array Point) (runs : Array Float) : Array Point := Id.run do
  let mut out : Array Point := #[]
  for i in [0:pts.size] do
    let p := pts.getD i ⟨0, 0⟩
    if i > 0 then
      let q := pts.getD (i - 1) ⟨0, 0⟩
      if (p.x - q.x).abs > 0.5 then
        let r := runs.getD (i - 1) 0.5
        let mid := q.y + (if r < 0 then 0.5 else r) * (p.y - q.y)
        out := (out.push ⟨q.x, mid⟩).push ⟨p.x, mid⟩
    out := out.push p
  return out

/-- The straight piece from `p` to `q`. -/
def linePiece (p q : Point) : Piece :=
  (p, ⟨p.x + (q.x - p.x) / 3, p.y + (q.y - p.y) / 3⟩,
    ⟨p.x + 2 * (q.x - p.x) / 3, p.y + 2 * (q.y - p.y) / 3⟩, q)

/-- The curve across a gap from `a` down to `b`, leaving and entering perpendicular to the
layers. -/
def gapPiece (a b : Point) : Piece :=
  let h := (b.y - a.y) / 3
  (a, ⟨a.x, a.y + h⟩, ⟨b.x, b.y - h⟩, b)

/-- The route across a gap from `a` down to `b` that goes far sideways: down from `a`, a
horizontal run at `y`, down into `b`, with rounded corners. -/
def stairPieces (a b : Point) (y : Float) : Array Piece :=
  let r := min 24 (min (min (y - a.y) (b.y - y)) ((b.x - a.x).abs / 2)) |> max 0
  let s : Float := if b.x ≥ a.x then 1 else -1
  -- a quarter circle as a cubic: the control points 0.5523 of the radius from the ends
  let k := 0.5523 * r
  let c1 : Point := ⟨a.x, y - r⟩
  let c2 : Point := ⟨a.x + s * r, y⟩
  let c3 : Point := ⟨b.x - s * r, y⟩
  let c4 : Point := ⟨b.x, y + r⟩
  #[linePiece a c1, (c1, ⟨a.x, y - r + k⟩, ⟨a.x + s * (r - k), y⟩, c2), linePiece c2 c3,
    (c3, ⟨b.x - s * (r - k), y⟩, ⟨b.x, y + r - k⟩, c4), linePiece c4 b]

/-- The pieces of a curve through stations (the points where it enters and leaves each node
of its chain, top to bottom): straight through a station, `gapPiece` across a gap, or
`stairPieces` at the fraction `runs[j]` of gap `j` when that is not negative. -/
def stationPieces (stations : Array (Point × Point)) (runs : Array Float) : Array Piece :=
  Id.run do
  let mut out : Array Piece := #[]
  for j in [0:stations.size] do
    let (p, q) := stations.getD j (⟨0, 0⟩, ⟨0, 0⟩)
    if j > 0 then
      let a := (stations.getD (j - 1) (⟨0, 0⟩, ⟨0, 0⟩)).2
      let r := runs.getD (j - 1) (-1)
      -- the runs keep a few pixels from both sides of the gap
      let m := min 8 ((p.y - a.y) / 4)
      out := out ++ (if r ≥ 0 then stairPieces a p (a.y + m + r * (p.y - a.y - 2 * m))
        else #[gapPiece a p])
    if q.y > p.y then out := out.push (linePiece p q)
  return out

/-- The box of a plate of size `(w, h)` centred at `c`. -/
def plateAt (c : Point) (w h : Float) : Box :=
  ⟨c.x - w / 2, c.y - h / 2, c.x + w / 2, c.y + h / 2⟩

/-- The route of the `k`-th valid edge, which is edge `i` of the graph. The index of the result
is `i`, whatever the route. -/
def routeOne (pl : Plan) (k i : Nat) (e : Graph.Edge) : RoutedEdge :=
  let frame := pl.dir.frame
  let arrow := pl.directedGraph && e.directed
  let plate := pl.plates.getD k (0, 0)
  if e.src == e.dst then
    let fb := pl.frameBoxes.getD e.src ⟨0, 0, 0, 0⟩
    let (p, h) := loopGeometry fb arrow
    let cy := (fb.y0 + fb.y1) / 2
    let q := min (fb.height / 4) 8
    let label : Option EdgeLabel :=
      if e.label.isEmpty then none
      else
        some { text := e.label,
               box := pl.dir.box (plateAt ⟨fb.x1 + 22 + plate.1 / 2, cy⟩ plate.1 plate.2) }
    { index := i, src := e.src, dst := e.dst, reversed := false,
      path := p.transform frame, head := h.map (·.transform frame), label,
      points := #[frame.apply ⟨fb.x1, cy - q⟩, frame.apply ⟨fb.x1, cy + q⟩] }
  else
    let c := pl.chains.getD k #[]
    let rev := pl.reversed.getD k false
    let a := c.getD 0 0
    let b := c.getD (c.size - 1) 0
    let fa := pl.frameBoxes.getD a ⟨0, 0, 0, 0⟩
    let fz := pl.frameBoxes.getD b ⟨0, 0, 0, 0⟩
    let so := pl.startOffset.getD k 0
    let eo := pl.endOffset.getD k 0
    let sx := (fa.x0 + fa.x1) / 2 + so
    let ex := (fz.x0 + fz.x1) / 2 + eo
    let sy := (fa.y0 + fa.y1) / 2 + boundaryOffset fa (pl.shapes.getD a .round) so
    let ey := (fz.y0 + fz.y1) / 2 - boundaryOffset fz (pl.shapes.getD b .round) eo
    -- each node of the chain is a station the edge enters and leaves: a dummy node is crossed
    -- straight along the layers through its layer's band (curves), so the edge keeps its distance
    -- from the boxes of that layer and leaves the band perpendicular to it
    let cut := arrowLength - 1
    let first : Point := if arrow && rev then ⟨sx, sy + cut⟩ else ⟨sx, sy⟩
    let last : Point := if arrow && !rev then ⟨ex, ey - cut⟩ else ⟨ex, ey⟩
    let stations : Array (Point × Point) :=
      #[(first, first)] ++ (c.extract 1 (c.size - 1)).map (fun d =>
        let cx := pl.across.getD d 0
        let cy := pl.along.getD d 0
        let h := pl.band.getD d 0
        if pl.routing == .spline && h > 0.5 then (⟨cx, cy - h⟩, ⟨cx, cy + h⟩)
        else (⟨cx, cy⟩, ⟨cx, cy⟩)) ++ #[(last, last)]
    -- the points of the route: its two ends on the outlines and the centres of its dummy nodes
    let pts : Array Point := #[⟨sx, sy⟩] ++ (c.extract 1 (c.size - 1)).map (fun d =>
      (⟨pl.across.getD d 0, pl.along.getD d 0⟩ : Point)) ++ #[⟨ex, ey⟩]
    let shortened : Array Point := stations.map (·.1)
    let runs := pl.runs.getD k #[]
    let path : Path := match pl.routing with
      | .spline =>
        let ps := stationPieces stations runs
        piecesPath (if rev then reversePieces ps else ps)
      | .orthogonal =>
        let vs := orthVertices shortened (pl.runs.getD k #[])
        roundedPolyline (if rev then vs.reverse else vs) 8
    let head : Option Path :=
      if !arrow then none
      else if rev then some (arrowPath ⟨sx, sy⟩ ⟨0, -1⟩)
      else some (arrowPath ⟨ex, ey⟩ ⟨0, 1⟩)
    let label : Option EdgeLabel :=
      if e.label.isEmpty then none
      else
        let centre : Point :=
          if c.size ≥ 3 then
            let d := c.getD ((c.size - 1) / 2) 0
            ⟨pl.across.getD d 0, pl.along.getD d 0⟩
          else ⟨(sx + ex) / 2, (sy + ey) / 2⟩
        some { text := e.label, box := pl.dir.box (plateAt centre plate.1 plate.2) }
    { index := i, src := e.src, dst := e.dst, reversed := rev, path := path.transform frame,
      head := head.map (·.transform frame), label,
      points := (if rev then pts.reverse else pts).map frame.apply }

/-- The routes of all the valid edges `ve` (each with its position in the graph's `edges`), in
order. -/
def routeAll (pl : Plan) (ve : Array (Nat × Graph.Edge)) : Array RoutedEdge :=
  ve.mapIdx fun k (i, e) => routeOne pl k i e

/-- The layout before it is fitted to its margins (see `Graph.layout`). -/
def layoutRaw (g : Graph) (o : LayeredOptions) (st : Style) : Layout :=
  let pl := layoutPlan g o st
  let nodes := (g.nodes.mapIdx fun i nd =>
    nodeBoxOf st i nd (o.direction.box (pl.frameBoxes.getD i ⟨0, 0, 0, 0⟩)))
  let clusters := match pl.clusterFrames with
    | some fs => fs.map fun (c, b) =>
      ({ name := (g.clusters.getD c default).name, index := c, box := o.direction.box b } :
        ClusterBox)
    | none => clusterBoxes g nodes
  { nodes, edges := routeAll pl g.validEdges, clusters }

/-- The layered layout of the graph: a box for every node, a route for every valid edge (in the
order of `Graph.validEdges`), a box for every cluster with a member, and the size of the
picture, with `st.margin` of room around everything. The graph's own order of nodes and edges
decides every tie, so the result is the same on every run. -/
def layout (g : Graph) (o : LayeredOptions := {}) (st : Style := {}) : Layout :=
  (layoutRaw g o st).fit st.margin

end PILean.Graph
