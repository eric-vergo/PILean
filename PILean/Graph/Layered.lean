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
5. **Edges**: through the points of their chains as smooth cubic Bézier curves, monotone in the
   direction of the layers with ends perpendicular to them (`Routing.spline`), or as
   horizontal and vertical segments with rounded corners (`Routing.orthogonal`); reversed edges
   are drawn in their own direction; edges meet a node's side at points spread by `portStep`;
   directed edges end in an arrowhead at the target's outline; labels sit on plates at the
   middle of their edges; self-loops are small loops beside the node.

Everything is computed in a frame whose first coordinate runs across the layers and the second
along them, and mapped to the picture at the end (swapped for `Direction.leftToRight`).
Positions are whole pixels.

**Clusters** are drawn as boxes around their members (the bounding box, padded). After the crossing
reduction the members of a cluster are gathered and the clusters put in the same order in every
layer, but nothing keeps other nodes out of a cluster's box, so a box can contain nodes that are
not members (and boxes can overlap).

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

## Main definitions

* `Graph.layout`, `Plan`, `layoutPlan`, `routeOne`, `routeAll`.
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
  let lay0 := assignLayers pos n pairs.toList o.layerWork
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
  let order := if clustered then reduceClustered tree bs order0 o.sweeps else order0
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
  -- a gap that edges cross far sideways is made taller (up to three times), so that those
  -- edges do not run flat just under the boxes of the layer above
  let mut sideways : Array Float := Array.replicate order.size 0
  for c in chains do
    for j in [0:c.size - 1] do
      let a := c.getD j 0
      let b := c.getD (j + 1) 0
      let la := layerAll.getD a 0
      sideways := sideways.modify la (max · ((x.getD a 0) - (x.getD b 0)).abs)
  let mut levels : Array Float := Array.replicate order.size 0
  let mut t : Float := 0
  let mut prev : Float := 0
  for l in [0:order.size] do
    let th := thick.getD l 0
    let g := if l == 0 then gap else min (3 * gap) (max gap (sideways.getD (l - 1) 0 / 5))
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
  -- orthogonal routes: the horizontal runs of each gap get tracks (greedy interval colouring)
  let mut runs : Array (Array Float) := chains.map fun c => Array.replicate (c.size - 1) 0.5
  if o.routing == .orthogonal then
    let mut gaps : Array (Array (Float × Float × Nat × Nat)) := Array.replicate order.size #[]
    for k in [0:m] do
      let c := chains.getD k #[]
      for j in [0:c.size - 1] do
        let a := across.getD (c.getD j 0) 0
        let b := across.getD (c.getD (j + 1) 0) 0
        if (a - b).abs > 0.5 then
          gaps := gaps.modify (layerAll.getD (c.getD j 0) 0) (·.push (min a b, max a b, k, j))
    for gap in gaps do
      let segs := gap.sortStable fun p q => p.1 < q.1 || (p.1 == q.1 && (p.2.2.1 < q.2.2.1))
      let mut ends : Array Float := #[]
      let mut assigned : Array Nat := #[]
      for (lo, hi, _, _) in segs do
        let mut track := ends.size
        for i in [0:ends.size] do
          if track == ends.size && ends.getD i 0 + 6 < lo then track := i
        if track == ends.size then ends := ends.push hi else ends := ends.setIfInBounds track hi
        assigned := assigned.push track
      for i in [0:segs.size] do
        let (_, _, k, j) := segs.getD i (0, 0, 0, 0)
        let frac := (assigned.getD i 0).toFloat + 1
        runs := runs.modify k fun r => r.setIfInBounds j (frac / (ends.size.toFloat + 1))
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
        let mid := q.y + runs.getD (i - 1) 0.5 * (p.y - q.y)
        out := (out.push ⟨q.x, mid⟩).push ⟨p.x, mid⟩
    out := out.push p
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
    -- a dummy node is crossed straight along the layers through its layer's band, so the edge
    -- keeps its distance from the boxes of that layer and leaves the band perpendicular to it
    let inner : Array Point := (c.extract 1 (c.size - 1)).foldl (init := #[]) fun acc d =>
      let cx := pl.across.getD d 0
      let cy := pl.along.getD d 0
      let h := pl.band.getD d 0
      if pl.routing == .spline && h > 0.5 then acc ++ #[⟨cx, cy - h⟩, ⟨cx, cy + h⟩]
      else acc.push ⟨cx, cy⟩
    let pts : Array Point := #[⟨sx, sy⟩] ++ inner ++ #[⟨ex, ey⟩]
    -- the end that carries the arrowhead moves in by the head's length
    let cut := arrowLength - 1
    let shortened : Array Point :=
      if !arrow then pts
      else if rev then pts.modify 0 fun p => ⟨p.x, p.y + cut⟩
      else pts.modify (pts.size - 1) fun p => ⟨p.x, p.y - cut⟩
    let path : Path := match pl.routing with
      | .spline =>
        let ps := splinePieces shortened
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
