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
import PILean.Graph.Route
import PILean.Graph.Nested
import PILean.Sort

/-!
# The layered layout

`Graph.layout` draws a directed graph in layers (Sugiyama, Tagawa and Toda; Gansner et al.), in
five phases, each with its work bounded by its input:

1. **Cycle removal** (`elsPositions`, `PILean.Graph.Layering`): edges that point backwards in a
   greedy order are reversed for the layout; self-loops are set aside.
2. **Layers** (`assignWide`): the layers of least total edge span by network simplex
   (`PILean.Graph.Simplex`), balanced, the layers wider than `maxLayerWidth` split into rows, and
   relaxed by `fixLayers` so that every edge points to a deeper layer. A graph with clusters is
   layered from the inside out, every cluster keeping a block of layers to itself
   (`assignNested`, `PILean.Graph.Nested`). When an edge has a label, the layers are doubled so
   that the label has a layer of its own half-way along its edge.
3. **Crossing reduction** (`orderLayers`, `PILean.Graph.Ordering`): long edges are cut into
   chains of dummy nodes; weighted-median sweeps and transposition from a depth-first, a
   breadth-first and a bottom-up start and from more depth-first starts drawn from a fixed
   sequence, each search ending with sifting (Matuszewski, Schönfeld and Molitor), counting
   crossings in `O(E log V)` per round.
4. **Coordinates** (`assignBreadth`, `refineBreadth`, `simplexBreadth`,
   `PILean.Graph.Coordinates`): Brandes and Köpf's four alignments, balanced, which keep the
   chains of long edges straight, refined, then improved by network simplex on the weighted
   horizontal length of the edges within a bound on the work; node widths come from the labels
   measured with the style's text engine.
5. **Edges** (`PILean.Graph.Route`): the shortest route through the free space beside the
   nodes of each layer the edge crosses (`tautRoute`), drawn as one curve that rounds the bends
   of that route and stays clear of the boxes and cluster sides beside it (`fitPieces`), so that
   no edge passes near a node it does not end at (`clearanceProblems`) or turns back across the
   layers; or as horizontal and vertical segments with rounded corners (`Routing.orthogonal`);
   reversed edges are drawn in their own direction; edges meet a node's side at points spread
   by `portStep`; directed edges end in an arrowhead at the target's outline, along the end of
   the curve; labels sit on plates at the middle of their edges; self-loops are small loops
   beside the node.

Everything is computed in a frame whose first coordinate runs across the layers and the second
along them, and mapped to the picture at the end (swapped for `Direction.leftToRight`).
Positions are whole pixels.

**Clusters** (`PILean.Graph.Compound`) keep their nodes together in every layer between border
nodes whose coordinates are one per side, so that a cluster's box holds exactly its nodes and
the boxes of two clusters nest or are apart (`PILean.Graph.Check.clusterProblems` states the
condition; the tests check it). An edge between two clusters leaves the one through its lower
side and enters the other through its upper side; where an edge would pass through a cluster
that holds neither of its ends (`strays`), the first three phases (`skeleton`) are run again
with that cluster and the node or cluster the edge leads to kept one above the other, up to
`clusterRounds` times. Gaps grow where cluster sides and titles need room.

The number of dummy nodes is the sum of the spans of the edges, at most `E × (L - 1)` for `L`
layers; when the real and dummy nodes together would be more than
`LayeredOptions.maxLayoutNodes`, long edges get no dummy nodes and are drawn straight between
their ends. With that cap, the two network simplex phases are bounded by their work budgets
(`layerWork`, `coordinateWork`), and every other phase by a function of the numbers of nodes and
edges and of the options (the sweeps, the starts, the cluster rounds). Not every such function
is near-linear: sifting costs `O(k² d)` for a layer of `k` nodes of mean degree `d` (skipped
above `siftPairLimit` pairs), and the tracks of orthogonal routes cost `k (k − 1) / 2`
comparisons for `k` horizontal runs in one gap and direction; `docs/DESIGN.md` gives the cost of
each phase.

## References

* Sugiyama, Tagawa, Toda, *Methods for visual understanding of hierarchical system structures*,
  IEEE Transactions on Systems, Man, and Cybernetics 11 (1981).
* Gansner, Koutsofios, North, Vo, *A technique for drawing directed graphs*, IEEE Transactions
  on Software Engineering 19 (1993).
* Eades, Lin, Smyth, *A fast and effective heuristic for the feedback arc set problem*,
  Information Processing Letters 47 (1993).
* Barth, Jünger, Mutzel, *Simple and efficient bilayer cross counting*, Journal of Graph
  Algorithms and Applications 8 (2004).
* Matuszewski, Schönfeld, Molitor, *Using sifting for k-layer straightline crossing
  minimization*, Graph Drawing 1999, LNCS 1731.
* Brandes, Köpf, *Fast and simple horizontal coordinate assignment*, Graph Drawing 2001,
  Lecture Notes in Computer Science 2265.
* Sander, *Layout of compound directed graphs*, Technical Report A/03/96, Universität des
  Saarlandes (1996).
* Lee, Preparata, *Euclidean shortest paths in the presence of rectilinear barriers*, Networks
  14 (1984).

## Main definitions

* `Graph.layout`, `Skeleton`, `skeleton`, `strays`, `Plan`, `layoutPlan`, `routeOne`,
  `routeAll`.
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
  /-- The stretch across its layer that a route through each real or dummy node may use: up to
  the middle of the free space towards a neighbouring dummy node, and up to a few pixels from
  a neighbouring box or cluster side. -/
  lanes : Array (Float × Float) := #[]
  /-- The stretch across its layer that a curve through each real or dummy node must stay in:
  up to a few pixels from the nearest box or cluster side on either hand. -/
  walls : Array (Float × Float) := #[]
  /-- The sides of the clusters that reach from the layer of each real or dummy node into the
  next one, nearest to the node on either hand (with a few pixels of room): a curve stays
  between them on its way to the next layer. -/
  sides : Array (Float × Float) := #[]
  /-- The heights at which a route enters and leaves the layer of each real or dummy node: a
  little above and below the layer's boxes and the cluster sides that begin or end there. -/
  gates : Array (Float × Float) := #[]
  /-- The length of an arrowhead. -/
  arrowLength : Float := Graph.arrowLength
  /-- The half-width of an arrowhead. -/
  arrowHalfWidth : Float := Graph.arrowHalfWidth

/-- The vertical offset of a node's boundary at the horizontal offset `off` from its centre
(the half-height, less where an ellipse curves in). -/
def boundaryOffset (box : Box) (shape : NodeShape) (off : Float) : Float :=
  match shape with
  | .ellipse =>
    let r := min 0.95 (off.abs / max 1 (box.width / 2))
    box.height / 2 * (1 - r * r).sqrt
  | _ => box.height / 2

/-- The first three phases of the layout: the order of the nodes that decides which edges are
reversed, the layers, the chains of the edges and the order inside the layers. -/
structure Skeleton where
  /-- Whether a node is in a cluster. -/
  clustered : Bool
  /-- The order of the nodes (`before`): an edge is drawn downwards from the node that comes
  first. -/
  pos : Array Nat
  /-- For every edge of `pairs`, its chain of nodes (real and dummy) from the upper end to the
  lower. -/
  chains : Array (Array Nat)
  /-- The layer of every real and dummy node. -/
  layerAll : Array Nat
  /-- The order of the nodes of every layer, with the clusters' border nodes. -/
  order : Array (Array Nat)
  /-- The layered graph with the clusters' border nodes. -/
  bs : Borders
  deriving Inhabited

/-- The first three phases for the edges `pairs` between the nodes of `g` (see `layoutPlan`):
`nb` is the breadth of every node across its layer, `pad` the room inside a cluster's side,
`double` whether the layers are doubled to make room for edge labels, and `apart` pairs of
items of one level that the layers keep one above the other (`nestedLayers`). -/
def skeleton (g : Graph) (o : LayeredOptions) (tree : ClusterTree) (pairs : Array (Nat × Nat))
    (nb : Array Float) (pad : Float) (double : Bool) (apart : Array (Nat × Nat)) : Skeleton :=
  Id.run do
  let n := g.nodes.size
  let clustered := tree.nodeCluster.any (·.isSome)
  let rooms := nb.map (· + o.nodeGap)
  -- a graph with clusters is layered from the inside out; the order of the nodes that decides
  -- which edges are reversed is then the order of the layers
  let nested := clustered && o.nestedClusters
  let (pos, lay0) :=
    if nested then assignNested n tree pairs.toList rooms pad o.maxLayerWidth o.layerWork apart
    else
      let pos := elsPositions n pairs
      (pos, if clustered then assignLayers pos n pairs.toList o.layerWork tree.nodeCluster
        else assignWide pos n pairs.toList rooms o.maxLayerWidth o.layerWork)
  let lay := if double then lay0.map (· * 2) else lay0
  let oriented : Array (Option (Nat × Nat)) := pairs.map fun (a, b) =>
    if before pos a b then some (a, b) else some (b, a)
  let (chains, layerAll) := buildChains lay oriented o.maxLayoutNodes
  let size := layerAll.size
  let (up, down) := chainNeighbours size chains
  -- the block of every real and dummy node: a dummy node stands in the innermost cluster that
  -- holds both ends of its edge or, when the clusters have layers of their own, in the
  -- innermost cluster around one of the ends whose layers reach the dummy node's layer (the
  -- edge then leaves a cluster through its lower side and enters one through its upper side)
  let block : Array (Option Nat) := Id.run do
    let mut b : Array (Option Nat) := (Array.range size).map fun v => tree.nodeCluster.getD v none
    if clustered then
      let mut span : Array (Option (Nat × Nat)) := Array.replicate g.clusters.size none
      for v in [0:n] do
        let l := layerAll.getD v 0
        for c in tree.path (tree.nodeCluster.getD v none) do
          span := span.modify c fun
            | none => some (l, l)
            | some (lo, hi) => some (min lo l, max hi l)
      for c in chains do
        if c.size ≥ 3 then
          let ca := tree.nodeCluster.getD (c.getD 0 0) none
          let cb := tree.nodeCluster.getD (c.getD (c.size - 1) 0) none
          let both := tree.lca ca cb
          let depth := (tree.path both).size
          for j in [1:c.size - 1] do
            let d := c.getD j 0
            let l := layerAll.getD d 0
            let mut inner := both
            if nested then
              for p in [tree.path ca, tree.path cb] do
                for i in [depth:p.size] do
                  let x := p.getD i 0
                  match span.getD x none with
                  | some (lo, hi) => if lo ≤ l && l ≤ hi then inner := some x else break
                  | none => break
            b := b.setIfInBounds d inner
    return b
  -- with clusters the order is found under the cluster rules; the free order is only a start
  let order0 := orderLayers layerAll up down o.sweeps (if clustered then 0 else o.starts)
  let bs : Borders := if clustered then addBorders tree layerAll up down block
    else { layerAll, up, down, block, part := Array.replicate size .node,
           span := #[], firstBorders := #[] }
  let order := if clustered then reduceClustered tree bs order0 up down o.sweeps o.starts
    else order0
  return { clustered, pos, chains, layerAll, order, bs }

/-- The clusters that an edge passes through without ending in them, each with the items to
keep apart from it: for every step of a chain between two layers in which a cluster has nodes,
when the step begins on one side of the cluster and ends on the other, or begins inside it
though the cluster holds neither end of the edge, the cluster with the item of the cluster's
level that holds the edge's lower end and the one that holds its upper end (a node of that
level, or a cluster directly inside it; `none` for an end outside the level), as `nestedLayers`
reads them: a node by its number, a cluster by its number plus the number of nodes. Laid out
again with the cluster above the lower item, or the upper item above the cluster, the edge can
pass the cluster's lower or upper side instead. -/
def strays (tree : ClusterTree) (sk : Skeleton) : Array (Nat × Option Nat × Option Nat) :=
  Id.run do
  if !sk.clustered then return #[]
  let n := tree.nodeCluster.size
  let k := tree.parent.size
  let size := sk.layerAll.size
  let total := sk.bs.layerAll.size
  let pos := positionsOf total sk.order
  -- the clusters by layer
  let mut inLayer : Array (Array Nat) := Array.replicate sk.order.size #[]
  for c in [0:k] do
    if let some (a, b) := sk.bs.span.getD c none then
      for l in [a:b + 1] do inLayer := inLayer.modify l (·.push c)
  let borders := fun (c l : Nat) =>
    match sk.bs.span.getD c none, sk.bs.firstBorders.getD c none with
    | some (a, _), some (lv, rv) => (pos.getD (lv + 2 * (l - a)) 0, pos.getD (rv + 2 * (l - a)) 0)
    | _, _ => (0, 0)
  -- 0 before the cluster, 1 inside, 2 after
  let side := fun (c l v : Nat) =>
    let p := pos.getD v 0
    if p < (borders c l).1 then 0 else if p > (borders c l).2 then 2 else 1
  let mut out : Array (Nat × Option Nat × Option Nat) := #[]
  for chain in sk.chains do
    if chain.size < 2 then continue
    let upper := chain.getD 0 0
    let lower := chain.getD (chain.size - 1) 0
    let ca := tree.nodeCluster.getD upper none
    let cb := tree.nodeCluster.getD lower none
    for j in [0:chain.size - 1] do
      let u := chain.getD j 0
      let w := chain.getD (j + 1) 0
      if u ≥ size || w ≥ size then continue
      let l := sk.layerAll.getD u 0
      if sk.layerAll.getD w 0 != l + 1 then continue
      for c in inLayer.getD l #[] do
        let spans := match sk.bs.span.getD c none with
          | some (_, b) => l + 1 ≤ b
          | none => false
        if !spans || tree.holdsOpt c ca || tree.holdsOpt c cb then continue
        if side c l u != side c (l + 1) w || side c l u == 1 then
          -- the item of the cluster's level that holds an end
          let level := tree.parent.getD c none
          let depth := (tree.path level).size
          let item := fun (v : Nat) =>
            let path := tree.path (tree.nodeCluster.getD v none)
            let inLevel := match level with
              | none => true
              | some p => path.contains p
            if !inLevel then none
            else match path[depth]? with
              | some y => some (n + y)
              | none => some v
          let entry := (n + c, item lower, item upper)
          if !out.contains entry then out := out.push entry
  return out

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
  -- phases 1 to 3; while an edge would pass through a cluster that holds neither of its ends,
  -- the layers are found again with that cluster and the item the edge leads to kept apart
  let pairs : Array (Nat × Nat) := ve.filterMap fun (_, e) =>
    if e.src != e.dst then some (e.src, e.dst) else none
  let hasLabels := ve.any fun (_, e) => e.src != e.dst && !e.label.isEmpty
  let pad : Float := 12
  let tree := ClusterTree.of g
  let sk := Id.run do
    let mut apart : Array (Nat × Nat) := #[]
    let mut sk := skeleton g o tree pairs nb pad hasLabels apart
    let mut found := strays tree sk
    let mut best := sk
    let mut least := found.size
    for _ in [0:if o.nestedClusters then o.clusterRounds else 0] do
      -- the cluster above the item the edge leads to; where that is in force already, the
      -- item the edge comes from above the cluster
      let mut more : Array (Nat × Nat) := #[]
      for (c, lower, upper) in found do
        let below := lower.map fun b => (c, b)
        let above := upper.map fun a => (a, c)
        let fresh := fun (p : Option (Nat × Nat)) => p.filter fun q =>
          !apart.contains q && !more.contains q
        match fresh below, fresh above with
        | some p, _ => more := more.push p
        | none, some p => more := more.push p
        | none, none => pure ()
      if more.isEmpty then break
      apart := apart ++ more
      sk := skeleton g o tree pairs nb pad hasLabels apart
      found := strays tree sk
      -- the layout with the fewest such edges is kept
      if found.size < least then
        best := sk
        least := found.size
    return best
  let clustered := sk.clustered
  let pos := sk.pos
  -- a chain for every valid edge: none for a self-loop
  let chains : Array (Array Nat) := Id.run do
    let mut out : Array (Array Nat) := Array.mkEmpty m
    let mut next := 0
    for (_, e) in ve do
      if e.src == e.dst then out := out.push #[]
      else
        out := out.push (sk.chains.getD next #[])
        next := next + 1
    return out
  let layerAll := sk.layerAll
  let size := layerAll.size
  let order := sk.order
  let bs := sk.bs
  let reversed : Array Bool := ve.map fun (_, e) => e.src != e.dst && !before pos e.src e.dst
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
  -- the width of every layer counts in the total that the coordinates minimise
  let vars := if clustered then borderVariable bs else #[]
  let spans : Array (Nat × Nat × Int × Int) :=
    if o.compact == 0 then #[]
    else order.filterMap fun layer =>
      let a := layer.getD 0 0
      let b := layer.getD (layer.size - 1) 0
      let (a, b) := if vars.isEmpty then (a, b) else (vars.getD a a, vars.getD b b)
      if a != b then some (a, b, 0, Int.ofNat o.compact) else none
  let x := simplexBreadth total n chains order sep bw x1 8 o.coordinateWork vars (extra ++ spans)
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
  -- orthogonal route that moves sideways; a value below zero marks a step without a run
  let mut runs : Array (Array Float) := chains.map fun c => Array.replicate (c.size - 1) (-1)
  let mut tracks : Array Nat := Array.replicate order.size 0
  let mut gaps : Array (Array (Float × Float × Nat × Nat)) := Array.replicate order.size #[]
  -- how far the steps of the curves go sideways in each gap, at most
  let mut reach : Array Float := Array.replicate order.size 0
  for k in [0:m] do
    let c := chains.getD k #[]
    for j in [0:c.size - 1] do
      let a := (x.getD (c.getD j 0) 0).round
      let b := (x.getD (c.getD (j + 1) 0) 0).round
      let upper := layerAll.getD (c.getD j 0) 0
      if o.routing == .spline && upper + 1 == layerAll.getD (c.getD (j + 1) 0) 0 then
        reach := reach.modify upper (max · (a - b).abs)
      if o.routing == .orthogonal && (a - b).abs > 0.5 then
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
    -- a gap grows (up to `sidewaysGap` times): with many runs of orthogonal routes, to keep
    -- them three pixels apart; with a curve that goes far sideways, so that it is not too flat
    let g := if l == 0 then gap
      else min (o.sidewaysGap * gap) (max gap (max (reach.getD (l - 1) 0 / o.flattest)
        ((tracks.getD (l - 1) 0 + 1).toFloat * 3 + 16)))
    let g := if l == 0 then g
      else max g (bottomNeed.getD (l - 1) 0 + topNeed.getD l 0 + 20)
    t := if l == 0 then th / 2 + topNeed.getD 0 0 else t + prev / 2 + g + th / 2
    prev := th
    levels := levels.setIfInBounds l t.round
  let across := (Array.range size).map fun v =>
    if v < n then (x.getD v 0 - loopExtra.getD v 0 / 2).round else (x.getD v 0).round
  -- the room of every real and dummy node in its layer: `lanes` for the shortest routes (two
  -- neighbouring dummy nodes share the space between them half and half, so the routes of a
  -- bundle stay apart), `walls` for the curves (only boxes and cluster sides bound them)
  let clear : Float := 9
  let far : Float := 1e7
  let solid := fun (v : Nat) => v < n || v ≥ size
  let mut lanes : Array (Float × Float) := Array.replicate size (-far, far)
  let mut walls : Array (Float × Float) := Array.replicate size (-far, far)
  let mut sides : Array (Float × Float) := Array.replicate size (-far, far)
  -- whether the node is the side of a cluster that has nodes in the next layer too
  let reaches := fun (v l : Nat) => match bs.part.getD v .node with
    | .node => false
    | .left c | .right c => match bs.span.getD c none with
      | some (_, b) => l + 1 ≤ b
      | none => false
  for layer in order, l in [0:order.size] do
    let mut wall := -far
    let mut side := -far
    for j in [0:layer.size] do
      let v := layer.getD j 0
      let xv := (x.getD v 0).round
      let hv := bw.getD v 0 / 2
      if reaches v l then side := xv + 3
      if v < size then
        sides := sides.modify v fun (_, r) => (side, r)
        let soft := if j == 0 then -far else
          let u := layer.getD (j - 1) 0
          let edge := (x.getD u 0).round + bw.getD u 0 / 2
          let free := max 0 (xv - hv - edge)
          if solid u then edge + min clear (free / 2) else edge + free / 2
        lanes := lanes.modify v fun (_, r) => (soft, r)
        walls := walls.modify v fun (_, r) => (min wall (xv - hv), r)
      if solid v then wall := xv + hv + 3
    wall := far
    side := far
    for i in [0:layer.size] do
      let j := layer.size - 1 - i
      let v := layer.getD j 0
      let xv := (x.getD v 0).round
      let hv := bw.getD v 0 / 2
      if reaches v l then side := xv - 3
      if v < size then
        sides := sides.modify v fun (l, _) => (l, side)
        let soft := if j + 1 == layer.size then far else
          let u := layer.getD (j + 1) 0
          let edge := (x.getD u 0).round - bw.getD u 0 / 2
          let free := max 0 (edge - xv - hv)
          if solid u then edge - min clear (free / 2) else edge - free / 2
        lanes := lanes.modify v fun (l, _) => (l, soft)
        walls := walls.modify v fun (l, _) => (l, max wall (xv + hv))
      if solid v then wall := xv - hv - 3
  let rim := max 0.5 (min 6 (gap / 4))
  let gates := layerAll.map fun l =>
    (levels.getD l 0 - thick.getD l 0 / 2 - topNeed.getD l 0 - rim,
      levels.getD l 0 + thick.getD l 0 / 2 + bottomNeed.getD l 0 + rim)
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
          -- each end in its own stretch of the side, as near as it can be there to the point
          -- straight above or below the other end
          let (other, k) := ps.getD j (0, 0)
          let slot := (j.toFloat - (cnt.toFloat - 1) / 2) * step
          let room := max 0 (step / 2 - 1)
          let toward := other - across.getD v 0 - slot
          off := off.setIfInBounds k (slot + max (-room) (min room toward))
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
           clusterFrames, lanes, walls, sides, gates,
           arrowLength := o.arrowLength.getD Graph.arrowLength,
           arrowHalfWidth := o.arrowHalfWidth.getD Graph.arrowHalfWidth }

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
    let cut := pl.arrowLength - 1
    let inner := c.extract 1 (c.size - 1)
    -- the points of an orthogonal route: its two ends (short of an arrowhead) and the centres of
    -- its dummy nodes
    let first : Point := if arrow && rev then ⟨sx, sy + cut⟩ else ⟨sx, sy⟩
    let last : Point := if arrow && !rev then ⟨ex, ey - cut⟩ else ⟨ex, ey⟩
    let centres : Array Point := inner.map fun d => ⟨pl.across.getD d 0, pl.along.getD d 0⟩
    -- the gates of a curve: out of the upper node's layer, into and out of the layer of every
    -- dummy node (through the middle of a label's plate), into the lower node's layer
    let far : Float := 1e7
    let lane := fun (v : Nat) => pl.lanes.getD v (-far, far)
    let gate := fun (v : Nat) => pl.gates.getD v (pl.along.getD v 0, pl.along.getD v 0)
    let plated := if e.label.isEmpty || c.size < 3 then c.size else (c.size - 1) / 2
    let gates : Array Gate :=
      #[⟨(lane a).1, (lane a).2, max (sy + 0.5) (gate a).2⟩] ++
      (Array.range inner.size).flatMap (fun j =>
        let d := inner.getD j 0
        let (lo, hi) := if j + 1 == plated then (pl.across.getD d 0, pl.across.getD d 0) else lane d
        #[⟨lo, hi, (gate d).1⟩, ⟨lo, hi, (gate d).2⟩]) ++
      #[⟨(lane b).1, (lane b).2, min (ey - 0.5) (gate b).1⟩]
    -- the room of the curve: in the layer of every node of the chain between the boxes and
    -- cluster sides beside it, and on the way to the next layer between the sides of the
    -- clusters that reach there
    let zones : Array Zone := (Array.range c.size).flatMap fun j =>
      let v := c.getD j 0
      let (lo, hi) := pl.walls.getD v (-far, far)
      let (slo, shi) := pl.sides.getD v (-far, far)
      #[⟨lo, hi, (gate v).1, (gate v).2⟩] ++
        (if j + 1 < c.size then #[⟨slo, shi, (gate v).2, (gate (c.getD (j + 1) 0)).1⟩] else #[])
    let taut := tautRoute ⟨sx, sy⟩ gates ⟨ex, ey⟩
    -- the points of the route: the bends of the shortest route for a curve, the ends and the
    -- centres of the dummy nodes for an orthogonal route
    let pts : Array Point := match pl.routing with
      | .spline => taut
      | .orthogonal => #[⟨sx, sy⟩] ++ centres ++ #[⟨ex, ey⟩]
    let curve := fitPieces taut zones
    let (pieces, dir) : Array Piece × Point :=
      if !arrow then (curve, ⟨0, 1⟩)
      else if rev then shortenStart curve cut else shortenEnd curve cut
    let path : Path := match pl.routing with
      | .spline => piecesPath (if rev then reversePieces pieces else pieces)
      | .orthogonal =>
        let vs := orthVertices (#[first] ++ centres ++ #[last]) (pl.runs.getD k #[])
        roundedPolyline (if rev then vs.reverse else vs) 8
    let head : Option Path :=
      if !arrow then none
      else
        let tip : Point := if rev then ⟨sx, sy⟩ else ⟨ex, ey⟩
        let along : Point := if rev then ⟨0, -1⟩ else ⟨0, 1⟩
        some (arrowPath tip (if pl.routing == .spline then dir else along) pl.arrowLength
          pl.arrowHalfWidth)
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
