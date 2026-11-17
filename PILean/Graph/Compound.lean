/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Graph.Model
import PILean.Graph.Ordering

/-!
# Clusters in the layered layout

A cluster is a named group of nodes drawn inside a box; clusters nest through `Cluster.parent`.
The layout keeps every cluster's box around exactly its nodes, and the boxes of two clusters
apart unless one holds the other. It does so as Sander's layout of compound graphs does, with
the cluster's sides as nodes of the layered graph:

* **The cluster of a node** (`ClusterTree`): a real node belongs to the deepest cluster that
  lists it; a cluster holds its own nodes and those of the clusters inside it. A dummy node of
  an edge belongs to the innermost cluster that holds both ends of the edge (`ClusterTree.lca`),
  or, when the clusters have layers of their own (`PILean.Graph.Nested`), to the innermost
  cluster around one of the ends whose layers reach the dummy node's layer: the edge then leaves
  a cluster through its lower side and enters one through its upper side.
* **Border nodes** (`addBorders`): a cluster spans the layers from its highest to its lowest node
  (its nested clusters' nodes included); in every layer of the span it gets a left and a right
  border node, joined to the border nodes of the next layer by edges that only count in the
  crossing count (`sideWeight` times an edge). An edge that crosses a cluster's side passes
  through the cluster.
* **Contiguous order** (`arrange`): in every layer a cluster's nodes stand together between its
  border nodes, nested clusters inside their parent's block; inside a block the free nodes and
  the blocks of the nested clusters are sorted by their keys, and the blocks take the places so
  found in one order, the same in every layer (`ClusterTree.rank`). The crossing reduction
  (`reduceClustered`) runs the median sweeps and transposition of `PILean.Graph.Ordering` under
  these rules: a node is never moved out of its block, and two nodes are swapped only when they
  are in the same block.
* **Sides kept** (`clusterSweep`, `seatClusters`): in a sweep a free node stays on the side of
  every nested cluster that its middle neighbour in the layer before is on, and a cluster that
  begins in a layer takes its place between the siblings that its edges from the layer before
  come between; so an edge does not pass through a cluster wherever the order of the clusters
  allows.
* **Straight sides**: the coordinate phase gives all left border nodes of a cluster one
  coordinate, and all its right border nodes another (`borderVariable`). Since the border nodes
  stand in the same order in every layer, every node of a layer of the span lies inside the
  cluster's two sides exactly when it belongs to the cluster, and the sides of two clusters
  that share a layer are in one order: boxes nest or are apart.

Work: `O(Σ span)` border nodes (at most the clusters times the layers), and per layer
`O(k log k · d)` for `k` nodes and clusters nested `d` deep.

## References

* Sander, *Layout of compound directed graphs*, Technical Report A/03/96, Universität des
  Saarlandes (1996).
* Gansner, Koutsofios, North, Vo, *A technique for drawing directed graphs*, IEEE Transactions
  on Software Engineering 19 (1993), section 3 (clusters ranked and ordered together).
* Forster, *A fast and simple heuristic for constrained two-level crossing reduction*, Graph
  Drawing 2004, Lecture Notes in Computer Science 3383 (keys of groups as the mean of their
  members').

## Main definitions

* `ClusterTree`, `ClusterTree.of`, `ClusterTree.lca`, `ClusterTree.holds`.
* `Borders`, `addBorders`, `arrange`, `seatClusters`, `clusterSweep`, `reduceFromClustered`,
  `reduceClustered`.
-/

namespace PILean.Graph

/-- The clusters of a graph as a tree, with the cluster of every real node. -/
structure ClusterTree where
  /-- The parent of every cluster (`none` at the top). A parent is always a cluster listed
  earlier, so the parents form a forest. -/
  parent : Array (Option Nat)
  /-- The depth of every cluster (`0` at the top). -/
  depth : Array Nat
  /-- The deepest cluster that lists each real node (`none` for none). -/
  nodeCluster : Array (Option Nat)
  deriving Inhabited

namespace ClusterTree

/-- The tree of the graph's clusters. A parent that is not a cluster listed before the child is
ignored (the child is then at the top); a node listed by several clusters belongs to the deepest
of them, the first listed among equally deep ones; members that are not nodes are ignored. -/
def of (g : Graph) : ClusterTree := Id.run do
  let k := g.clusters.size
  let mut parent : Array (Option Nat) := Array.replicate k none
  let mut depth : Array Nat := Array.replicate k 0
  for i in [0:k] do
    match (g.clusters.getD i default).parent with
    | some p =>
      if p < i then
        parent := parent.setIfInBounds i (some p)
        depth := depth.setIfInBounds i (depth.getD p 0 + 1)
    | none => pure ()
  let n := g.nodes.size
  let mut nc : Array (Option Nat) := Array.replicate n none
  for i in [0:k] do
    for v in (g.clusters.getD i default).members do
      if v < n then
        match nc.getD v none with
        | none => nc := nc.setIfInBounds v (some i)
        | some j => if depth.getD i 0 > depth.getD j 0 then nc := nc.setIfInBounds v (some i)
  return { parent, depth, nodeCluster := nc }

/-- The clusters from the top down to `c` (empty for `none`). -/
def path (t : ClusterTree) (c : Option Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut cur := c
  for _ in [0:t.parent.size + 1] do
    match cur with
    | none => break
    | some x =>
      out := out.push x
      cur := t.parent.getD x none
  return out.reverse

/-- Whether cluster `a` is `c` or holds `c` (through parents). -/
def holds (t : ClusterTree) (a c : Nat) : Bool := (t.path (some c)).contains a

/-- Whether the cluster `a` holds a node of cluster `c` (`none`: in no cluster). -/
def holdsOpt (t : ClusterTree) (a : Nat) (c : Option Nat) : Bool :=
  match c with
  | none => false
  | some x => t.holds a x

/-- The innermost cluster holding both `a` and `b` (`none` when only the whole graph does). -/
def lca (t : ClusterTree) (a b : Option Nat) : Option Nat := Id.run do
  let pa := t.path a
  let pb := t.path b
  let mut out : Option Nat := none
  for i in [0:min pa.size pb.size] do
    if pa.getD i 0 == pb.getD i 0 then out := some (pa.getD i 0) else break
  return out

end ClusterTree

/-- What a node of the layered graph is, for the cluster rules. -/
inductive Part where
  /-- A real or a dummy node. -/
  | node
  /-- The left side of a cluster in one layer. -/
  | left (c : Nat)
  /-- The right side of a cluster in one layer. -/
  | right (c : Nat)
  deriving BEq, Inhabited, Repr

/-- The layered graph with the clusters' border nodes added (see the module docstring). -/
structure Borders where
  /-- The layer of every node, border nodes after the others. -/
  layerAll : Array Nat
  /-- The neighbours above every node, with the border edges. -/
  up : Array (Array Nat)
  /-- The neighbours below every node, with the border edges. -/
  down : Array (Array Nat)
  /-- The block of every node: the innermost cluster it stands in (for a border node, its
  cluster). -/
  block : Array (Option Nat)
  /-- What every node is. -/
  part : Array Part
  /-- The first and last layer of every cluster, `none` for a cluster without nodes. -/
  span : Array (Option (Nat × Nat))
  /-- The left and the right border node of every cluster in the first layer of its span. -/
  firstBorders : Array (Option (Nat × Nat))
  deriving Inhabited

/-- Adds the border nodes of the clusters to the layered graph of `size` nodes (layers
`layerAll`, neighbours `up` and `down`, the block of every node `block`). The new nodes are
numbered from `size`, cluster by cluster, layer by layer, left then right. -/
def addBorders (t : ClusterTree) (layerAll : Array Nat) (up down : Array (Array Nat))
    (block : Array (Option Nat)) : Borders := Id.run do
  let k := t.parent.size
  let size := layerAll.size
  let mut span : Array (Option (Nat × Nat)) := Array.replicate k none
  for v in [0:size] do
    let l := layerAll.getD v 0
    for c in t.path (block.getD v none) do
      span := span.modify c fun
        | none => some (l, l)
        | some (a, b) => some (min a l, max b l)
  let mut layerAll := layerAll
  let mut up := up
  let mut down := down
  let mut blk := block
  let mut part : Array Part := Array.replicate size .node
  let mut first : Array (Option (Nat × Nat)) := Array.replicate k none
  for c in [0:k] do
    if let some (a, b) := span.getD c none then
      for l in [a:b + 1] do
        let lv := layerAll.size
        let rv := lv + 1
        layerAll := (layerAll.push l).push l
        blk := (blk.push (some c)).push (some c)
        part := (part.push (.left c)).push (.right c)
        up := (up.push #[]).push #[]
        down := (down.push #[]).push #[]
        if l == a then first := first.setIfInBounds c (some (lv, rv))
        else
          -- joined to the border nodes of the layer above (made just before)
          up := (up.modify lv (·.push (lv - 2))).modify rv (·.push (rv - 2))
          down := (down.modify (lv - 2) (·.push lv)).modify (rv - 2) (·.push rv)
  return { layerAll, up, down, block := blk, part, span, firstBorders := first }

/-- The rule of order inside one block: `items` are the nodes of one layer that stand in the
block of the cluster at depth `level - 1` of their path (all of them at `level = 0`); the
result has them with the left border first, the right border last, and the free nodes and the
blocks of the nested clusters sorted by `key` (a block's key is the mean of its nodes' keys),
the blocks then put into the places they took in the order of `rank`. `fuel` bounds the
nesting followed.

A free node stands after some of the nested clusters (taken in the order of `rank`) and before
the others. `held c v` says whether the nested cluster `c` must come before the free node `v`
(`none`: it need not): the node is put where every such demand is met, when they can be met
together. Among the places left, the keys decide (a cluster comes before the node when its key
is smaller). So an edge to another layer does not pass through a cluster that has nodes in both
layers when `held` keeps a node on the side of that cluster its neighbour is on. -/
def arrangeBlock (t : ClusterTree) (bs : Borders) (key : Nat → Float) (rank : Nat → Float)
    (held : Nat → Nat → Option Bool) : Nat → Nat → Array Nat → Array Nat
  | 0, _, items => items
  | fuel + 1, level, items => Id.run do
    let mut lefts : Array Nat := #[]
    let mut rights : Array Nat := #[]
    -- free nodes as (key, node); nested blocks as their cluster with their nodes
    let mut free : Array (Float × Nat) := #[]
    let mut kids : Array Nat := #[]
    let mut kidNodes : Array (Array Nat) := #[]
    for v in items do
      let p := t.path (bs.block.getD v none)
      let own := match bs.part.getD v .node with
        | .left _ => if p.size == level then 1 else 0
        | .right _ => if p.size == level then 2 else 0
        | .node => if p.size ≤ level then 3 else 0
      if own == 1 then lefts := lefts.push v
      else if own == 2 then rights := rights.push v
      else if own == 3 then free := free.push (key v, v)
      else
        let c := p.getD level 0
        match kids.idxOf? c with
        | some i => kidNodes := kidNodes.modify i (·.push v)
        | none => kids := kids.push c; kidNodes := kidNodes.push #[v]
    let kidKey : Array Float := (Array.range kids.size).map fun i =>
      let ns := kidNodes.getD i #[]
      let real := ns.filter fun v => bs.part.getD v .node == .node
      let base := if real.isEmpty then ns else real
      base.foldl (fun s v => s + key v) 0 / (max 1 base.size).toFloat
    let byRank := ((Array.range kids.size).sortStable fun i j =>
      let ri := rank (kids.getD i 0)
      let rj := rank (kids.getD j 0)
      ri < rj || (ri == rj && kids.getD i 0 < kids.getD j 0))
    -- (key, 0 for a free node or 1 for a block, its node or block number) by the number of
    -- nested blocks that come before
    let mut slots : Array (Array (Float × Nat × Nat)) := Array.replicate (kids.size + 1) #[]
    for (kv, v) in free do
      let hard := byRank.map fun i => held (kids.getD i 0) v
      let soft : Array Bool := byRank.map fun i => kidKey.getD i 0 < kv
      -- the places that meet every demand: after `lo` blocks at least, `hi` at most
      let mut lo := 0
      let mut hi := kids.size
      for r in [0:kids.size] do
        match hard.getD r none with
        | some true => lo := max lo (r + 1)
        | some false => hi := min hi r
        | none => pure ()
      let count := fun (a b : Nat) => (Array.range (b - a)).foldl (init := 0) fun n d =>
        if (hard.getD (a + d) none).getD (soft.getD (a + d) false) then n + 1 else n
      let j := if lo ≤ hi then lo + count lo hi else count 0 kids.size
      slots := slots.modify j (·.push (kv, 0, v))
    let mut out := lefts
    for j in [0:kids.size + 1] do
      -- the free nodes between two blocks that keep their places; a block that is not a
      -- separator may change places with the free nodes beside it by its key
      let here := (slots.getD j #[]).sortStable fun a b =>
        a.1 < b.1 || (a.1 == b.1 && a.2.2 < b.2.2)
      for (_, _, x) in here do out := out.push x
      if j < kids.size then
        out := out ++ arrangeBlock t bs key rank held fuel (level + 1)
          (kidNodes.getD (byRank.getD j 0) #[])
    return out ++ rights

/-- One layer in the cluster rules' order (`arrangeBlock` from the top). -/
def arrange (t : ClusterTree) (bs : Borders) (key : Nat → Float) (rank : Nat → Float)
    (layer : Array Nat) (held : Nat → Nat → Option Bool := fun _ _ => none) : Array Nat :=
  arrangeBlock t bs key rank held (t.parent.size + 1) 0 layer

/-- The place of every cluster in the order of its siblings: the mean, over the layers, of the
relative positions (position plus a half, over the layer's size) of its real and dummy nodes,
nested clusters' included. -/
def clusterRank (t : ClusterTree) (bs : Borders) (order : Array (Array Nat)) : Array Float :=
  Id.run do
  let k := t.parent.size
  let mut sum : Array Float := Array.replicate k 0
  let mut cnt : Array Nat := Array.replicate k 0
  for layer in order do
    for i in [0:layer.size] do
      let v := layer.getD i 0
      if bs.part.getD v .node == .node then
        let r := (i.toFloat + 0.5) / layer.size.toFloat
        for c in t.path (bs.block.getD v none) do
          sum := sum.modify c (· + r)
          cnt := cnt.modify c (· + 1)
  return (Array.range k).map fun c =>
    if cnt.getD c 0 == 0 then 0.5 else sum.getD c 0 / (cnt.getD c 0).toFloat

/-- The right border node of cluster `c` in the layer `l` of its span. -/
def rightBorder (bs : Borders) (c l : Nat) : Option Nat :=
  match bs.span.getD c none, bs.firstBorders.getD c none with
  | some (a, b), some (_, rv) => if a ≤ l && l ≤ b then some (rv + 2 * (l - a)) else none
  | _, _ => none

/-- The places of the clusters that begin in a layer, among their siblings. `layer` is layer
`i`, about to be ordered by the positions `pos` of the layer `from_` beside it (through the
neighbours `nbr` there). A cluster with nodes in `layer` and none in layer `from_` gets a rank
that puts it between the same two of its siblings that have nodes in both layers (the
*separators*) as the middle one of the neighbours of its nodes there, so that the edges from
that layer need not pass through a separator. `inside` lists the clusters directly inside each
cluster (the top ones last). Other ranks are unchanged. -/
def seatClusters (t : ClusterTree) (bs : Borders) (inside : Array (Array Nat))
    (rank : Array Float) (layer : Array Nat) (nbr : Array (Array Nat)) (pos : Array Nat)
    (i from_ : Nat) : Array Float := Id.run do
  let clusters := t.parent.size
  let present := fun (c l : Nat) => match bs.span.getD c none with
    | some (a, b) => a ≤ l && l ≤ b
    | none => false
  -- the positions of the neighbours, outside the cluster, of the nodes of each beginning cluster
  let mut seen : Array (Array Nat) := Array.replicate clusters #[]
  let mut found : Array Nat := #[]
  for v in layer do
    if bs.part.getD v .node != .node then continue
    let path := t.path (bs.block.getD v none)
    for c in path do
      if present c from_ then continue
      for u in nbr.getD v #[] do
        if !(t.path (bs.block.getD u none)).contains c then
          if (seen.getD c #[]).isEmpty then found := found.push c
          seen := seen.modify c (·.push (pos.getD u 0))
  let mut out := rank
  for c in found do
    let seps := ((inside.getD ((t.parent.getD c none).getD clusters) #[]).filter fun s =>
      s != c && present s i && present s from_).sortStable fun a b =>
        out.getD a 0 < out.getD b 0 || (out.getD a 0 == out.getD b 0 && a < b)
    if seps.isEmpty then continue
    let ps := (seen.getD c #[]).sortStable (· < ·)
    let at_ := ps.getD ((ps.size - 1) / 2) 0
    let j := seps.foldl (init := 0) fun n s =>
      match rightBorder bs s from_ with
      | some rv => if pos.getD rv 0 < at_ then n + 1 else n
      | none => n
    let r := fun (j : Nat) => out.getD (seps.getD j 0) 0
    let seat := if j == 0 then r 0 - 1 else if j == seps.size then r (j - 1) + 1
      else (r (j - 1) + r j) / 2
    out := out.setIfInBounds c seat
  return out

/-- How many crossings of edges the crossing of an edge with a cluster's side counts as, when
orders are compared. -/
def sideWeight : Nat := 8

/-- One sweep of the crossing reduction under the cluster rules: every layer but the first one
met (from the top down when `downward`, else from the bottom up) is put in the order of the
weighted medians of its nodes' neighbours in the layer before (a node without neighbours there
keeps its position as its key), by `arrange`. A free node keeps the side of every nested cluster
that its middle neighbour in the layer before has there, and a cluster that begins in a layer is
first given its place among its siblings (`seatClusters`). `inside` lists the clusters directly
inside each cluster (the top ones last). Returns the order, the positions and the ranks. -/
def clusterSweep (t : ClusterTree) (bs : Borders) (inside : Array (Array Nat))
    (order : Array (Array Nat)) (pos : Array Nat) (rank : Array Float) (downward : Bool) :
    Array (Array Nat) × Array Nat × Array Float := Id.run do
  let count := order.size
  let mut order := order
  let mut pos := pos
  let mut rank := rank
  for k in [0:count] do
    let i := if downward then k else count - 1 - k
    let nbr := if downward then bs.up else bs.down
    let edge := if downward then i == 0 else i + 1 == count
    if !edge then
      let p := pos
      let from_ := if downward then i - 1 else i + 1
      rank := seatClusters t bs inside rank (order.getD i #[]) nbr p i from_
      let ranks := rank
      let key := fun (v : Nat) =>
        let ns := nbr.getD v #[]
        if ns.isEmpty then (p.getD v 0).toFloat
        else weightedMedian ((ns.map fun u => p.getD u 0).sortStable (· < ·))
      let present := fun (c : Nat) => match bs.span.getD c none with
        | some (a, b) => a ≤ from_ && from_ ≤ b
        | none => false
      let held := fun (c v : Nat) =>
        match bs.span.getD c none, bs.firstBorders.getD c none with
        | some (a, _), some (_, rv) =>
          let ns := (nbr.getD v #[]).map fun u => p.getD u 0
          if !present c || ns.isEmpty then none
          else
            some (p.getD (rv + 2 * (from_ - a)) 0 <
              (ns.sortStable (· < ·)).getD ((ns.size - 1) / 2) 0)
        | _, _ => none
      let r := arrange t bs key (ranks.getD · 0.5) (order.getD i #[]) held
      order := order.setIfInBounds i r
      for j in [0:r.size] do pos := pos.setIfInBounds (r.getD j 0) j
  return (order, pos, rank)

/-- The order of the nodes inside the layers under the cluster rules and its crossings (border
edges included, each counting `sideWeight` times), from an order `start` of the real and dummy
nodes (the border nodes are placed by the rules): the start arranged, then at most `sweeps`
rounds of `clusterSweep` (down on even rounds, up on odd ones, seating the clusters that
begin), each followed by transposition of adjacent nodes of one block, the order with the
fewest crossings kept (the start only when no edge crosses a cluster's side in it: a sweep puts
every free node on its side of the clusters); the search stops after `4` rounds without
improvement. -/
def reduceFromClustered (t : ClusterTree) (bs : Borders) (start : Array (Array Nat))
    (sweeps : Nat) : Array (Array Nat) × Nat := Id.run do
  let size := bs.layerAll.size
  -- the border nodes go into their layers, then everything is arranged by the start positions
  let mut layers := start
  for v in [0:size] do
    if bs.part.getD v .node != .node then
      layers := layers.modify (bs.layerAll.getD v 0) (·.push v)
  let pos0 := positionsOf size layers
  let rank0 := clusterRank t bs layers
  let mut order := layers.map (arrange t bs (fun v => (pos0.getD v 0).toFloat) (rank0.getD · 0.5))
  let mut pos := positionsOf size order
  -- crossings are counted with the sides of the clusters weighing more than edges
  let heavy : Array (Array Nat) := (Array.range size).map fun v =>
    let ns := bs.down.getD v #[]
    if bs.part.getD v .node == .node then ns
    else (Array.range (ns.size * sideWeight)).map fun j => ns.getD (j / sideWeight) 0
  let canSwap := fun (u v : Nat) =>
    bs.part.getD u .node == .node && bs.part.getD v .node == .node &&
      bs.block.getD u none == bs.block.getD v none
  -- the clusters directly inside every cluster, and those at the top (the last entry)
  let clusters := t.parent.size
  let mut inside : Array (Array Nat) := Array.replicate (clusters + 1) #[]
  for c in [0:clusters] do inside := inside.modify ((t.parent.getD c none).getD clusters) (·.push c)
  let mut rank := rank0
  let mut best := order
  let mut bestC := totalCrossings order heavy pos
  let startClean := bestC == totalCrossings order bs.down pos
  let mut stall := 0
  for s in [0:sweeps] do
    if s > 0 && (bestC == 0 || stall ≥ 4) then break
    let (o, p, r) := clusterSweep t bs inside order pos rank (s % 2 == 0)
    order := o
    pos := p
    rank := r
    for t in [0:8] do
      let (o, p, changed) :=
        transposePass order pos bs.up bs.down canSwap (ties := s % 2 == 1 && t == 0)
      order := o
      pos := p
      if !changed then break
    let c := totalCrossings order heavy pos
    -- a start in which an edge crosses a cluster's side is not kept: only a sweep puts every
    -- node on its side of the clusters
    if c < bestC || (s == 0 && !startClean) then
      best := order
      bestC := c
      stall := 0
    else stall := stall + 1
  return (best, bestC)

/-- The order of the nodes inside the layers under the cluster rules: `reduceFromClustered` from
the unconstrained order `start` and, up to 6000 nodes, from the depth-first and breadth-first
orders of `PILean.Graph.Ordering` and from up to `starts` depth-first orders drawn from a fixed
sequence (`initialLayersSeeded`; as many as `extraStarts` allows for the graph's size); the one
with the fewest crossings (border edges included; the first on a tie). `up` and `down` are the
neighbours of the real and dummy nodes. -/
def reduceClustered (t : ClusterTree) (bs : Borders) (start : Array (Array Nat))
    (up down : Array (Array Nat)) (sweeps : Nat) (starts : Nat := 16) : Array (Array Nat) :=
  Id.run do
  let layerAll := bs.layerAll.extract 0 up.size
  let mut best := reduceFromClustered t bs start sweeps
  if up.size ≤ 6000 && best.2 != 0 then
    -- the other starts are searched at the same time, and the first of the best results is
    -- kept, as if they had been searched one after the other
    let pairs := best.1.foldl (fun s l => s + l.size * l.size) 0
    let others : Array (Task (Array (Array Nat) × Nat)) :=
      #[Task.spawn fun _ => reduceFromClustered t bs (initialLayers layerAll up down) sweeps,
        Task.spawn fun _ => reduceFromClustered t bs (initialLayersBfs layerAll up down) sweeps] ++
      (Array.range (extraStarts pairs starts)).map fun k => Task.spawn fun _ =>
        reduceFromClustered t bs (initialLayersSeeded layerAll up down k) sweeps
    for task in others do
      let r := task.get
      if r.2 < best.2 then best := r
  return best.1

/-- The least distance between the centres of `u` left of `v` with border nodes: `base` between
two real or dummy nodes; `inside` from a left border to what follows it, and `pad` from what
precedes a right border to it (half the width of the node besides); `outside` between a border
and a node of another block; `apart` from the right border of a cluster to the left border of
the next. -/
def borderSeparation (bs : Borders) (base : Nat → Nat → Float) (bw : Array Float)
    (pad inside outside apart : Float) (u v : Nat) : Float :=
  let hu := bw.getD u 0 / 2
  let hv := bw.getD v 0 / 2
  match bs.part.getD u .node, bs.part.getD v .node with
  | .node, .node => base u v
  | .left _, .right _ => inside + pad
  | .left _, _ => inside + hv
  | _, .right _ => hu + pad
  | .right _, .left _ => apart
  | .right _, _ => outside + hv
  | _, .left _ => hu + outside

/-- The variable of every node in the coordinate phase: a cluster's left border nodes all take
the variable of its first left border node, its right ones that of its first right one, every
other node its own. -/
def borderVariable (bs : Borders) : Array Nat :=
  (Array.range bs.layerAll.size).map fun v =>
    match bs.part.getD v .node with
    | .node => v
    | .left c => ((bs.firstBorders.getD c none).map (·.1)).getD v
    | .right c => ((bs.firstBorders.getD c none).map (·.2)).getD v

end PILean.Graph
