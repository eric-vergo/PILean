/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Std.Data.HashMap
import PILean.Graph.Layering
import PILean.Graph.Compound

/-!
# Layers of a graph with clusters

A graph with clusters is layered from the inside out, each cluster on its own (Gansner,
Koutsofios, North and Vo rank the clusters of a graph recursively; Sander's compound graphs are
layered the same way). At one *level* (the whole graph, or the inside of one cluster) the items
are the nodes that stand there directly and the clusters directly inside, each cluster already
layered and so many layers high. An edge between two different items of a level joins them, and
its target item starts below the whole of its source item:

1. **Cycles** between the items of a level are removed as between nodes (`elsPositions` on the
   items).
2. **Layers** (`levelLayers`): the first layer of every item, with every edge's target item
   starting at least the height of its source item further down, of least total weighted span,
   by network simplex (`simplexSolve` with the heights as the edges' least lengths).
3. **Wide layers** (`wrapLayers`): when the items that start in one layer are together wider
   than a limit, they are split over rows put in between, the items with more edges from above
   first. Edges keep pointing down.

The layer of a node is the sum of the first layers of the clusters around it and its own inside
the innermost (`nestedLayers`). So every cluster keeps a block of layers to itself and to the
clusters inside it; two clusters of a level that an edge joins lie one wholly above the other,
and an edge between them leaves the one through its lower side and enters the other through its
upper side.

`assignNested` relaxes the result once more with `fixLayers`, as `assignLayers` does, so that
every edge points to a deeper layer by proof (`PILean.Graph.assignNested_lt`); the relaxation is
expected to change nothing, which the tests check.

Work: one network simplex per level on its items and the edges between them, within the work
given; `O(V + E)` besides, up to sorting.

## References

* Gansner, Koutsofios, North, Vo, *A technique for drawing directed graphs*, IEEE Transactions
  on Software Engineering 19 (1993).
* Sander, *Layout of compound directed graphs*, Technical Report A/03/96, Universität des
  Saarlandes (1996).

## Main definitions

* `levelLayers`, `wrapLayers`, `nestedLayers`, `assignNested`, `assignWide`.
-/

namespace PILean.Graph

/-- Splits the layers that are too wide. Item `i` starts at layer `top i`, is `height i` layers
high and `width i` wide; `lean i` orders the items that start in one layer (smaller first). The
items that start in a layer fill a row from the left until the next would pass `limit`, then a
new row below, and every later layer moves down by the rows added. An item that covers several
layers counts in each. Returns the new first layers. With `limit ≤ 0` nothing is split. Every
pair of items with `top a + height a ≤ top b` keeps that relation. -/
def wrapLayers (top height : Array Nat) (width : Array Float) (lean : Array Int)
    (limit : Float) : Array Nat := Id.run do
  let m := top.size
  if limit ≤ 0 || m == 0 then return top
  let layers := top.foldl max 0 + 1
  let mut starters : Array (Array Nat) := Array.replicate layers #[]
  for i in [0:m] do starters := starters.modify (top.getD i 0) (·.push i)
  let mut out := top
  -- the width used in every new row
  let mut used : Array Float := #[]
  let mut shift := 0
  for t in [0:layers] do
    let items := (starters.getD t #[]).sortStable fun a b =>
      lean.getD a 0 < lean.getD b 0 || (lean.getD a 0 == lean.getD b 0 && a < b)
    let mut row := t + shift
    let mut placed := 0
    for i in items do
      let w := width.getD i 0
      if placed > 0 && used.getD row 0 + w > limit then
        row := row + 1
        shift := shift + 1
        placed := 0
      out := out.setIfInBounds i row
      placed := placed + 1
      for r in [row:row + max 1 (height.getD i 1)] do
        if used.size ≤ r then used := used ++ Array.replicate (r + 1 - used.size) 0
        used := used.modify r (· + w)
  return out

/-- The first layer of each of `m` items for the edges `edges` between them (pairs of item
numbers; loops and pairs out of range are ignored), item `i` being `height i` layers high and
`width i` wide: cycles removed (`elsPositions`), then the layers of least total span in which
every edge's target starts at least the height of its source below the source's first layer
(`simplexSolve` within the work `work`, from the longest paths), then the layers wider than
`limit` split (`wrapLayers`; none for `limit ≤ 0`). Returns the first layers and the number of
layers used. -/
def levelLayers (m : Nat) (height : Array Nat) (width : Array Float) (edges : Array (Nat × Nat))
    (limit : Float) (work : Nat) : Array Nat × Nat := Id.run do
  if m == 0 then return (#[], 0)
  let h := fun (i : Nat) => max 1 (height.getD i 1)
  let pos := elsPositions m edges
  -- the oriented edges with their multiplicities
  let mut weightOf : Std.HashMap Nat Int := {}
  let mut keys : Array Nat := #[]
  for (a, b) in edges do
    if a < m && b < m && a != b then
      let (a, b) := orient pos (a, b)
      let key := a * m + b
      match weightOf.get? key with
      | some w => weightOf := weightOf.insert key (w + 1)
      | none =>
        weightOf := weightOf.insert key 1
        keys := keys.push key
  let tails := keys.map (· / m)
  let heads := keys.map (· % m)
  let minlen : Array Int := tails.map fun a => (h a : Int)
  let weight : Array Int := keys.map fun k => weightOf.getD k 1
  -- the longest paths, in the order of the items
  let mut outs : Array (Array Nat) := Array.replicate m #[]
  for k in [0:keys.size] do outs := outs.modify (tails.getD k 0) (·.push (heads.getD k 0))
  let order := (Array.range m).sortStable fun a b => before pos a b
  let mut start : Array Nat := Array.replicate m 0
  for a in order do
    let below := start.getD a 0 + h a
    for b in outs.getD a #[] do start := start.modify b (max · below)
  let (sol, _) := simplexSolve m tails heads minlen weight (start.map (Int.ofNat ·)) 8 work
  let tops := sol.map (·.toNat)
  let feasible := tops.size == m && (Array.range keys.size).all fun k =>
    tops.getD (tails.getD k 0) 0 + h (tails.getD k 0) ≤ tops.getD (heads.getD k 0) 0
  let tops := if feasible then tops else start
  -- an item with more edges from above than to below goes into an upper row of its layer
  let mut lean : Array Int := Array.replicate m 0
  for k in [0:keys.size] do
    let w := weight.getD k 1
    lean := (lean.modify (tails.getD k 0) (· + w)).modify (heads.getD k 0) (· - w)
  let wrapped := wrapLayers tops ((Array.range m).map h) width lean limit
  let total := (Array.range m).foldl (fun t i => max t (wrapped.getD i 0 + h i)) 0
  return (wrapped, total)

/-- The layer of each of the `n` nodes of a graph with the cluster tree `t` and the edges
`edges` (pairs of node numbers), layered from the inside out (see the module docstring). `width`
is the room every node takes across its layer (its box and the gap beside it), `pad` what a
cluster's sides add to its contents, `limit` the width from which a layer is split into rows
(none for `limit ≤ 0`), `work` the work allowed to the network simplex of each level. `apart`
lists pairs of items of one level to be laid out one above the other, as if an edge joined
them: a node by its number, a cluster by its number plus `n`; a pair of items of different
levels is ignored. -/
def nestedLayers (n : Nat) (t : ClusterTree) (edges : Array (Nat × Nat)) (width : Array Float)
    (pad limit : Float) (work : Nat) (apart : Array (Nat × Nat) := #[]) : Array Nat := Id.run do
  let k := t.parent.size
  -- the level of cluster `c` is `c`, the whole graph's is `k`
  let levelOf := fun (c : Option Nat) => c.getD k
  -- the items of every level: its own nodes, then the clusters directly inside
  let mut ownNodes : Array (Array Nat) := Array.replicate (k + 1) #[]
  let mut local_ : Array Nat := Array.replicate n 0
  for v in [0:n] do
    let l := levelOf (t.nodeCluster.getD v none)
    local_ := local_.setIfInBounds v (ownNodes.getD l #[]).size
    ownNodes := ownNodes.modify l (·.push v)
  let mut kids : Array (Array Nat) := Array.replicate (k + 1) #[]
  let mut clusterLocal : Array Nat := Array.replicate k 0
  for c in [0:k] do
    let l := levelOf (t.parent.getD c none)
    clusterLocal := clusterLocal.setIfInBounds c
      ((ownNodes.getD l #[]).size + (kids.getD l #[]).size)
    kids := kids.modify l (·.push c)
  -- the edges of every level, between its items
  let paths : Array (Array Nat) := (Array.range k).map fun c => t.path (some c)
  let pathOf := fun (v : Nat) => match t.nodeCluster.getD v none with
    | some c => paths.getD c #[]
    | none => #[]
  let mut levelEdges : Array (Array (Nat × Nat)) := Array.replicate (k + 1) #[]
  for (u, w) in edges do
    if u < n && w < n && u != w then
      let pu := pathOf u
      let pw := pathOf w
      let mut d := 0
      for i in [0:min pu.size pw.size] do
        if pu.getD i 0 == pw.getD i 0 then d := i + 1 else break
      let l := if d == 0 then k else pu.getD (d - 1) 0
      let a := if pu.size > d then clusterLocal.getD (pu.getD d 0) 0 else local_.getD u 0
      let b := if pw.size > d then clusterLocal.getD (pw.getD d 0) 0 else local_.getD w 0
      levelEdges := levelEdges.modify l (·.push (a, b))
  -- the pairs to keep one above the other: edges between two items of one level
  for (a, b) in apart do
    let levelOfItem := fun (x : Nat) =>
      if x < n then levelOf (t.nodeCluster.getD x none) else levelOf (t.parent.getD (x - n) none)
    let localOf := fun (x : Nat) => if x < n then local_.getD x 0 else clusterLocal.getD (x - n) 0
    if a < n + k && b < n + k && a != b && levelOfItem a == levelOfItem b then
      levelEdges := levelEdges.modify (levelOfItem a) (·.push (localOf a, localOf b))
  -- from the innermost clusters out (a cluster is listed after its parent)
  let mut height : Array Nat := Array.replicate (k + 1) 1
  let mut breadth : Array Float := Array.replicate (k + 1) 0
  let mut nodeTop : Array Nat := Array.replicate n 0
  let mut clusterTop : Array Nat := Array.replicate k 0
  for i in [0:k + 1] do
    let l := if i == k then k else k - 1 - i
    let nodes := ownNodes.getD l #[]
    let inside := kids.getD l #[]
    let m := nodes.size + inside.size
    if m == 0 then continue
    let hs := nodes.map (fun _ => 1) ++ inside.map (height.getD · 1)
    let ws := nodes.map (width.getD · 0) ++ inside.map (breadth.getD · 0)
    let (tops, total) := levelLayers m hs ws (levelEdges.getD l #[]) limit work
    for j in [0:nodes.size] do nodeTop := nodeTop.setIfInBounds (nodes.getD j 0) (tops.getD j 0)
    for j in [0:inside.size] do
      clusterTop := clusterTop.setIfInBounds (inside.getD j 0) (tops.getD (nodes.size + j) 0)
    -- the widest row of the level
    let mut rows : Array Float := Array.replicate (max 1 total) 0
    for j in [0:m] do
      for r in [tops.getD j 0:tops.getD j 0 + max 1 (hs.getD j 1)] do
        rows := rows.modify r (· + ws.getD j 0)
    height := height.setIfInBounds l (max 1 total)
    breadth := breadth.setIfInBounds l (rows.foldl max 0 + 2 * pad)
  -- the first layer of every cluster in the whole graph (parents first)
  let mut base : Array Nat := Array.replicate k 0
  for c in [0:k] do
    let up := match t.parent.getD c none with
      | some p => base.getD p 0
      | none => 0
    base := base.setIfInBounds c (up + clusterTop.getD c 0)
  return (Array.range n).map fun v =>
    nodeTop.getD v 0 + match t.nodeCluster.getD v none with
      | some c => base.getD c 0
      | none => 0

/-- The layers of a graph with clusters, and the order of its nodes that the layers give (a
node comes before another when its layer is smaller, `before`): `nestedLayers` (all zero should
its result have the wrong size, which never happens), relaxed once more with `fixLayers` along
that order, so that every edge between two different nodes points from the one that comes first
to a deeper layer (`PILean.Graph.assignNested_lt`). The relaxation is expected to change
nothing. -/
def assignNested (n : Nat) (t : ClusterTree) (edges : List (Nat × Nat)) (width : Array Float)
    (pad limit : Float) (work : Nat := 100000000) (apart : Array (Nat × Nat) := #[]) :
    Array Nat × Array Nat :=
  let raw := nestedLayers n t edges.toArray width pad limit work apart
  let pos := if raw.size = n then raw else Array.replicate n 0
  (pos, fixLayers (acyclicEdges pos edges) pos)

/-- The layers of a graph without clusters whose layers are to be no wider than `limit`:
`assignLayers`, the layers wider than `limit` split into rows (`wrapLayers`, with `width` the
room of every node across its layer; the result is dropped should its size be wrong, which
never happens), relaxed once more with `fixLayers` (`PILean.Graph.assignWide_lt`). With
`limit ≤ 0` these are the layers of `assignLayers`. -/
def assignWide (pos : Array Nat) (n : Nat) (edges : List (Nat × Nat)) (width : Array Float)
    (limit : Float) (work : Nat := 100000000) : Array Nat :=
  let lay := assignLayers pos n edges work
  let es := acyclicEdges pos edges
  let lean : Array Int := es.foldl (init := Array.replicate n 0) fun l (a, b) =>
    (l.modify a (· + 1)).modify b (· - 1)
  let wide := wrapLayers lay (Array.replicate n 1) width lean limit
  fixLayers es (if wide.size = n then wide else lay)

end PILean.Graph
