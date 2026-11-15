/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Std.Data.HashSet
import PILean.Graph.Ordering

/-!
# Horizontal coordinate assignment

Positions across the layers by the method of Brandes and Köpf, which keeps the chains of dummy
nodes of long edges straight:

1. **Type 1 conflicts** (`markConflicts`): a segment between two dummy nodes (an *inner*
   segment) always wins against a crossing segment of which one end is a real node; the losing
   segments are marked and never used for alignment.
2. **Vertical alignment** (inside `alignCompact`): each node is aligned with one of its two median
   neighbours in the previous layer, when that does not cross an earlier alignment or a marked
   segment; aligned nodes form *blocks* that share one coordinate.
3. **Horizontal compaction** (inside `alignCompact`): the blocks are placed as far left as
   the separations of neighbours in a layer allow (the longest path through the block graph, found
   with a topological sweep). The class shifts of the original paper are left out: blocks are
   never moved relative to each other after this, so they cannot overlap.
4. **Balancing** (`assignBreadth`): the four alignments (upper or lower neighbours, left or right)
   are made by mirroring the layers and their order, brought to the narrowest one's extent, and
   each node takes the mean of its two median values; the separation of the neighbours
   holds for each alignment, hence for the mean of two order statistics.

Work: `O(V + E)` per alignment up to the sorting of each node's neighbours.

## References

* Brandes, Köpf, *Fast and simple horizontal coordinate assignment*, Graph Drawing 2001,
  Lecture Notes in Computer Science 2265.
-/

namespace PILean.Graph

/-- The key of the segment between two nodes in the set of marked segments. -/
def segmentKey (size a b : Nat) : Nat := min a b * size + max a b

/-- The marked (type 1 conflict) segments: for each pair of adjacent layers, the non-inner
segments that cross an inner segment. `order` is the node order of the layers, `pos` the
positions in it, `up` the neighbours above, and the nodes numbered `n` and above are dummy
nodes. -/
def markConflicts (size n : Nat) (order : Array (Array Nat)) (up : Array (Array Nat))
    (pos : Array Nat) : Std.HashSet Nat := Id.run do
  let mut marked : Std.HashSet Nat := {}
  for i in [0:order.size - 1] do
    let upper := order.getD i #[]
    let lower := order.getD (i + 1) #[]
    let mut k0 := 0
    let mut l := 0
    for l1 in [0:lower.size] do
      let v := lower.getD l1 0
      let inner : Option Nat := if v ≥ n then (up.getD v #[]).find? (· ≥ n) else none
      if l1 + 1 == lower.size || inner.isSome then
        let k1 := match inner with
          | some u => pos.getD u 0
          | none => upper.size - 1
        for ll in [l:l1 + 1] do
          let w := lower.getD ll 0
          for u in up.getD w #[] do
            let k := pos.getD u 0
            if k < k0 || k > k1 then marked := marked.insert (segmentKey size u w)
        l := l1 + 1
        k0 := k1
  return marked

/-- One alignment and compaction. `layers` are the layers in the order they are processed (each
in left-to-right order), `nbr` the neighbours in the layer processed before, `sep u v` the least
distance between the centres of `u` left of `v`. Returns the coordinate of every node, at least
`0`. -/
def alignCompact (size : Nat) (marked : Std.HashSet Nat) (layers : Array (Array Nat))
    (nbr : Array (Array Nat)) (sep : Nat → Nat → Float) : Array Float := Id.run do
  let mut pos : Array Nat := Array.replicate size 0
  let mut pred : Array Nat := Array.replicate size size
  for layer in layers do
    for j in [0:layer.size] do
      let v := layer.getD j 0
      pos := pos.setIfInBounds v j
      pred := pred.setIfInBounds v (if j == 0 then size else layer.getD (j - 1) 0)
  -- vertical alignment
  let mut root : Array Nat := Array.range size
  let mut align : Array Nat := Array.range size
  for layer in layers do
    let mut r : Int := -1
    for v in layer do
      let ns := (nbr.getD v #[]).qsort fun a b =>
        pos.getD a 0 < pos.getD b 0 || (pos.getD a 0 == pos.getD b 0 && a < b)
      let d := ns.size
      if d > 0 then
        let lo := (d - 1) / 2
        let hi := d / 2
        for m in (if lo == hi then [lo] else [lo, hi]) do
          if align.getD v v == v then
            let u := ns.getD m 0
            let pu := pos.getD u 0
            if !marked.contains (segmentKey size u v) && r < (pu : Int) then
              align := align.setIfInBounds u v
              root := root.setIfInBounds v (root.getD u u)
              align := align.setIfInBounds v (root.getD v v)
              r := pu
  -- the block graph: an edge from the block of a node's left neighbour to the node's block
  let mut succs : Array (Array (Nat × Float)) := Array.replicate size #[]
  let mut indeg : Array Nat := Array.replicate size 0
  for r in [0:size] do
    if root.getD r r == r then
      let mut w := r
      for _ in [0:size] do
        let p := pred.getD w size
        if p < size then
          succs := succs.modify (root.getD p p) (·.push (r, sep p w))
          indeg := indeg.modify r (· + 1)
        w := align.getD w w
        if w == r then break
  -- longest paths through it, in topological order
  let mut xs : Array Float := Array.replicate size 0
  let mut queue : Array Nat :=
    (Array.range size).filter fun r => root.getD r r == r && indeg.getD r 0 == 0
  let mut head := 0
  for _ in [0:size + 1] do
    if head ≥ queue.size then break
    let u := queue.getD head 0
    head := head + 1
    let xu := xs.getD u 0
    for (r, s) in succs.getD u #[] do
      xs := xs.modify r fun x => max x (xu + s)
      indeg := indeg.modify r (· - 1)
      if indeg.getD r 0 == 0 then queue := queue.push r
  return (Array.range size).map fun v => xs.getD (root.getD v v) 0

/-- The mean of the middle two of four numbers. -/
def medianMean (a b c d : Float) : Float :=
  let lo := min (min a b) (min c d)
  let hi := max (max a b) (max c d)
  (a + b + c + d - lo - hi) / 2

/-- The coordinate of the centre of every node across the layers (`order` is the node order of
the layers, `up` and `down` the neighbours in the layers above and below, nodes numbered `n` and
above are dummy nodes, `bw` the widths): four alignments balanced as described in the module
docstring, shifted so that the leftmost edge of any node is at `0`. Neighbouring nodes of a
layer are at least `(bw u + bw v) / 2` plus `nodeGap` (two real nodes), `edgeGap` (two dummy
nodes) or their mean (one of each) apart. -/
def assignBreadth (size n : Nat) (order : Array (Array Nat)) (up down : Array (Array Nat))
    (bw : Array Float) (nodeGap edgeGap : Float) : Array Float := Id.run do
  if size == 0 then return #[]
  let pos := positionsOf size order
  let marked := markConflicts size n order up pos
  let sep := fun (u v : Nat) =>
    (bw.getD u 0 + bw.getD v 0) / 2 +
      (if u ≥ n && v ≥ n then edgeGap else if u ≥ n || v ≥ n then (nodeGap + edgeGap) / 2
        else nodeGap)
  let mirror := fun (o : Array (Array Nat)) => o.map Array.reverse
  let ul := alignCompact size marked order up sep
  let ur := (alignCompact size marked (mirror order) up sep).map (- ·)
  let dl := alignCompact size marked order.reverse down sep
  let dr := (alignCompact size marked (mirror order).reverse down sep).map (- ·)
  let all := #[ul, ur, dl, dr]
  let lo := fun (xs : Array Float) => (Array.range size).foldl
    (fun m v => min m (xs.getD v 0 - bw.getD v 0 / 2)) 1e300
  let hi := fun (xs : Array Float) => (Array.range size).foldl
    (fun m v => max m (xs.getD v 0 + bw.getD v 0 / 2)) (-1e300)
  let mut narrow := 0
  for k in [1:4] do
    let wk := hi (all.getD k #[]) - lo (all.getD k #[])
    if wk < hi (all.getD narrow #[]) - lo (all.getD narrow #[]) then narrow := k
  let ref := all.getD narrow #[]
  let shifted := (Array.range 4).map fun k =>
    let xs := all.getD k #[]
    let d := if k == 0 || k == 2 then lo ref - lo xs else hi ref - hi xs
    xs.map (· + d)
  let at_ := fun (k v : Nat) => (shifted.getD k #[]).getD v 0
  let xs := (Array.range size).map fun v => medianMean (at_ 0 v) (at_ 1 v) (at_ 2 v) (at_ 3 v)
  let left := lo xs
  return xs.map (· - left)

end PILean.Graph
