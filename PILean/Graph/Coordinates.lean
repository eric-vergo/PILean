/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Std.Data.HashSet
import PILean.Graph.Ordering
import PILean.Graph.Simplex
import PILean.Sort

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

Work: `O(V + E)` per alignment up to the sorting of each node's neighbours. The four alignments
are the start of the last step:

5. **Refinement** (`refineBreadth`): a fixed number of passes that move each *unit* (a node, or
   a straight run of dummy nodes of one long edge, moved as one) towards the median of the
   positions of the nodes it is connected to, as far as the separations from its neighbours in
   the layers allow, alternately from the left and from the right. Straight runs stay straight,
   the order never changes, and the separations keep holding. Work: `O(passes × (V log V + E))`.
6. **Network simplex** (`simplexBreadth`): the coordinates that minimise the weighted total
   horizontal length of the edges' segments (Gansner et al., section 4.2), found by the network
   simplex of `PILean.Graph.Simplex` from the refined coordinates, on an auxiliary graph with a
   node for each segment and an edge for each pair of neighbours in a layer. Segments between
   dummy nodes weigh most, so the chains of long edges stay straight where they can. The search
   improves the coordinates with every exchange, and it has a bound on the exchanges and on the
   work: on a large graph it stops early and returns the improved coordinates it has.

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
      let ns := (nbr.getD v #[]).sortStable fun a b =>
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

/-- The least distance between the centres of `u` left of `v`: half the widths plus `nodeGap`
(two real nodes), `edgeGap` (two dummy nodes) or their mean (one of each; the nodes numbered `n`
and above are dummy nodes), plus `clusterGap` when the two are not in the same cluster and one
is in a cluster (`cluster v` is the number of the cluster of `v`). -/
def separation (n : Nat) (bw : Array Float) (nodeGap edgeGap clusterGap : Float)
    (cluster : Array (Option Nat)) (u v : Nat) : Float :=
  let cu := cluster.getD u none
  let cv := cluster.getD v none
  (bw.getD u 0 + bw.getD v 0) / 2 +
    (if u ≥ n && v ≥ n then edgeGap else if u ≥ n || v ≥ n then (nodeGap + edgeGap) / 2
      else nodeGap) +
    (if cu != cv then clusterGap else 0)

/-- The mean of the middle two of four numbers. -/
def medianMean (a b c d : Float) : Float :=
  let lo := min (min a b) (min c d)
  let hi := max (max a b) (max c d)
  (a + b + c + d - lo - hi) / 2

/-- The coordinate of the centre of every node across the layers (`order` is the node order of
the layers, `up` and `down` the neighbours in the layers above and below, nodes numbered `n` and
above are dummy nodes, `sep u v` the least distance between the centres of `u` left of `v`, `bw`
the widths): four alignments balanced as described in the module docstring, shifted so that the
leftmost edge of any node is at `0`. -/
def assignBreadth (size n : Nat) (order : Array (Array Nat)) (up down : Array (Array Nat))
    (sep : Nat → Nat → Float) (bw : Array Float) : Array Float := Id.run do
  if size == 0 then return #[]
  let pos := positionsOf size order
  let marked := markConflicts size n order up pos
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

/-- The coordinates that minimise the weighted total horizontal length of the segments of the
chains, by network simplex (Gansner et al., section 4.2), starting from the coordinates `x`:
every segment `(a, b)` of a chain becomes a node `s` with edges `s → a` and `s → b` of length
`0` (so that `s` sits at the least of the two and the cost of the segment is `|x a - x b|`), the
weight `1` for two real nodes, `2` for one dummy node and `8` for two (long edges stay straight);
neighbours `u`, `v` in a layer get an edge `u → v` of length `sep u v` and weight `0`.

Nodes can share one coordinate: `var v` is the variable of node `v` (the identity when `var` is
empty), and the layer edges join variables. `extra` adds edges `(a, b, length, weight)` between
variables (in half pixels). The order of the layers and the extra edges must leave the edges
between variables without a cycle.

Coordinates are whole numbers of half pixels (the separation is rounded up to half pixels). The
start is `x` rounded and moved right, in an order of the variables that follows the edges, where
a separation would be violated. The method never makes a coordinate assignment worse, so it
stops after `rounds m + 50` exchanges for `m` nodes of the problem, or when the work (`budget`,
in the units of `simplexComponent`) is used up, and returns what it has, shifted so that the
leftmost edge of any node (widths `bw`) is at `0`. -/
def simplexBreadth (size n : Nat) (chains order : Array (Array Nat)) (sep : Nat → Nat → Float)
    (bw : Array Float) (x : Array Float) (rounds budget : Nat) (var : Array Nat := #[])
    (extra : Array (Nat × Nat × Int × Int) := #[]) : Array Float := Id.run do
  let toHalf := fun (f : Float) => Int.ofNat (f * 2).ceil.toUInt64.toNat
  let vr := fun (v : Nat) => if var.isEmpty then v else var.getD v v
  -- the constraints between variables: layer neighbours, then the extra edges
  let mut cons : Array (Nat × Nat × Int × Int) := #[]
  for layer in order do
    for j in [1:layer.size] do
      let u := layer.getD (j - 1) 0
      let v := layer.getD j 0
      cons := cons.push (vr u, vr v, toHalf (sep u v), 0)
  cons := cons ++ extra
  -- the start: positions in half pixels, repaired in an order that follows the constraints
  let mut pos : Array Int := (Array.range size).map fun v =>
    Int.ofNat ((x.getD (vr v) (x.getD v 0)) * 2).round.toUInt64.toNat
  let mut outs : Array (Array Nat) := Array.replicate size #[]
  let mut indeg : Array Nat := Array.replicate size 0
  for k in [0:cons.size] do
    let (a, b, _, _) := cons.getD k (0, 0, 0, 0)
    if a < size && b < size then
      outs := outs.modify a (·.push k)
      indeg := indeg.modify b (· + 1)
  let mut queue : Array Nat := (Array.range size).filter (indeg.getD · 0 == 0)
  let mut head := 0
  for _ in [0:size] do
    if head ≥ queue.size then break
    let a := queue.getD head 0
    head := head + 1
    for k in outs.getD a #[] do
      let (_, b, l, _) := cons.getD k (0, 0, 0, 0)
      pos := pos.setIfInBounds b (max (pos.getD b 0) (pos.getD a 0 + l))
      indeg := indeg.modify b (· - 1)
      if indeg.getD b 0 == 0 then queue := queue.push b
  let mut start := pos
  let mut tails : Array Nat := #[]
  let mut heads : Array Nat := #[]
  let mut minlen : Array Int := #[]
  let mut weight : Array Int := #[]
  for (a, b, l, w) in cons do
    tails := tails.push a
    heads := heads.push b
    minlen := minlen.push l
    weight := weight.push w
  let mut total := size
  for c in chains do
    for j in [1:c.size] do
      let a := vr (c.getD (j - 1) 0)
      let b := vr (c.getD j 0)
      let w : Int := if a ≥ n && b ≥ n then 8 else if a ≥ n || b ≥ n then 2 else 1
      start := start.push (min (pos.getD a 0) (pos.getD b 0))
      tails := (tails.push total).push total
      heads := (heads.push a).push b
      minlen := (minlen.push 0).push 0
      weight := (weight.push w).push w
      total := total + 1
  let (r, _) := simplexSolve total tails heads minlen weight start rounds budget
  let sol := if r.size == total then r else start
  let xs := (Array.range size).map fun v => (sol.getD (vr v) 0).toNat.toFloat / 2
  let left := (Array.range size).foldl (fun m v => min m (xs.getD v 0 - bw.getD v 0 / 2)) 1e300
  return xs.map (· - left)

/-- The median of a list of numbers (the mean of the two middle ones for an even count), `none`
for no numbers. -/
def medianOf (xs : Array Float) : Option Float :=
  if xs.isEmpty then none
  else
    let s := xs.sortStable (· < ·)
    let k := s.size / 2
    if s.size % 2 == 1 then s[k]? else
      match s[k - 1]?, s[k]? with
      | some a, some b => some ((a + b) / 2)
      | _, _ => none

/-- Moves units of the layout towards the median of their neighbours, `passes` times (see the
module docstring). `chains` are the chains of the edges (a unit joins consecutive dummy nodes of
one chain that are at the same position), `x` the positions to start from, the other arguments
as in `assignBreadth`. The result satisfies the same separations as `x` does. -/
def refineBreadth (size n : Nat) (chains order : Array (Array Nat)) (up down : Array (Array Nat))
    (sep : Nat → Nat → Float) (bw : Array Float) (x : Array Float) (passes : Nat) :
    Array Float := Id.run do
  -- neighbours inside the layers
  let mut leftN : Array Nat := Array.replicate size size
  let mut rightN : Array Nat := Array.replicate size size
  for layer in order do
    for j in [0:layer.size] do
      let v := layer.getD j 0
      if j > 0 then leftN := leftN.setIfInBounds v (layer.getD (j - 1) 0)
      if j + 1 < layer.size then rightN := rightN.setIfInBounds v (layer.getD (j + 1) 0)
  -- units
  let mut unitOf : Array Nat := Array.range size
  for c in chains do
    for j in [1:c.size] do
      let v := c.getD j 0
      let w := c.getD (j - 1) 0
      if v ≥ n && w ≥ n && (x.getD v 0 - x.getD w 0).abs < 0.5 then
        unitOf := unitOf.setIfInBounds v (unitOf.getD w w)
  let mut members : Array (Array Nat) := Array.replicate size #[]
  for v in [0:size] do
    members := members.modify (unitOf.getD v v) (·.push v)
  let units := (Array.range size).filter fun u => !(members.getD u #[]).isEmpty
  let mut xs := x
  for pass in [0:passes] do
    let sorted := units.sortStable fun a b =>
      let xa := xs.getD ((members.getD a #[]).getD 0 0) 0
      let xb := xs.getD ((members.getD b #[]).getD 0 0) 0
      if pass % 2 == 0 then xa < xb || (xa == xb && a < b) else xa > xb || (xa == xb && a < b)
    for u in sorted do
      let ms := members.getD u #[]
      let mut near : Array Float := #[]
      let mut lo : Float := -1e300
      let mut hi : Float := 1e300
      for v in ms do
        for w in up.getD v #[] do
          if unitOf.getD w w != u then near := near.push (xs.getD w 0)
        for w in down.getD v #[] do
          if unitOf.getD w w != u then near := near.push (xs.getD w 0)
        let l := leftN.getD v size
        if l < size then lo := max lo (xs.getD l 0 + sep l v)
        let r := rightN.getD v size
        if r < size then hi := min hi (xs.getD r 0 - sep v r)
      match medianOf near with
      | none => pure ()
      | some d =>
        if lo ≤ hi then
          let target := max lo (min hi d)
          for v in ms do xs := xs.setIfInBounds v target
  let left := (Array.range size).foldl (fun m v => min m (xs.getD v 0 - bw.getD v 0 / 2)) 1e300
  return xs.map (· - left)

end PILean.Graph
