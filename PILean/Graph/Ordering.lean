/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# The proper layered graph and crossing reduction

Long edges are cut into chains of dummy nodes, one per layer crossed (`buildChains`), so that
every edge joins nodes of adjacent layers. The order of the nodes inside each layer is then
improved to reduce the crossings between adjacent layers (`orderLayers`):

* **Sweeps**: layer by layer, first downwards, then upwards, each node is placed by the
  barycenter (mean position) of its neighbours in the previous layer, compared exactly as a
  fraction of whole numbers; nodes without such neighbours keep their position; ties go to the
  current position, then the node number. A fixed number of sweeps is run.
* **Crossing count** (`crossings`): between two adjacent layers, the crossings are the
  inversions of the sequence of target positions taken in order of source position, counted with
  a Fenwick tree (the accumulator tree of Barth, Jünger and Mutzel, in an array): `O(E log V)`.
* **Best order**: after every sweep the order is kept when it has strictly fewer crossings than
  the best so far.
* **Transposition**: finally, adjacent nodes of a layer are swapped while that lowers the
  crossings of their edges (`transposePasses`); pairs whose degrees make the count costly are
  skipped, and the number of passes is fixed.

Work: `sweeps × (E log V + V log V)` for the sweeps, and at most `passes × (V + E × cap)` for
the transposition, where the cap bounds the pair of degrees compared.

## References

* Sugiyama, Tagawa, Toda, *Methods for visual understanding of hierarchical system structures*,
  IEEE Transactions on Systems, Man, and Cybernetics 11 (1981).
* Barth, Jünger, Mutzel, *Simple and efficient bilayer cross counting*, Journal of Graph
  Algorithms and Applications 8 (2004).
* Gansner, Koutsofios, North, Vo, *A technique for drawing directed graphs*, IEEE Transactions
  on Software Engineering 19 (1993).
-/

namespace PILean.Graph

/-- The dummy-node chains of the edges and the layer of every node, real and dummy.

`oriented k` is `some (a, b)` for the `k`-th edge when it is to be routed (`a` above `b`) and
`none` for a self-loop. Every chain starts at `a`, ends at `b`, and has one dummy node (numbered
from the number of real nodes upwards, in edge order) for each layer strictly between. Returns
the chains and the layers of all nodes. Work and size: the sum of the spans of the edges. -/
def buildChains (lay : Array Nat) (oriented : Array (Option (Nat × Nat))) :
    Array (Array Nat) × Array Nat := Id.run do
  let mut layerAll := lay
  let mut chains : Array (Array Nat) := Array.mkEmpty oriented.size
  for o in oriented do
    match o with
    | none => chains := chains.push #[]
    | some (a, b) =>
      let la := lay.getD a 0
      let lb := lay.getD b 0
      let mut chain : Array Nat := #[a]
      for l in [la + 1:lb] do
        chain := chain.push layerAll.size
        layerAll := layerAll.push l
      chains := chains.push (chain.push b)
  return (chains, layerAll)

/-- The neighbours above and below every node, from the chains. -/
def chainNeighbours (size : Nat) (chains : Array (Array Nat)) :
    Array (Array Nat) × Array (Array Nat) := Id.run do
  let mut up : Array (Array Nat) := Array.replicate size #[]
  let mut down : Array (Array Nat) := Array.replicate size #[]
  for c in chains do
    for j in [0:c.size - 1] do
      let a := c.getD j 0
      let b := c.getD (j + 1) 0
      down := down.modify a (·.push b)
      up := up.modify b (·.push a)
  return (up, down)

/-- The nodes by layer, each layer in the order of node numbers. -/
def initialLayers (layerAll : Array Nat) : Array (Array Nat) := Id.run do
  let count := layerAll.foldl (fun m l => max m (l + 1)) 0
  let mut layers : Array (Array Nat) := Array.replicate count #[]
  for v in [0:layerAll.size] do
    layers := layers.modify (layerAll.getD v 0) (·.push v)
  return layers

/-- The position of every node in its layer. -/
def positionsOf (size : Nat) (order : Array (Array Nat)) : Array Nat := Id.run do
  let mut pos : Array Nat := Array.replicate size 0
  for layer in order do
    for i in [0:layer.size] do
      pos := pos.setIfInBounds (layer.getD i 0) i
  return pos

/-- The crossings between a layer `upper` and the layer below, which has `lowerSize` nodes:
`down` lists the neighbours below, `pos` the positions. A Fenwick tree counts, for each edge in
order of source position, the earlier edges whose target lies further right. -/
def crossings (upper : Array Nat) (lowerSize : Nat) (down : Array (Array Nat))
    (pos : Array Nat) : Nat := Id.run do
  let mut tree : Array Nat := Array.replicate (lowerSize + 2) 0
  let mut inserted := 0
  let mut total := 0
  for x in upper do
    let ys := ((down.getD x #[]).map fun y => pos.getD y 0).qsort (· < ·)
    for y in ys do
      -- the number of inserted targets at positions ≤ y
      let mut i := y + 1
      let mut s := 0
      for _ in [0:64] do
        if i == 0 then break
        s := s + tree.getD i 0
        i := i &&& (i - 1)
      total := total + (inserted - s)
    for y in ys do
      let mut i := y + 1
      for _ in [0:64] do
        if i > lowerSize then break
        tree := tree.modify i (· + 1)
        i := i + (i - (i &&& (i - 1)))
      inserted := inserted + 1
  return total

/-- The crossings of the whole order. -/
def totalCrossings (order : Array (Array Nat)) (down : Array (Array Nat)) (pos : Array Nat) :
    Nat := Id.run do
  let mut total := 0
  for i in [0:order.size - 1] do
    total := total + crossings (order.getD i #[]) (order.getD (i + 1) #[]).size down pos
  return total

/-- A layer sorted by the barycenter of the neighbours listed in `nbr`, compared exactly (as the
fractions `sum / count`); a node without neighbours counts at its own position; ties go to the
current position, then the node number. -/
def reorder (layer : Array Nat) (nbr : Array (Array Nat)) (pos : Array Nat) : Array Nat :=
  let keyed : Array (Nat × Nat × Nat × Nat) := layer.map fun v =>
    let ns := nbr.getD v #[]
    if ns.isEmpty then (pos.getD v 0, 1, pos.getD v 0, v)
    else (ns.foldl (fun s u => s + pos.getD u 0) 0, ns.size, pos.getD v 0, v)
  let lt := fun (a b : Nat × Nat × Nat × Nat) =>
    let l := a.1 * b.2.1
    let r := b.1 * a.2.1
    l < r || (l == r && (a.2.2.1 < b.2.2.1 || (a.2.2.1 == b.2.2.1 && a.2.2.2 < b.2.2.2)))
  (keyed.qsort lt).map (·.2.2.2)

/-- The number of crossings between the edges of two adjacent nodes `u`, `v` of one layer when
`u` is left of `v` (counting the edges to the neighbours in `nbr`), or `none` when the
product of the degrees is above the cap. -/
def pairCrossings (nbr : Array (Array Nat)) (pos : Array Nat) (u v : Nat) : Option Nat :=
  let a := nbr.getD u #[]
  let b := nbr.getD v #[]
  if a.size * b.size > 400 then none
  else some (a.foldl (fun acc x => acc + b.foldl (fun c y =>
    if pos.getD x 0 > pos.getD y 0 then c + 1 else c) 0) 0)

/-- One left-to-right pass of adjacent swaps over every layer: `u v` are swapped when that
lowers the crossings of their edges with both neighbouring layers. Returns the new order and
positions and whether anything changed. -/
def transposePass (order : Array (Array Nat)) (pos : Array Nat) (up down : Array (Array Nat)) :
    Array (Array Nat) × Array Nat × Bool := Id.run do
  let mut order := order
  let mut pos := pos
  let mut changed := false
  for i in [0:order.size] do
    let mut layer := order.getD i #[]
    for j in [0:layer.size - 1] do
      let u := layer.getD j 0
      let v := layer.getD (j + 1) 0
      let keep := (pairCrossings up pos u v).bind fun a =>
        (pairCrossings down pos u v).map fun b => a + b
      let swapped := (pairCrossings up pos v u).bind fun a =>
        (pairCrossings down pos v u).map fun b => a + b
      match keep, swapped with
      | some k, some s =>
        if s < k then
          layer := (layer.setIfInBounds j v).setIfInBounds (j + 1) u
          pos := (pos.setIfInBounds u (j + 1)).setIfInBounds v j
          changed := true
      | _, _ => pure ()
    order := order.setIfInBounds i layer
  return (order, pos, changed)

/-- The order of the nodes inside the layers, from the initial `layers`, `sweeps` barycenter
sweeps (alternating down and up), keeping the order with the fewest crossings, then at most
three transposition passes. `up` and `down` list each node's neighbours in the layers above
and below; the result has the same nodes in the same layers. -/
def orderLayers (size : Nat) (layers : Array (Array Nat)) (up down : Array (Array Nat))
    (sweeps : Nat) : Array (Array Nat) := Id.run do
  let count := layers.size
  let mut order := layers
  let mut pos := positionsOf size order
  let mut best := order
  let mut bestC := totalCrossings order down pos
  for s in [0:sweeps] do
    if bestC == 0 then break
    if s % 2 == 0 then
      for i in [1:count] do
        let r := reorder (order.getD i #[]) up pos
        order := order.setIfInBounds i r
        for j in [0:r.size] do pos := pos.setIfInBounds (r.getD j 0) j
    else
      for k in [0:count - 1] do
        let i := count - 2 - k
        let r := reorder (order.getD i #[]) down pos
        order := order.setIfInBounds i r
        for j in [0:r.size] do pos := pos.setIfInBounds (r.getD j 0) j
    let c := totalCrossings order down pos
    if c < bestC then
      best := order
      bestC := c
  order := best
  pos := positionsOf size order
  for _ in [0:3] do
    if bestC == 0 then break
    let (o, p, changed) := transposePass order pos up down
    order := o
    pos := p
    if !changed then break
  return order

end PILean.Graph
