/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Std.Data.HashMap

/-!
# The proper layered graph and crossing reduction

Long edges are cut into chains of dummy nodes, one per layer crossed (`buildChains`), so that
every edge joins nodes of adjacent layers. The order of the nodes inside each layer is then
improved to reduce the crossings between adjacent layers (`orderLayers`):

* **Initial orders** (`initialLayers`, `initialLayersBfs`): the nodes of each layer in the order
  of a depth-first or of a breadth-first search from the nodes without neighbours above.
* **Sweeps** (`reorderMedian`): layer by layer, first downwards, then upwards, the nodes that have
  neighbours in the previous layer are sorted by the *weighted median* of their positions
  (Gansner et al.: the middle position, the mean of the two for two, otherwise the two middle
  positions weighted by the spread on the other side); nodes without such neighbours keep their
  places; ties go to the current position, then the node number.
* **Transposition** (`transposePass`): after each sweep adjacent nodes of a layer are swapped
  while that lowers the crossings of their edges with both neighbouring layers; pairs whose
  degrees make the count costly are skipped, and the passes are bounded.
* **Crossing count** (`crossings`): between two adjacent layers, the crossings are the
  inversions of the sequence of target positions taken in order of source position, counted with
  a Fenwick tree (the accumulator tree of Barth, Jünger and Mutzel, in an array): `O(E log V)`.
* **Best order** (`reduceFrom`): after every round the order is kept when it has strictly fewer
  crossings than the best so far; the rounds stop after a run without improvement or at the
  bound. `orderLayers` runs it from both initial orders (from the depth-first one only on large
  graphs) and keeps the better result.
* **Clusters** (`groupClusters`): the members of a cluster are gathered, and the clusters stand
  in the same order in every layer.

Work: at most `sweeps × (E log V + V log V + passes × (V + E × cap))`, where the cap bounds the
pair of degrees compared in a transposition.

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

/-- The nodes by layer, in the order of a depth-first search from the nodes without neighbours
above (in node order, each node's lower neighbours in listed order): nodes that are connected
start near each other. Nodes the search does not reach (none, when every edge runs between
adjacent layers) follow in node order. Work: `O(V + E)`. -/
def initialLayers (layerAll : Array Nat) (up down : Array (Array Nat)) : Array (Array Nat) :=
  Id.run do
    let size := layerAll.size
    let count := layerAll.foldl (fun m l => max m (l + 1)) 0
    let mut layers : Array (Array Nat) := Array.replicate count #[]
    let mut seen : Array Bool := Array.replicate size false
    for root in [0:size] do
      if (up.getD root #[]).isEmpty && !seen.getD root true then
        let mut stack : Array Nat := #[root]
        for _ in [0:size + (down.foldl (fun s d => s + d.size) 0) + 1] do
          match stack.back? with
          | none => break
          | some v =>
            stack := stack.pop
            if !seen.getD v true then
              seen := seen.setIfInBounds v true
              layers := layers.modify (layerAll.getD v 0) (·.push v)
              for w in (down.getD v #[]).reverse do
                if !seen.getD w true then stack := stack.push w
    for v in [0:size] do
      if !seen.getD v true then
        layers := layers.modify (layerAll.getD v 0) (·.push v)
    return layers

/-- The nodes by layer, in the order of a breadth-first search from the nodes without neighbours
above (in node order, each node's lower neighbours in listed order). Nodes the search does not
reach follow in node order. Work: `O(V + E)`. -/
def initialLayersBfs (layerAll : Array Nat) (up down : Array (Array Nat)) : Array (Array Nat) :=
  Id.run do
    let size := layerAll.size
    let count := layerAll.foldl (fun m l => max m (l + 1)) 0
    let mut layers : Array (Array Nat) := Array.replicate count #[]
    let mut seen : Array Bool := Array.replicate size false
    let mut queue : Array Nat := #[]
    for root in [0:size] do
      if (up.getD root #[]).isEmpty then
        seen := seen.setIfInBounds root true
        queue := queue.push root
    let mut head := 0
    for _ in [0:size + 1] do
      if head ≥ queue.size then break
      let v := queue.getD head 0
      head := head + 1
      layers := layers.modify (layerAll.getD v 0) (·.push v)
      for w in down.getD v #[] do
        if !seen.getD w true then
          seen := seen.setIfInBounds w true
          queue := queue.push w
    for v in [0:size] do
      if !seen.getD v true then
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

/-- The weighted median of the sorted positions `ps` of a node's neighbours (Gansner et al.): the
middle position for an odd count, the mean of the two middle ones for two, and otherwise the
mean of the two middle positions weighted by the spread of the neighbours on the other side
(a median leaning towards the denser side). `-1` when `ps` is empty. -/
def weightedMedian (ps : Array Nat) : Float :=
  let d := ps.size
  if d == 0 then -1
  else
    let m := d / 2
    let at_ := fun (i : Nat) => (ps.getD i 0).toFloat
    if d % 2 == 1 then at_ m
    else if d == 2 then (at_ 0 + at_ 1) / 2
    else
      let left := at_ (m - 1) - at_ 0
      let right := at_ (d - 1) - at_ m
      if left + right == 0 then at_ m
      else (at_ (m - 1) * right + at_ m * left) / (left + right)

/-- A layer reordered by the weighted medians of the positions of the neighbours listed in
`nbr`: the nodes that have neighbours are sorted by median (ties: current position, then node
number) into the places those nodes held; the other nodes stay where they are. -/
def reorderMedian (layer : Array Nat) (nbr : Array (Array Nat)) (pos : Array Nat) :
    Array Nat := Id.run do
  let mut keyed : Array (Float × Nat × Nat) := #[]
  let mut slots : Array Nat := #[]
  for j in [0:layer.size] do
    let v := layer.getD j 0
    let ns := nbr.getD v #[]
    if !ns.isEmpty then
      let ps := (ns.map fun u => pos.getD u 0).qsort (· < ·)
      keyed := keyed.push (weightedMedian ps, j, v)
      slots := slots.push j
  let lt := fun (a b : Float × Nat × Nat) =>
    a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)))
  let sorted := keyed.qsort lt
  let mut out := layer
  for i in [0:slots.size] do
    out := out.setIfInBounds (slots.getD i 0) (sorted.getD i (0, 0, 0)).2.2
  return out

/-- The number of crossings between the edges of two adjacent nodes `u`, `v` of one layer when
`u` is left of `v` (counting the edges to the neighbours in `nbr`), or `none` when the
product of the degrees is above the cap. -/
def pairCrossings (nbr : Array (Array Nat)) (pos : Array Nat) (u v : Nat) : Option Nat :=
  let a := nbr.getD u #[]
  let b := nbr.getD v #[]
  if a.size * b.size > 2500 then none
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

/-- The order of the nodes inside the layers and its crossings, from the initial `layers`: at
most `sweeps` rounds of a weighted-median sweep (down on even rounds, up on odd ones) followed
by transposition until no adjacent swap helps (at most `8` passes), the order with the fewest
crossings kept; the search stops after `4` rounds in a row that found nothing better. `up` and
`down` list each node's neighbours in the layers above and below; the result has the same nodes
in the same layers. -/
def reduceFrom (size : Nat) (layers : Array (Array Nat)) (up down : Array (Array Nat))
    (sweeps : Nat) : Array (Array Nat) × Nat := Id.run do
  let count := layers.size
  let mut order := layers
  let mut pos := positionsOf size order
  let mut best := order
  let mut bestC := totalCrossings order down pos
  let mut stall := 0
  for s in [0:sweeps] do
    if bestC == 0 || stall ≥ 4 then break
    if s % 2 == 0 then
      for i in [1:count] do
        let r := reorderMedian (order.getD i #[]) up pos
        order := order.setIfInBounds i r
        for j in [0:r.size] do pos := pos.setIfInBounds (r.getD j 0) j
    else
      for k in [0:count - 1] do
        let i := count - 2 - k
        let r := reorderMedian (order.getD i #[]) down pos
        order := order.setIfInBounds i r
        for j in [0:r.size] do pos := pos.setIfInBounds (r.getD j 0) j
    for _ in [0:8] do
      let (o, p, changed) := transposePass order pos up down
      order := o
      pos := p
      if !changed then break
    let c := totalCrossings order down pos
    if c < bestC then
      best := order
      bestC := c
      stall := 0
    else stall := stall + 1
  return (best, bestC)

/-- The order of the nodes inside the layers: `reduceFrom` the depth-first and from the
breadth-first initial orders, the one with fewer crossings (the depth-first on a tie; only the
depth-first for more than 6000 nodes, real and dummy). -/
def orderLayers (layerAll : Array Nat) (up down : Array (Array Nat)) (sweeps : Nat) :
    Array (Array Nat) :=
  let size := layerAll.size
  let a := reduceFrom size (initialLayers layerAll up down) up down sweeps
  if a.2 == 0 || size > 6000 then a.1
  else
    let b := reduceFrom size (initialLayersBfs layerAll up down) up down sweeps
    let c := reduceFrom size (initialLayers layerAll down up) up down sweeps
    let best := if b.2 < a.2 then b else a
    if c.2 < best.2 then c.1 else best.1

/-- Gathers the members of each cluster: every cluster gets one place across the whole drawing,
the mean of its members' relative positions in their layers (position plus a half, over the
layer's size), and in each layer its members take that place, in their old order; the other
nodes keep their relative places. So the clusters stand side by side in the same order in every
layer. `clusterOf v` is the number of `v`'s cluster, `none` for none (and for dummy nodes).
Work: `O(V log V)`. -/
def groupClusters (order : Array (Array Nat)) (clusterOf : Nat → Option Nat) :
    Array (Array Nat) :=
  let stats : Std.HashMap Nat (Float × Nat) := Id.run do
    let mut m : Std.HashMap Nat (Float × Nat) := {}
    for layer in order do
      for i in [0:layer.size] do
        if let some c := clusterOf (layer.getD i 0) then
          let (sum, cnt) := m.getD c (0, 0)
          m := m.insert c (sum + (i.toFloat + 0.5) / layer.size.toFloat, cnt + 1)
    return m
  order.map fun layer =>
    let keyed : Array (Float × Nat × Nat) := (Array.range layer.size).map fun i =>
      match clusterOf (layer.getD i 0) with
      | some c =>
        let (sum, cnt) := stats.getD c (0, 1)
        (sum / cnt.toFloat, c + 1, i)
      | none => ((i.toFloat + 0.5) / layer.size.toFloat, 0, i)
    let lt := fun (a b : Float × Nat × Nat) =>
      a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)))
    (keyed.qsort lt).map fun k => layer.getD k.2.2 0

end PILean.Graph
