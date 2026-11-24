/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Std.Data.HashMap
import PILean.Sort

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
* **Sifting** (`siftLayer`, `siftRound`, `siftFrom`): after the sweeps, each node of a layer, the
  nodes of most edges first, is taken out and put where its edges cross the fewest edges of the
  other nodes of the layer, rounds over all layers alternately down and up, each followed by
  transposition, while the crossings fall (Matuszewski, Schönfeld and Molitor).
* **Best order** (`reduceFrom`): after every round the order is kept when it has strictly fewer
  crossings than the best so far; the rounds stop after a run without improvement or at the
  bound, and the best order is sifted. `orderLayers` runs it from the depth-first, the
  breadth-first and the bottom-up depth-first initial orders (from the depth-first one only on
  large graphs) and from more depth-first orders drawn from a fixed pseudo-random sequence
  (`initialLayersSeeded`, as many as `extraStarts` allows for the size of the graph), and keeps
  the best result.
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
* Matuszewski, Schönfeld, Molitor, *Using sifting for k-layer straightline crossing
  minimization*, Graph Drawing 1999, LNCS 1731.
-/

namespace PILean.Graph

/-- The dummy-node chains of the edges and the layer of every node, real and dummy.

`oriented k` is `some (a, b)` for the `k`-th edge when it is to be routed (`a` above `b`) and
`none` for a self-loop. Every chain starts at `a`, ends at `b`, and has one dummy node (numbered
from the number of real nodes upwards, in edge order) for each layer strictly between, unless
the real and dummy nodes together would be more than `maxSize`: then no edge gets dummy nodes
(each chain is its two ends), so a graph whose edges span many layers costs `O(V + E)` here
instead of the sum of the spans. Returns the chains and the layers of all nodes. Work and size:
the sum of the spans of the edges, at most `maxSize` plus `O(E)`. -/
def buildChains (lay : Array Nat) (oriented : Array (Option (Nat × Nat)))
    (maxSize : Nat := 200000) : Array (Array Nat) × Array Nat := Id.run do
  let dummies := oriented.foldl (init := 0) fun acc o => match o with
    | some (a, b) => acc + (lay.getD b 0 - lay.getD a 0 - 1)
    | none => acc
  if lay.size + dummies > maxSize then
    return (oriented.map fun o => match o with | some (a, b) => #[a, b] | none => #[], lay)
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
    -- the most steps of one search (computed once: per root it would make the work quadratic)
    let steps := size + down.foldl (fun s d => s + d.size) 0 + 1
    for root in [0:size] do
      if (up.getD root #[]).isEmpty && !seen.getD root true then
        let mut stack : Array Nat := #[root]
        for _ in [0:steps] do
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

/-- A step of a fixed pseudo-random sequence (a linear congruential generator): the next state
and a number below `2 ^ 31`. The extra starts of the crossing reduction draw from it, so they are
the same on every run. -/
def nextRandom (s : UInt64) : UInt64 × Nat :=
  let s := s * 6364136223846793005 + 1442695040888963407
  (s, (s >>> 33).toNat)

/-- `xs` in an order drawn from the sequence at state `s` (Fisher and Yates), with the state
after it. -/
def shuffle (xs : Array Nat) (s : UInt64) : Array Nat × UInt64 := Id.run do
  let mut xs := xs
  let mut s := s
  for k in [0:xs.size] do
    let i := xs.size - 1 - k
    let (s', r) := nextRandom s
    s := s'
    let j := r % (i + 1)
    let a := xs.getD i 0
    xs := (xs.setIfInBounds i (xs.getD j 0)).setIfInBounds j a
  return (xs, s)

/-- The nodes by layer in the order of a depth-first search as `initialLayers` makes it, but
from the roots in an order drawn from the fixed sequence at `seed`, each node's lower neighbours
in a drawn order too. Work: `O(V + E)`. -/
def initialLayersSeeded (layerAll : Array Nat) (up down : Array (Array Nat)) (seed : Nat) :
    Array (Array Nat) := Id.run do
  let size := layerAll.size
  let count := layerAll.foldl (fun m l => max m (l + 1)) 0
  let mut layers : Array (Array Nat) := Array.replicate count #[]
  let mut seen : Array Bool := Array.replicate size false
  let (roots, s0) := shuffle ((Array.range size).filter fun v => (up.getD v #[]).isEmpty)
    (seed.toUInt64 * 2654435761 + 97)
  let mut s := s0
  let steps := size + down.foldl (fun s d => s + d.size) 0 + 1
  for root in roots do
    if !seen.getD root true then
      let mut stack : Array Nat := #[root]
      for _ in [0:steps] do
        match stack.back? with
        | none => break
        | some v =>
          stack := stack.pop
          if !seen.getD v true then
            seen := seen.setIfInBounds v true
            layers := layers.modify (layerAll.getD v 0) (·.push v)
            let (ws, s') := shuffle (down.getD v #[]) s
            s := s'
            for w in ws do
              if !seen.getD w true then stack := stack.push w
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
    let ys := ((down.getD x #[]).map fun y => pos.getD y 0).sortStable (· < ·)
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
      let ps := (ns.map fun u => pos.getD u 0).sortStable (· < ·)
      keyed := keyed.push (weightedMedian ps, j, v)
      slots := slots.push j
  let lt := fun (a b : Float × Nat × Nat) =>
    a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)))
  let sorted := keyed.sortStable lt
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

/-- One left-to-right pass of adjacent swaps over every layer: `u v` are swapped when
`canSwap u v` allows it and the swap lowers the crossings of their edges with both neighbouring
layers (with `ties`, also when it leaves them equal and not zero, which moves the search off a
plateau; such a swap does not count as a change). Returns the new order and positions and
whether anything got better. -/
def transposePass (order : Array (Array Nat)) (pos : Array Nat) (up down : Array (Array Nat))
    (canSwap : Nat → Nat → Bool := fun _ _ => true) (ties : Bool := false) :
    Array (Array Nat) × Array Nat × Bool := Id.run do
  let mut order := order
  let mut pos := pos
  let mut changed := false
  for i in [0:order.size] do
    let mut layer := order.getD i #[]
    for j in [0:layer.size - 1] do
      let u := layer.getD j 0
      let v := layer.getD (j + 1) 0
      if !canSwap u v then continue
      let keep := (pairCrossings up pos u v).bind fun a =>
        (pairCrossings down pos u v).map fun b => a + b
      let swapped := (pairCrossings up pos v u).bind fun a =>
        (pairCrossings down pos v u).map fun b => a + b
      match keep, swapped with
      | some k, some s =>
        if s < k || (ties && s == k && k > 0) then
          layer := (layer.setIfInBounds j v).setIfInBounds (j + 1) u
          pos := (pos.setIfInBounds u (j + 1)).setIfInBounds v j
          if s < k then changed := true
      | _, _ => pure ()
    order := order.setIfInBounds i layer
  return (order, pos, changed)

/-- For sorted positions `a` of the neighbours of a node `u` and `b` of a node `v` of the same
layer: the crossings between their edges when `u` stands left of `v`, and when `v` stands left
of `u` (one merge, `O(|a| + |b|)`). -/
def crossBothWays (a b : Array Nat) : Nat × Nat := Id.run do
  -- for each x in a: the y in b below x cross when u is left, the y above x when v is left
  let mut below := 0
  let mut notAbove := 0
  let mut uLeft := 0
  let mut vLeft := 0
  for x in a do
    for _ in [0:b.size] do
      if below < b.size && b.getD below 0 < x then below := below + 1 else break
    for _ in [0:b.size] do
      if notAbove < b.size && b.getD notAbove 0 ≤ x then notAbove := notAbove + 1 else break
    uLeft := uLeft + below
    vLeft := vLeft + (b.size - notAbove)
  return (uLeft, vLeft)

/-- One layer sifted (Matuszewski, Schönfeld and Molitor): each node that `movable` allows, the
nodes of most edges first, is taken out and put where the crossings of its edges with the edges
of the other nodes of the layer are fewest, over all places from `lo v` to `hi v` (positions
among the other nodes; the whole layer by default); on a tie it stays as near as it can to where
it stood. `upPos` and `downPos` give every node's sorted neighbour positions in the layers above
and below, which do not change. Work: `O(k² d)` for `k` nodes of mean degree `d`. Returns the
layer and whether any node moved to a place with fewer crossings. -/
def siftLayer (layer : Array Nat) (upPos downPos : Nat → Array Nat)
    (movable : Nat → Bool := fun _ => true)
    (range : Array Nat → Nat → Nat × Nat := fun rest _ => (0, rest.size)) :
    Array Nat × Bool := Id.run do
  let degree := fun (v : Nat) => (upPos v).size + (downPos v).size
  let byDegree := (layer.filter fun v => movable v && degree v > 0).sortStable fun u v =>
    degree u > degree v || (degree u == degree v && u < v)
  let mut order := layer
  let mut improved := false
  for v in byDegree do
    let at_ := (order.idxOf? v).getD 0
    let rest := order.eraseIdxIfInBounds at_
    let (lo, hi) := range rest at_
    let lo := min lo at_
    let hi := max (min hi rest.size) at_
    let uv := upPos v
    let dv := downPos v
    -- the cost of standing at `lo`, then the change of every step to the right
    let mut cost : Int := 0
    let mut steps : Array Int := Array.mkEmpty (hi - lo)
    for j in [lo:hi] do
      let u := rest.getD j 0
      let (ul, vl) := crossBothWays (upPos u) uv
      let (ul', vl') := crossBothWays (downPos u) dv
      -- `u` left of `v`: `ul + ul'`; `v` left of `u`: `vl + vl'`
      cost := cost + Int.ofNat (vl + vl')
      steps := steps.push (Int.ofNat (ul + ul') - Int.ofNat (vl + vl'))
    let mut cur := cost
    let mut here := cost
    let mut best := cost
    let mut bestAt := lo
    let mut bestDist := at_ - lo
    for j in [lo:hi] do
      if j == at_ then here := cur
      cur := cur + steps.getD (j - lo) 0
      let d := if j + 1 ≥ at_ then j + 1 - at_ else at_ - (j + 1)
      if cur < best || (cur == best && d < bestDist) then
        best := cur
        bestAt := j + 1
        bestDist := d
    if at_ == hi then here := cur
    if best < here then
      improved := true
      order := rest.insertIdxIfInBounds bestAt v
  return (order, improved)

/-- One round of sifting over every layer, from the top down or from the bottom up: each layer
is sifted against the current orders of its neighbours (`siftLayer`). Returns the order, the
positions and whether anything got better. -/
def siftRound (order : Array (Array Nat)) (pos : Array Nat) (up down : Array (Array Nat))
    (downward : Bool) : Array (Array Nat) × Array Nat × Bool := Id.run do
  let mut order := order
  let mut pos := pos
  let mut improved := false
  let count := order.size
  for k in [0:count] do
    let i := if downward then k else count - 1 - k
    let layer := order.getD i #[]
    if layer.size < 2 then continue
    let p := pos
    let sorted := fun (nbr : Array (Array Nat)) =>
      (layer.foldl (init := (∅ : Std.HashMap Nat (Array Nat))) fun m v =>
        m.insert v (((nbr.getD v #[]).map fun u => p.getD u 0).sortStable (· < ·)))
    let ups := sorted up
    let downs := sorted down
    let (r, better) := siftLayer layer (ups.getD · #[]) (downs.getD · #[])
    if better then
      improved := true
      order := order.setIfInBounds i r
      for j in [0:r.size] do pos := pos.setIfInBounds (r.getD j 0) j
  return (order, pos, improved)

/-- The most pairs of nodes of one layer, summed over the layers, that a round of sifting may
compare: above it the order is left as the sweeps found it. -/
def siftPairLimit : Nat := 6000000

/-- The order improved by sifting: rounds over all layers, alternately downwards and upwards,
each followed by transposition, while the crossings fall (at most `rounds` rounds). Graphs whose
layers hold more than `siftPairLimit` pairs of nodes in all are returned as they are. -/
def siftFrom (size : Nat) (order : Array (Array Nat)) (crossings : Nat)
    (up down : Array (Array Nat)) (rounds : Nat := 12) : Array (Array Nat) × Nat := Id.run do
  let pairs := order.foldl (fun s l => s + l.size * l.size) 0
  if crossings == 0 || pairs > siftPairLimit then return (order, crossings)
  let mut best := order
  let mut bestC := crossings
  let mut cur := order
  let mut pos := positionsOf size order
  let mut stall := 0
  for r in [0:rounds] do
    if bestC == 0 || stall ≥ 2 then break
    let (o, p, _) := siftRound cur pos up down (r % 2 == 0)
    cur := o
    pos := p
    for _ in [0:8] do
      let (o, p, changed) := transposePass cur pos up down
      cur := o
      pos := p
      if !changed then break
    let c := totalCrossings cur down pos
    if c < bestC then
      best := cur
      bestC := c
      stall := 0
    else stall := stall + 1
  return (best, bestC)

/-- The order of the nodes inside the layers and its crossings, from the initial `layers`: at
most `sweeps` rounds of a weighted-median sweep (down on even rounds, up on odd ones) followed
by transposition until no adjacent swap helps (at most `8` passes; the first pass of an up round
also swaps pairs with equal crossings), the order with the fewest
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
    for t in [0:8] do
      let (o, p, changed) := transposePass order pos up down (ties := s % 2 == 1 && t == 0)
      order := o
      pos := p
      if !changed then break
    let c := totalCrossings order down pos
    if c < bestC then
      best := order
      bestC := c
      stall := 0
    else stall := stall + 1
  return siftFrom size best bestC up down

/-- The work the extra starts of the crossing reduction may take in all, in pairs of nodes of
one layer (summed over the layers, per start). -/
def extraStartWork : Nat := 600000

/-- How many extra starts (`initialLayersSeeded`) the crossing reduction makes on a layered graph
whose layers hold `pairs` pairs of nodes in all: as many as `extraStartWork` allows, at most
`most`. -/
def extraStarts (pairs most : Nat) : Nat := min most (extraStartWork / max 1 pairs)

/-- The order of the nodes inside the layers: `reduceFrom` the depth-first, the breadth-first
and the bottom-up depth-first initial orders (only the first for more than 6000 nodes, real and
dummy), and from up to `starts` more depth-first orders drawn from a fixed sequence, as many as
`extraStarts` allows for the graph's size; the order with the fewest crossings, the earliest on a
tie. -/
def orderLayers (layerAll : Array Nat) (up down : Array (Array Nat)) (sweeps : Nat)
    (starts : Nat := 24) : Array (Array Nat) := Id.run do
  let size := layerAll.size
  let a := reduceFrom size (initialLayers layerAll up down) up down sweeps
  if a.2 == 0 || size > 6000 then return a.1
  -- the other starts are searched at the same time, and the first of the best results is kept,
  -- as if they had been searched one after the other
  let pairs := a.1.foldl (fun s l => s + l.size * l.size) 0
  let others : Array (Task (Array (Array Nat) × Nat)) :=
    #[Task.spawn fun _ => reduceFrom size (initialLayersBfs layerAll up down) up down sweeps,
      Task.spawn fun _ => reduceFrom size (initialLayers layerAll down up) up down sweeps] ++
    (Array.range (extraStarts pairs starts)).map fun k => Task.spawn fun _ =>
      reduceFrom size (initialLayersSeeded layerAll up down k) up down sweeps
  let mut best := a
  for task in others do
    let r := task.get
    if r.2 < best.2 then best := r
  return best.1

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
    (keyed.sortStable lt).map fun k => layer.getD k.2.2 0

end PILean.Graph
