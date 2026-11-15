/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# Cycle removal and layer assignment

The first two phases of the layered layout (Sugiyama, Tagawa and Toda; Gansner et al.):

* **Cycle removal** (`elsPositions`): the greedy heuristic of Eades, Lin and Smyth for a small
  feedback arc set. It orders the nodes so that few edges point backwards; an edge is reversed
  (for layout only) when it does. Work: `O(V + E)` plus one `O(V)` scan for each time no node is
  a source or sink, so at most `O(V² + E)`; the loop runs at most `3 V + 2` times.
* **Layer assignment** (`assignLayers`): longest-path layering of the acyclic edges, from the
  sources, then a few balancing passes (`balanceLayers`) that move nodes between the layers their
  neighbours leave free, to shorten edges (fewer dummy nodes) and to even out the layers, then
  `fixLayers` once more. Work: `O(V log V + E)` for the layering, `O(V (log V + L) + E)` for
  each balancing pass.

The edges are first oriented by the order of the nodes (`orient`: a pair `(u, v)` stays when `u`
comes before `v`, else it is turned) and sorted by the order of their source (`acyclicEdges`).
Relaxing the edges in that order (`fixLayers`) gives every edge `layer src < layer dst`, whatever
layers it starts from: `PILean.Graph.Proofs` proves this for the function the layout calls.

## References

* Eades, Lin, Smyth, *A fast and effective heuristic for the feedback arc set problem*,
  Information Processing Letters 47 (1993).
* Gansner, Koutsofios, North, Vo, *A technique for drawing directed graphs*, IEEE Transactions
  on Software Engineering 19 (1993).
* Sugiyama, Tagawa, Toda, *Methods for visual understanding of hierarchical system structures*,
  IEEE Transactions on Systems, Man, and Cybernetics 11 (1981).
-/

namespace PILean.Graph

/-- The position of every node in the order of the Eades–Lin–Smyth heuristic for the edges
`edges` (pairs of node numbers below `n`; loops and out-of-range pairs are ignored): sinks go to
the end, sources to the front, and when neither exists the node with the largest out-degree
minus in-degree goes to the front. Ties go to the smaller node number, so the result is
deterministic. The result is a permutation of `0, …, n - 1`. -/
def elsPositions (n : Nat) (edges : Array (Nat × Nat)) : Array Nat := Id.run do
  let mut outAdj : Array (Array Nat) := Array.replicate n #[]
  let mut inAdj : Array (Array Nat) := Array.replicate n #[]
  for (u, v) in edges do
    if u < n && v < n && u != v then
      outAdj := outAdj.modify u (·.push v)
      inAdj := inAdj.modify v (·.push u)
  let mut outDeg := outAdj.map (·.size)
  let mut inDeg := inAdj.map (·.size)
  let mut removed : Array Bool := Array.replicate n false
  let mut work : Array Nat :=
    (Array.range n).filter fun v => outDeg.getD v 0 == 0 || inDeg.getD v 0 == 0
  let mut front : Array Nat := #[]
  let mut back : Array Nat := #[]
  let mut left := n
  for _ in [0:3 * n + 2] do
    if left == 0 then break
    let mut pick : Option Nat := none
    let mut toFront := true
    match work.back? with
    | some w =>
      work := work.pop
      if !removed.getD w true then
        pick := some w
        toFront := outDeg.getD w 0 != 0
    | none =>
      let mut best : Option (Nat × Int) := none
      for v in [0:n] do
        if !removed.getD v true then
          let d : Int := (outDeg.getD v 0 : Int) - (inDeg.getD v 0 : Int)
          match best with
          | some (_, bd) => if d > bd then best := some (v, d)
          | none => best := some (v, d)
      pick := best.map (·.1)
    if let some w := pick then
      if toFront then front := front.push w else back := back.push w
      removed := removed.setIfInBounds w true
      left := left - 1
      for x in outAdj.getD w #[] do
        if !removed.getD x true then
          inDeg := inDeg.modify x (· - 1)
          if inDeg.getD x 0 == 0 then work := work.push x
      for x in inAdj.getD w #[] do
        if !removed.getD x true then
          outDeg := outDeg.modify x (· - 1)
          if outDeg.getD x 0 == 0 then work := work.push x
  let rest := (Array.range n).filter fun v => !removed.getD v true
  let seq := front ++ rest ++ back.reverse
  let mut pos : Array Nat := Array.replicate n 0
  for i in [0:seq.size] do
    pos := pos.setIfInBounds (seq.getD i 0) i
  return pos

/-- `a` comes before `b`: its position is smaller, or equal with the smaller node number. This
is a strict total order on the nodes whatever `pos` is. -/
def before (pos : Array Nat) (a b : Nat) : Bool :=
  pos.getD a 0 < pos.getD b 0 || (pos.getD a 0 == pos.getD b 0 && a < b)

/-- The edge pointing from the node that comes first to the other. -/
def orient (pos : Array Nat) (e : Nat × Nat) : Nat × Nat :=
  if before pos e.1 e.2 then e else (e.2, e.1)

/-- The acyclic edges of `edges`: loops dropped, the others oriented by `orient`, and sorted by
the order of their source (the order in which `fixLayers` has to relax them). -/
def acyclicEdges (pos : Array Nat) (edges : List (Nat × Nat)) : List (Nat × Nat) :=
  ((edges.filter fun e => e.1 != e.2).map (orient pos)).mergeSort
    fun a b => !before pos b.1 a.1

/-- One relaxation: the target of the edge is at least one layer below its source. -/
def relax (layer : Array Nat) (e : Nat × Nat) : Array Nat :=
  let below := layer.getD e.1 0 + 1
  layer.modify e.2 fun l => max l below

/-- Relaxes the edges in order, starting from `layer`. Run on `acyclicEdges`, the result puts
every edge's target below its source, and each node is moved down no further than that
requires. -/
def fixLayers (edges : List (Nat × Nat)) (layer : Array Nat) : Array Nat :=
  edges.foldl relax layer

/-- Balancing: `rounds` passes over the nodes (from the top layer down, then from the bottom
up, alternately), each node moving within the layers its neighbours leave free (below all its
predecessors, above all its successors): to the lowest one when it has more out-edges than
in-edges, to the highest when it has more in-edges, and otherwise to the freest layer (fewest
nodes, the current one on ties). Edges stay pointing downwards and the total of the edges' spans
never grows. Work: `O(rounds × (V log V + E + V L))` for `L` layers. -/
def balanceLayers (n : Nat) (es : List (Nat × Nat)) (layer : Array Nat) (rounds : Nat) :
    Array Nat := Id.run do
  let mut outAdj : Array (Array Nat) := Array.replicate n #[]
  let mut inAdj : Array (Array Nat) := Array.replicate n #[]
  for (u, v) in es do
    if u < n && v < n then
      outAdj := outAdj.modify u (·.push v)
      inAdj := inAdj.modify v (·.push u)
  let top := layer.foldl max 0
  let mut l := layer
  let mut cnt : Array Nat := Array.replicate (top + 1) 0
  for v in [0:n] do cnt := cnt.modify (l.getD v 0) (· + 1)
  for r in [0:rounds] do
    let order := (Array.range n).qsort fun a b =>
      let la := l.getD a 0
      let lb := l.getD b 0
      if r % 2 == 0 then la < lb || (la == lb && a < b) else la > lb || (la == lb && a < b)
    for u in order do
      let outs := outAdj.getD u #[]
      let ins := inAdj.getD u #[]
      let lo := ins.foldl (fun a v => max a (l.getD v 0 + 1)) 0
      let hi := outs.foldl (fun a v => min a (l.getD v 0 - 1)) top
      let cur := l.getD u 0
      if lo ≤ cur && cur ≤ hi then
        let mut target := cur
        if outs.size > ins.size then target := hi
        else if ins.size > outs.size then target := lo
        else
          for t in [lo:hi + 1] do
            if cnt.getD t 0 < cnt.getD target 0 then target := t
        if target != cur then
          l := l.setIfInBounds u target
          cnt := (cnt.modify cur (· - 1)).modify target (· + 1)
  return l

/-- The layer of each of the `n` nodes for the edges `edges` (pairs of node numbers below `n`)
and the node order `pos`: longest-path layers of `acyclicEdges`, balanced, then relaxed once
more with `fixLayers` (the balancing is used only if it kept the number of nodes, which it
always does), so that every acyclic edge points to a larger layer
(`PILean.Graph.Proofs`). -/
def assignLayers (pos : Array Nat) (n : Nat) (edges : List (Nat × Nat)) : Array Nat :=
  let es := acyclicEdges pos edges
  let l0 := fixLayers es (Array.replicate n 0)
  let l1 := balanceLayers n es l0 6
  fixLayers es (if l1.size = n then l1 else l0)

end PILean.Graph
