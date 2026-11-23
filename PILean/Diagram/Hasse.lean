/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Diagram.Graph

/-!
# Hasse diagrams

A `FinPoset` is a relation `le` on `Fin n`, read as an order. Its Hasse diagram draws an edge
from `i` up to `j` exactly when `j` covers `i` (`covers`: `i < j` and nothing lies strictly
between), with the elements in layers by height (the length of the longest chain of covers below
them), the lowest layer at the bottom, and each layer ordered by the mean position of the
elements it covers (one sweep up from the bottom, ties by number).

The diagram is a `FinGraph` (directed, no arrowheads) of the covering relation at the layered
positions, so the faithfulness of graphs carries over: the drawn edges are exactly the covering
pairs. For a partial order, the transitive closure of the covering relation is the strict order
(`transGen_covers_iff`), so the diagram determines the order.

## Main definitions

* `FinPoset`, `FinPoset.lt`, `FinPoset.covers`, `FinPoset.coverPairs`, `FinPoset.IsPartialOrder`
* `FinPoset.heights`, `FinPoset.layout`, `FinPoset.toFinGraph`, `FinPoset.figure`,
  `FinPoset.Faithful`

## Main results

* `FinPoset.mem_coverPairs`: a pair is drawn exactly when it is a cover.
* `FinPoset.draw_faithful`, `FinPoset.builder_faithful`: the drawn edges are `coverPairs`, in
  order, the vertices `0, …, n - 1`, each mark at the layout's position.
* `FinPoset.transGen_covers_iff`: for a partial order, `i < j` exactly when a chain of covers
  leads from `i` to `j`.
-/

namespace PILean.Diagram

/-- A finite order on the elements `0, …, n - 1`, given by its relation `le` (whether it is a
partial order is `IsPartialOrder`), with the elements' names. -/
structure FinPoset where
  /-- The number of elements. -/
  n : Nat
  /-- The order relation. -/
  le : Fin n → Fin n → Bool
  /-- The elements' names. -/
  names : Array String := #[]

namespace FinPoset

/-- The most elements `figure` draws: the covering relation takes `n³` steps to compute. -/
def maxElements : Nat := 128

/-- The strict relation: `le i j` and `i ≠ j`. -/
def lt (P : FinPoset) (i j : Fin P.n) : Bool := P.le i j && i != j

/-- Whether `j` covers `i`: `i < j` and no `k` has `i < k < j`. -/
def covers (P : FinPoset) (i j : Fin P.n) : Bool :=
  P.lt i j && !(List.finRange P.n).any fun k => P.lt i k && P.lt k j

/-- The covering pairs `(i, j)`, in the order of `i` and then `j`. -/
def coverPairs (P : FinPoset) : List (Nat × Nat) :=
  Graph.relationPairs (List.finRange P.n) P.covers

/-- The relation is a partial order: reflexive, antisymmetric and transitive. -/
structure IsPartialOrder (P : FinPoset) : Prop where
  /-- Every element is below itself. -/
  refl : ∀ i, P.le i i = true
  /-- Two elements below each other are equal. -/
  antisymm : ∀ i j, P.le i j = true → P.le j i = true → i = j
  /-- Below is transitive. -/
  trans : ∀ i j k, P.le i j = true → P.le j k = true → P.le i k = true

/-- The heights: element `j` at `0` when nothing is covered by it, otherwise one more than the
highest element it covers, computed by `n` rounds of relaxation over the covering pairs (enough
for a partial order, whose chains have at most `n` elements). -/
def heights (P : FinPoset) : Array Nat := Id.run do
  let pairs := P.coverPairs
  let mut h : Array Nat := Array.replicate P.n 0
  for _ in [0:P.n] do
    for (i, j) in pairs do
      let hi := h.getD i 0 + 1
      if hi > h.getD j 0 then h := h.set! j hi
  return h

/-- The layers: the elements of each height, from height 0 up, each layer ordered by the mean
horizontal position of the elements it covers in the layers below (ties, and elements covering
nothing, by number). The positions used are those of `layerPosition`. -/
def layers (P : FinPoset) : Array (Array Nat) := Id.run do
  let h := P.heights
  let top := h.foldl max 0
  let pairs := P.coverPairs
  let mut out : Array (Array Nat) := #[]
  let mut x : Array Rat := Array.replicate P.n 0
  for l in [0:top + 1] do
    let members := (List.range P.n).filter fun i => h.getD i 0 == l
    let key := fun (j : Nat) =>
      let below := pairs.filterMap fun (i, j') => if j' == j then some (x.getD i 0) else none
      if below.isEmpty then (0 : Rat) else below.foldl (· + ·) 0 / below.length
    let sorted := (members.map fun j => (key j, j)).toArray.qsort fun a b =>
      a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)
    let layer := sorted.map (·.2)
    for k in [0:layer.size] do
      x := x.set! (layer.getD k 0) ((k : Rat) - ((layer.size : Rat) - 1) / 2)
    out := out.push layer
  return out

/-- The exact position of each element: its place `k` in its layer of size `s` gives
`x = k - (s - 1) / 2`, its height `y`, both times `gap`. -/
def layerPositions (P : FinPoset) (gap : Rat := 1) : Array QPoint := Id.run do
  let mut pos : Array QPoint := Array.replicate P.n (0, 0)
  let ls := P.layers
  for l in [0:ls.size] do
    let layer := ls.getD l #[]
    for k in [0:layer.size] do
      pos := pos.set! (layer.getD k 0) (gap * ((k : Rat) - ((layer.size : Rat) - 1) / 2), gap * l)
  return pos

/-- The layout of the Hasse diagram: `layerPositions`, loops (which a partial order's covers never
are) of radius `1/8`. -/
def layout (P : FinPoset) : Layout := Layout.given P.layerPositions

/-- The graph of the covering relation: directed, drawn without arrowheads. -/
def toFinGraph (P : FinPoset) : FinGraph where
  n := P.n
  adj := P.covers
  directed := true
  arrowheads := false
  names := P.names

/-- The edges of the graph of the covering relation are the covering pairs. -/
theorem toFinGraph_edgePairs (P : FinPoset) : P.toFinGraph.edgePairs = P.coverPairs := by sorry

/-- A pair is drawn exactly when its two elements exist and the second covers the first. -/
theorem mem_coverPairs (P : FinPoset) (i j : Nat) :
    (i, j) ∈ P.coverPairs ↔ ∃ (hi : i < P.n) (hj : j < P.n), P.covers ⟨i, hi⟩ ⟨j, hj⟩ = true := by sorry

/-- The diagram at the layout `L`. -/
def draw (P : FinPoset) (L : Layout) : Diagram := P.toFinGraph.draw L

/-- The diagram draws the order faithfully at `L`: its edges are exactly `coverPairs`, in order,
its vertex dots `0, …, n - 1`, every mark at `L`'s position for its part. -/
def Faithful (P : FinPoset) (L : Layout) (d : Diagram) : Prop :=
  d.edges = P.coverPairs ∧ d.vertices = List.range P.n ∧ d.marks.all (P.toFinGraph.placed L) = true

instance (P : FinPoset) (L : Layout) (d : Diagram) : Decidable (P.Faithful L d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The Hasse diagram is faithful at every layout. -/
theorem draw_faithful (P : FinPoset) (L : Layout) : P.Faithful L (P.draw L) := by sorry

/-- The Hasse diagram of the order, or a note for more than `maxElements` elements. -/
def figure (P : FinPoset) : Diagram :=
  if P.n ≤ maxElements then P.draw P.layout
  else
    let note := s!"{P.n} elements: too many to draw"
    { marks := [{ part := .note 0, shape := .text note (0, 0) .center }] }

/-- An order on at most `maxElements` elements is drawn faithfully by `figure`. -/
theorem builder_faithful (P : FinPoset) (h : P.n ≤ maxElements) :
    P.Faithful P.layout P.figure := by sorry

/-! ### The covering relation determines the order -/

/-- A count of the elements that satisfy a stronger predicate is smaller when some element
satisfies the weaker one only. -/
theorem countP_lt_of_imp {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true → q x = true) → (∃ x ∈ l, q x = true ∧ p x = false) →
      l.countP p < l.countP q := by sorry

variable {P : FinPoset}

/-- In a partial order the strict relation is transitive. -/
theorem IsPartialOrder.lt_trans (hP : P.IsPartialOrder) {i j k : Fin P.n} (hij : P.lt i j = true)
    (hjk : P.lt j k = true) : P.lt i k = true := by sorry

/-- In a partial order nothing is strictly below itself. -/
theorem lt_irrefl (i : Fin P.n) : P.lt i i = false := by sorry

/-- A cover is a strict relation. -/
theorem lt_of_covers {i j : Fin P.n} (h : P.covers i j = true) : P.lt i j = true := by sorry

/-- For a partial order, `i < j` exactly when a chain of covers leads from `i` to `j`: the
transitive closure of the drawn edges is the strict order. -/
theorem transGen_covers_iff (hP : P.IsPartialOrder) (i j : Fin P.n) :
    Relation.TransGen (fun a b => P.covers a b = true) i j ↔ P.lt i j = true := by sorry

end FinPoset

/-- The hypotheses can be met: the chain `0 ≤ 1 ≤ 2` is a partial order whose covers are
`(0, 1)` and `(1, 2)`. -/
example : FinPoset.IsPartialOrder ⟨3, fun i j => decide (i ≤ j), #[]⟩ ∧
    (FinPoset.mk 3 (fun i j => decide (i ≤ j)) #[]).coverPairs = [(0, 1), (1, 2)] := by sorry

end PILean.Diagram
