/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Diagram.Graph

/-!
# Permutations

A `FinPerm` is a permutation of `0, …, n - 1` in one-line notation: the list
`[σ 0, σ 1, …, σ (n - 1)]` (whether it is a permutation is `IsPerm`). It is drawn five ways:

* `oneLine`: the values `σ 0, …, σ (n - 1)` in a row (written from `base`, 1 by default);
* `twoLine`: the arguments above and the values below;
* `matrix`: the permutation matrix, a dot in row `i` and column `σ i` of an `n × n` grid, row 0 at
  the top;
* `cycles`: the functional graph `i → σ i` on a circle, the vertices in the order of the cycles
  (each cycle from its least element), so that a cycle runs round the circle; a fixed point is a
  loop;
* `wiring`: strand `i` a segment from `(i, 1)` at the top to `(σ i, 0)` at the bottom. Two strands
  between the two lines cross exactly when their order changes, so the drawn crossings are the
  inversions: `wiring_crossings` proves that the pairs of strands that cross are exactly the
  pairs `i < j` with `σ i > σ j`, so there are as many as the inversions.

## Main definitions

* `FinPerm`, `FinPerm.IsPerm`, `FinPerm.apply`, `FinPerm.inversions`, `FinPerm.cycleOrder`
* `FinPerm.oneLine`, `twoLine`, `matrix`, `cycles`, `wiring` with their `Faithful…` predicates
* `Diagram.strands`, `crossingPairs`: the strands a diagram draws and those that cross

## Main results

* `FinPerm.oneLine_faithful`, `twoLine_faithful`, `matrix_faithful`, `cycles_faithful`,
  `wiring_faithful`
* `FinPerm.mem_inversions`, `FinPerm.wiring_crossings`: the crossings of the wiring diagram are
  the inversions.
-/

namespace PILean.Diagram

/-- The strands a diagram draws: `(i, p, q)` for each mark of the part `strand i` that is the
segment from `p` to `q`, in order. -/
def Diagram.strands (d : Diagram) : List (Nat × QPoint × QPoint) :=
  d.marks.filterMap fun m => match m.part, m.shape with
    | .strand i, .segment p q => some (i, p, q)
    | _, _ => none

/-- The pairs of strands that cross, read from their ends: strands `(a, p, q)` and `(b, p', q')`
running from a top line to a bottom line cross exactly when the top end of `a` is left of `b`'s and
its bottom end right of `b`'s. Each crossing pair `(a, b)` is listed once, `a` the strand whose top
end is on the left, in the order of the strands. -/
def crossingPairs (ss : List (Nat × QPoint × QPoint)) : List (Nat × Nat) :=
  ss.flatMap fun (a, p, q) => ss.filterMap fun (b, p', q') =>
    if p.1 < p'.1 ∧ q'.1 < q.1 then some (a, b) else none

/-- A permutation of `0, …, n - 1` in one-line notation, its values written from `base`. -/
structure FinPerm where
  /-- The values `σ 0, σ 1, …`. -/
  values : List Nat
  /-- The number the first argument is written as (1 for the usual notation). -/
  base : Nat := 1

namespace FinPerm

/-- The size `n`. -/
def n (σ : FinPerm) : Nat := σ.values.length

/-- The value at `i` (0 outside). -/
def apply (σ : FinPerm) (i : Nat) : Nat := σ.values.getD i 0

/-- Whether the values are a permutation of `0, …, n - 1`: each of them occurs exactly once. -/
def IsPerm (σ : FinPerm) : Prop :=
  (List.range σ.n).all (fun k => σ.values.count k == 1) = true

instance (σ : FinPerm) : Decidable σ.IsPerm := inferInstanceAs (Decidable (_ = _))

/-- The most values the figures draw. -/
def maxSize : Nat := 128

/-- The inversions: the pairs `i < j` with `σ i > σ j`, in the order of `i` and then `j`. -/
def inversions (σ : FinPerm) : List (Nat × Nat) :=
  (List.range σ.n).flatMap fun i => (List.range σ.n).filterMap fun j =>
    if i < j ∧ σ.apply j < σ.apply i then some (i, j) else none

/-- A pair is an inversion exactly when `i < j < n` and `σ i > σ j`. -/
theorem mem_inversions (σ : FinPerm) (i j : Nat) :
    (i, j) ∈ σ.inversions ↔ i < j ∧ j < σ.n ∧ σ.apply j < σ.apply i := by sorry

/-- The text of a number from the base. -/
def text (σ : FinPerm) (k : Nat) : String := toString (k + σ.base)

/-- The one-line notation: value `σ i` written at `(i, 0)`, as entry `(0, i)`. -/
def oneLine (σ : FinPerm) : Diagram where
  marks := (List.range σ.n).map fun i =>
    { part := .entry 0 i, shape := .text (σ.text (σ.apply i)) ((i : Rat), 0) .center }
  width := 32 * σ.n.toFloat + 24

/-- The entries the one-line notation writes: `((0, i), σ i)` for each `i`, in order. -/
def oneLineEntries (σ : FinPerm) : List ((Nat × Nat) × String) :=
  (List.range σ.n).map fun i => ((0, i), σ.text (σ.apply i))

/-- The one-line diagram is faithful: its entries are the values, in order. -/
def FaithfulOneLine (σ : FinPerm) (d : Diagram) : Prop := d.entries = σ.oneLineEntries

instance (σ : FinPerm) (d : Diagram) : Decidable (σ.FaithfulOneLine d) :=
  inferInstanceAs (Decidable (_ = _))

/-- The one-line notation writes the values, in order. -/
theorem oneLine_faithful (σ : FinPerm) : σ.FaithfulOneLine σ.oneLine := by sorry

/-- The two-line notation: argument `i` at `(i, 1)` (entry `(0, i)`), its value `σ i` below it at
`(i, 0)` (entry `(1, i)`), and a bar between the rows. -/
def twoLine (σ : FinPerm) : Diagram where
  marks := (List.range σ.n).map (fun i =>
      { part := .entry 0 i, shape := .text (σ.text i) ((i : Rat), 1) .center }) ++
    (List.range σ.n).map (fun i =>
      { part := .entry 1 i, shape := .text (σ.text (σ.apply i)) ((i : Rat), 0) .center }) ++
    [{ part := .guide, shape := .segment (-1 / 2, 1 / 2) ((σ.n : Rat) - 1 / 2, 1 / 2),
       ink := .faint }]
  width := 32 * σ.n.toFloat + 24

/-- The entries of the two-line notation: the arguments, then the values. -/
def twoLineEntries (σ : FinPerm) : List ((Nat × Nat) × String) :=
  (List.range σ.n).map (fun i => ((0, i), σ.text i)) ++
    (List.range σ.n).map (fun i => ((1, i), σ.text (σ.apply i)))

/-- The two-line diagram is faithful: its entries are the arguments and then their values. -/
def FaithfulTwoLine (σ : FinPerm) (d : Diagram) : Prop := d.entries = σ.twoLineEntries

instance (σ : FinPerm) (d : Diagram) : Decidable (σ.FaithfulTwoLine d) :=
  inferInstanceAs (Decidable (_ = _))

/-- The two-line notation writes the arguments and their values. -/
theorem twoLine_faithful (σ : FinPerm) : σ.FaithfulTwoLine σ.twoLine := by sorry

/-- The centre of cell `(i, j)` of the matrix, row 0 at the top. -/
def matrixCentre (i j : Nat) : QPoint := ((j : Rat) + 1 / 2, -((i : Rat) + 1 / 2))

/-- The permutation matrix: the `n × n` grid (guides), then a dot at the centre of cell
`(i, σ i)` for each `i` (part `cell i (σ i)`). -/
def matrix (σ : FinPerm) : Diagram where
  marks := ((List.range σ.n).flatMap fun (i : Nat) => (List.range σ.n).map fun (j : Nat) =>
      ({ part := .guide, shape := .rect ((j : Rat), -((i : Rat) + 1)) ((j : Rat) + 1, -(i : Rat)),
         ink := .faint } : Mark)) ++
    (List.range σ.n).map fun i =>
      { part := .cell i (σ.apply i), shape := .dot (matrixCentre i (σ.apply i)) }
  width := 28 * σ.n.toFloat + 24

/-- The matrix is faithful: its marked cells are `(i, σ i)`, in order of `i`, each a dot at its
cell's centre. -/
def FaithfulMatrix (σ : FinPerm) (d : Diagram) : Prop :=
  d.cells = (List.range σ.n).map (fun i => (i, σ.apply i)) ∧
    d.marks.all (fun m => match m.part, m.shape with
      | .cell i j, .dot p => p == matrixCentre i j
      | .cell _ _, _ => false
      | _, _ => true) = true

instance (σ : FinPerm) (d : Diagram) : Decidable (σ.FaithfulMatrix d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The permutation matrix marks exactly the cells `(i, σ i)`. -/
theorem matrix_faithful (σ : FinPerm) : σ.FaithfulMatrix σ.matrix := by sorry

/-- The order of the vertices round the circle: each cycle in turn, from its least element and
then its images, the cycles in the order of their least elements (at most `n` steps a cycle, so
the work is bounded for any list). -/
def cycleOrder (σ : FinPerm) : List Nat := Id.run do
  let mut seen : Array Bool := Array.replicate σ.n false
  let mut out : Array Nat := #[]
  for s in [0:σ.n] do
    if !seen.getD s true then
      let mut k := s
      for _ in [0:σ.n] do
        if seen.getD k true then break
        seen := seen.set! k true
        out := out.push k
        k := σ.apply k
  return out.toList

/-- The functional graph `i → σ i`, directed. -/
def toFinGraph (σ : FinPerm) : FinGraph where
  n := σ.n
  adj i j := σ.apply i == j.val
  directed := true
  names := ((List.range σ.n).map σ.text).toArray

/-- The cycle layout: the `k`-th vertex of `cycleOrder` at the `k`-th place of the circle. -/
def cycleLayout (σ : FinPerm) : Layout :=
  let order := σ.cycleOrder
  let circle := Layout.circular σ.n
  Layout.given (((List.range σ.n).map fun i => circle.pos (order.idxOf i)).toArray)

/-- The cycle diagram: the functional graph at the cycle layout. -/
def cycles (σ : FinPerm) : Diagram := σ.toFinGraph.draw σ.cycleLayout

/-- The cycle diagram is faithful: it is the functional graph's diagram, faithful at the cycle
layout (`FinGraph.Faithful`). -/
def FaithfulCycles (σ : FinPerm) (d : Diagram) : Prop := σ.toFinGraph.Faithful σ.cycleLayout d

instance (σ : FinPerm) (d : Diagram) : Decidable (σ.FaithfulCycles d) :=
  inferInstanceAs (Decidable (σ.toFinGraph.Faithful _ d))

/-- The cycle diagram draws exactly the arrows `i → σ i`. -/
theorem cycles_faithful (σ : FinPerm) : σ.FaithfulCycles σ.cycles := by sorry

/-- A pair is an arrow of the cycle diagram exactly when `i < n` and `j = σ i < n`. -/
theorem mem_cycles_edges (σ : FinPerm) (i j : Nat) :
    (i, j) ∈ σ.cycles.edges ↔ i < σ.n ∧ j < σ.n ∧ σ.apply i = j := by sorry

/-- The strand of `i`: from `(i, 1)` to `(σ i, 0)`. -/
def strand (σ : FinPerm) (i : Nat) : Nat × QPoint × QPoint :=
  (i, ((i : Rat), 1), ((σ.apply i : Rat), 0))

/-- The wiring diagram: the top and bottom lines (guides), then strand `i` for each `i`. -/
def wiring (σ : FinPerm) : Diagram where
  marks := [{ part := .guide, shape := .segment (-1 / 2, 1) ((σ.n : Rat) - 1 / 2, 1), ink := .faint },
      { part := .guide, shape := .segment (-1 / 2, 0) ((σ.n : Rat) - 1 / 2, 0), ink := .faint }] ++
    (List.range σ.n).map fun i =>
      let (_, p, q) := σ.strand i
      { part := .strand i, shape := .segment p q, ink := .accent (i % 3) }
  width := 40 * σ.n.toFloat + 24

/-- The wiring diagram is faithful: its strands are `strand 0, …, strand (n - 1)`, in order. -/
def FaithfulWiring (σ : FinPerm) (d : Diagram) : Prop :=
  d.strands = (List.range σ.n).map σ.strand

instance (σ : FinPerm) (d : Diagram) : Decidable (σ.FaithfulWiring d) :=
  inferInstanceAs (Decidable (_ = _))

/-- The wiring diagram draws the strands. -/
theorem wiring_faithful (σ : FinPerm) : σ.FaithfulWiring σ.wiring := by sorry

/-- The pairs of strands of the wiring diagram that cross are exactly the inversions, in
order. -/
theorem wiring_crossings (σ : FinPerm) : crossingPairs σ.wiring.strands = σ.inversions := by sorry

/-- The wiring diagram has as many crossings as the permutation has inversions. -/
theorem wiring_crossings_length (σ : FinPerm) :
    (crossingPairs σ.wiring.strands).length = σ.inversions.length := by sorry

end FinPerm

/-- The hypotheses can be met: `[2, 0, 1]` is a permutation with the inversions `(0, 1)` and
`(0, 2)`. -/
example : (FinPerm.mk [2, 0, 1] 1).IsPerm ∧
    (FinPerm.mk [2, 0, 1] 1).inversions = [(0, 1), (0, 2)] := by sorry

end PILean.Diagram
