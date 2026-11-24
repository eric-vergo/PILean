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
* `wiring`: strand `i` a segment from `(i, 2)` at the top to `(σ i, 0)` at the bottom. Two strands
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
    (i, j) ∈ σ.inversions ↔ i < j ∧ j < σ.n ∧ σ.apply j < σ.apply i := by
  simp only [inversions, List.mem_flatMap, List.mem_range, List.mem_filterMap]
  constructor
  · rintro ⟨i', hi, j', hj, h⟩
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      omega
    · simp at h
  · rintro ⟨hij, hj, hv⟩
    exact ⟨i, by omega, j, hj, by simp [hij, hv]⟩

/-- The text of a number from the base. -/
def text (σ : FinPerm) (k : Nat) : String := toString (k + σ.base)

/-- The marks of the one-line notation: value `σ i` written at `(i, 0)`, as entry `(0, i)`. -/
def oneLineMarks (σ : FinPerm) : List Mark :=
  (List.range σ.n).map fun i =>
    { part := .entry 0 i, shape := .text (σ.text (σ.apply i)) ((i : Rat), 0) .center }

/-- The one-line notation (`oneLineMarks`). -/
def oneLine (σ : FinPerm) : Diagram where
  marks := σ.oneLineMarks
  width := 32 * σ.n.toFloat + 24

/-- The entries the one-line notation writes: `((0, i), σ i)` for each `i`, in order. -/
def oneLineEntries (σ : FinPerm) : List ((Nat × Nat) × String) :=
  (List.range σ.n).map fun i => ((0, i), σ.text (σ.apply i))

/-- The one-line diagram is faithful: its entries are the values, in order; its texts are exactly
those entries, value `σ i` at `(i, 0)`; and its marks are exactly `oneLineMarks` (no other mark,
each in the ink). -/
def FaithfulOneLine (σ : FinPerm) (d : Diagram) : Prop :=
  d.entries = σ.oneLineEntries ∧
    d.texts = (List.range σ.n).map (fun i => (.entry 0 i, σ.text (σ.apply i), ((i : Rat), 0))) ∧
    d.marks = σ.oneLineMarks

instance (σ : FinPerm) (d : Diagram) : Decidable (σ.FaithfulOneLine d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The one-line notation writes the values, in order. -/
theorem oneLine_faithful (σ : FinPerm) : σ.FaithfulOneLine σ.oneLine := by
  refine ⟨?_, ?_, rfl⟩ <;>
  simp [Diagram.entries, Diagram.texts, oneLine, oneLineMarks, oneLineEntries, List.filterMap_map,
    Function.comp_def]

/-- The entries of the two-line notation as marks: argument `i` at `(i, 1)` (entry `(0, i)`), then
its value `σ i` below it at `(i, 0)` (entry `(1, i)`). -/
def twoLineEntryMarks (σ : FinPerm) : List Mark :=
  (List.range σ.n).map (fun i =>
      { part := .entry 0 i, shape := .text (σ.text i) ((i : Rat), 1) .center }) ++
    (List.range σ.n).map (fun i =>
      { part := .entry 1 i, shape := .text (σ.text (σ.apply i)) ((i : Rat), 0) .center })

/-- The bar between the rows of the two-line notation (a guide). -/
def twoLineBar (σ : FinPerm) : List Mark :=
  [{ part := .guide, shape := .segment (-1 / 2, 1 / 2) ((σ.n : Rat) - 1 / 2, 1 / 2),
     ink := .faint }]

/-- The two-line notation: the entries (`twoLineEntryMarks`) and the bar between the rows. -/
def twoLine (σ : FinPerm) : Diagram where
  marks := σ.twoLineEntryMarks ++ σ.twoLineBar
  width := 32 * σ.n.toFloat + 24

/-- The entries of the two-line notation: the arguments, then the values. -/
def twoLineEntries (σ : FinPerm) : List ((Nat × Nat) × String) :=
  (List.range σ.n).map (fun i => ((0, i), σ.text i)) ++
    (List.range σ.n).map (fun i => ((1, i), σ.text (σ.apply i)))

/-- The two-line diagram is faithful: its entries are the arguments and then their values; its
texts are exactly those, argument `i` at `(i, 1)` and `σ i` below it at `(i, 0)`; its marks of
entries are exactly `twoLineEntryMarks` and its decorations exactly the bar (`twoLineBar`),
with their colour roles; and it has no mark of any other part. -/
def FaithfulTwoLine (σ : FinPerm) (d : Diagram) : Prop :=
  d.entries = σ.twoLineEntries ∧
    d.texts = (List.range σ.n).map (fun i => (.entry 0 i, σ.text i, ((i : Rat), 1))) ++
      (List.range σ.n).map (fun i => (.entry 1 i, σ.text (σ.apply i), ((i : Rat), 0))) ∧
    d.marksWhere Part.isEntry = σ.twoLineEntryMarks ∧
    d.marksWhere Part.isDecoration = σ.twoLineBar ∧
    d.marks.all (fun m => m.part.isEntry || m.part.isDecoration) = true

instance (σ : FinPerm) (d : Diagram) : Decidable (σ.FaithfulTwoLine d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The two-line notation writes the arguments and their values. -/
theorem twoLine_faithful (σ : FinPerm) : σ.FaithfulTwoLine σ.twoLine := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Diagram.entries, twoLine, twoLineEntryMarks, twoLineBar, twoLineEntries,
      List.filterMap_append, List.filterMap_map, Function.comp_def]
  · simp [Diagram.texts, twoLine, twoLineEntryMarks, twoLineBar, List.filterMap_append,
      List.filterMap_map, Function.comp_def]
  · simp [twoLine, twoLineEntryMarks, twoLineBar, Part.isEntry, Function.comp_def,
      filter_const_true, List.filter_append, List.filter_map, Diagram.marksWhere]
  · simp [twoLine, twoLineEntryMarks, twoLineBar, Part.isDecoration, Function.comp_def,
      filter_const_false, List.filter_append, List.filter_map, Diagram.marksWhere]
  · simp [twoLine, twoLineEntryMarks, twoLineBar, Part.isEntry, Part.isDecoration]

/-- The centre of cell `(i, j)` of the matrix, row 0 at the top. -/
def matrixCentre (i j : Nat) : QPoint := ((j : Rat) + 1 / 2, -((i : Rat) + 1 / 2))

/-- The grid of the permutation matrix: the `n × n` unit squares, row by row (guides). -/
def matrixGrid (σ : FinPerm) : List Mark :=
  (List.range σ.n).flatMap fun (i : Nat) => (List.range σ.n).map fun (j : Nat) =>
    ({ part := .guide, shape := .rect ((j : Rat), -((i : Rat) + 1)) ((j : Rat) + 1, -(i : Rat)),
       ink := .faint } : Mark)

/-- The dots of the permutation matrix: one at the centre of cell `(i, σ i)` for each `i` (part
`cell i (σ i)`), in the ink. -/
def matrixDots (σ : FinPerm) : List Mark :=
  (List.range σ.n).map fun i =>
    { part := .cell i (σ.apply i), shape := .dot (matrixCentre i (σ.apply i)) }

/-- The permutation matrix: the grid (`matrixGrid`), then the dots (`matrixDots`). -/
def matrix (σ : FinPerm) : Diagram where
  marks := σ.matrixGrid ++ σ.matrixDots
  width := 28 * σ.n.toFloat + 24

/-- The matrix is faithful: its marked cells are `(i, σ i)`, in order of `i`, each a dot at its
cell's centre; its marks of cells are exactly `matrixDots` and its decorations exactly the grid
(`matrixGrid`), with their colour roles; and it has no mark of any other part. -/
def FaithfulMatrix (σ : FinPerm) (d : Diagram) : Prop :=
  d.cells = (List.range σ.n).map (fun i => (i, σ.apply i)) ∧
    d.marks.all (fun m => match m.part, m.shape with
      | .cell i j, .dot p => p == matrixCentre i j
      | .guide, .rect _ _ => true
      | _, _ => false) = true ∧
    d.marksWhere Part.isCell = σ.matrixDots ∧ d.marksWhere Part.isDecoration = σ.matrixGrid

instance (σ : FinPerm) (d : Diagram) : Decidable (σ.FaithfulMatrix d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The permutation matrix marks exactly the cells `(i, σ i)`. -/
theorem matrix_faithful (σ : FinPerm) : σ.FaithfulMatrix σ.matrix := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Diagram.cells, matrix, matrixGrid, matrixDots, List.filterMap_append,
      List.filterMap_map, List.filterMap_flatMap, Function.comp_def]
  · simp [matrix, matrixGrid, matrixDots]
  · simp [matrix, matrixGrid, matrixDots, Part.isCell, List.filter_flatMap, Function.comp_def,
      filter_const_true, filter_const_false, List.filter_append, List.filter_map,
      Diagram.marksWhere]
  · simp [matrix, matrixGrid, matrixDots, Part.isDecoration, List.filter_flatMap,
      Function.comp_def, filter_const_true, filter_const_false, List.filter_append,
      List.filter_map, Diagram.marksWhere]

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
theorem cycles_faithful (σ : FinPerm) : σ.FaithfulCycles σ.cycles :=
  σ.toFinGraph.draw_faithful _

/-- A pair is an arrow of the cycle diagram exactly when `i < n` and `j = σ i < n`. -/
theorem mem_cycles_edges (σ : FinPerm) (i j : Nat) :
    (i, j) ∈ σ.cycles.edges ↔ i < σ.n ∧ j < σ.n ∧ σ.apply i = j := by
  rw [(σ.cycles_faithful).1, FinGraph.mem_edgePairs]
  simp [toFinGraph, FinGraph.drawn]
  constructor
  · rintro ⟨hj, hi, h⟩
    exact ⟨hi, hj, h⟩
  · rintro ⟨hi, hj, h⟩
    exact ⟨hj, hi, h⟩

/-- The strand of `i`: from `(i, 2)` to `(σ i, 0)`. -/
def strand (σ : FinPerm) (i : Nat) : Nat × QPoint × QPoint :=
  (i, ((i : Rat), 2), ((σ.apply i : Rat), 0))

/-- The top and bottom lines of the wiring diagram (guides). -/
def wiringLines (σ : FinPerm) : List Mark :=
  [{ part := .guide, shape := .segment (-1 / 2, 2) ((σ.n : Rat) - 1 / 2, 2), ink := .faint },
    { part := .guide, shape := .segment (-1 / 2, 0) ((σ.n : Rat) - 1 / 2, 0), ink := .faint }]

/-- The strands of the wiring diagram: strand `i` as the segment `strand i`, in accent `i % 3`. -/
def strandMarks (σ : FinPerm) : List Mark :=
  (List.range σ.n).map fun i =>
    let (_, p, q) := σ.strand i
    { part := .strand i, shape := .segment p q, ink := .accent (i % 3) }

/-- The labels of the wiring diagram: the positions above the top line (entries `(0, i)`), then
below the bottom one (entries `(1, i)`). -/
def wiringLabels (σ : FinPerm) : List Mark :=
  (List.range σ.n).map (fun i =>
      { part := .entry 0 i, shape := .text (σ.text i) ((i : Rat), 2) .above }) ++
    (List.range σ.n).map (fun i =>
      { part := .entry 1 i, shape := .text (σ.text i) ((i : Rat), 0) .below })

/-- The wiring diagram: the top and bottom lines (`wiringLines`), then the strands
(`strandMarks`), then the positions above and below (`wiringLabels`). -/
def wiring (σ : FinPerm) : Diagram where
  marks := σ.wiringLines ++ σ.strandMarks ++ σ.wiringLabels
  width := 40 * σ.n.toFloat + 24

/-- The wiring diagram is faithful: its strands are `strand 0, …, strand (n - 1)`, in order; its
texts are the positions `1, …, n` above the top line and below the bottom one; its marks of
strands, of entries and of decorations are exactly `strandMarks`, `wiringLabels` and the two
lines (`wiringLines`), with their colour roles; and it has no mark of any other part. -/
def FaithfulWiring (σ : FinPerm) (d : Diagram) : Prop :=
  d.strands = (List.range σ.n).map σ.strand ∧
    d.texts = (List.range σ.n).map (fun i => (.entry 0 i, σ.text i, ((i : Rat), 2))) ++
      (List.range σ.n).map (fun i => (.entry 1 i, σ.text i, ((i : Rat), 0))) ∧
    d.marksWhere Part.isStrand = σ.strandMarks ∧ d.marksWhere Part.isEntry = σ.wiringLabels ∧
    d.marksWhere Part.isDecoration = σ.wiringLines ∧
    d.marks.all (fun m => m.part.isStrand || m.part.isEntry || m.part.isDecoration) = true

instance (σ : FinPerm) (d : Diagram) : Decidable (σ.FaithfulWiring d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The wiring diagram draws the strands. -/
theorem wiring_faithful (σ : FinPerm) : σ.FaithfulWiring σ.wiring := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Diagram.strands, wiring, wiringLines, strandMarks, wiringLabels, strand,
      List.filterMap_map, List.filterMap_append, Function.comp_def]
  · simp [Diagram.texts, wiring, wiringLines, strandMarks, wiringLabels, strand,
      List.filterMap_map, List.filterMap_append, Function.comp_def]
  · simp [wiring, wiringLines, strandMarks, wiringLabels, strand, Part.isStrand,
      Function.comp_def, filter_const_true, filter_const_false, List.filter_append,
      List.filter_map, Diagram.marksWhere]
  · simp [wiring, wiringLines, strandMarks, wiringLabels, strand, Part.isEntry,
      Function.comp_def, filter_const_true, filter_const_false, List.filter_append,
      List.filter_map, Diagram.marksWhere]
  · simp [wiring, wiringLines, strandMarks, wiringLabels, strand, Part.isDecoration,
      Function.comp_def, filter_const_false, List.filter_append,
      List.filter_map, Diagram.marksWhere]
  · simp [wiring, wiringLines, strandMarks, wiringLabels, strand, Part.isStrand, Part.isEntry,
      Part.isDecoration]

/-- The pairs of strands of the wiring diagram that cross are exactly the inversions, in
order. -/
theorem wiring_crossings (σ : FinPerm) : crossingPairs σ.wiring.strands = σ.inversions := by
  rw [σ.wiring_faithful.1]
  simp only [crossingPairs, inversions, strand, List.flatMap_map, List.filterMap_map,
    Function.comp_def, Rat.natCast_lt_natCast]

/-- Whether the permutation is within the figures' cap (`maxSize`). -/
def small (σ : FinPerm) : Bool := σ.values.length ≤ maxSize

/-- The figure of one of the drawings `draw` (`oneLine`, `twoLine`, `matrix`, `cycles`, `wiring`),
or a note for more than `maxSize` values (the matrix and the crossings take `n²` steps). -/
def figure (σ : FinPerm) (draw : FinPerm → Diagram) : Diagram :=
  Diagram.capped σ.small s!"{σ.n} values: too many to draw" fun _ => draw σ

/-- Within the cap, the figure is the drawing itself, so its faithfulness theorem applies. -/
theorem figure_eq (σ : FinPerm) (draw : FinPerm → Diagram) (h : σ.small = true) :
    σ.figure draw = draw σ :=
  Diagram.capped_of h _ _

/-- The wiring diagram has as many crossings as the permutation has inversions. -/
theorem wiring_crossings_length (σ : FinPerm) :
    (crossingPairs σ.wiring.strands).length = σ.inversions.length := by
  rw [σ.wiring_crossings]

end FinPerm

/-- The hypotheses can be met: `[2, 0, 1]` is a permutation with the inversions `(0, 1)` and
`(0, 2)`. -/
example : (FinPerm.mk [2, 0, 1] 1).IsPerm ∧
    (FinPerm.mk [2, 0, 1] 1).inversions = [(0, 1), (0, 2)] := by decide

end PILean.Diagram
