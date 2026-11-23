/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Diagram.Basic

/-!
# Young diagrams and tableaux

A Young diagram is given by its row lengths `λ = [λ₀, λ₁, …]` (a partition when they are
positive and weakly decreasing, which the drawing does not require). Cell `(i, j)`, row `i` and
column `j`, is drawn exactly when `j < λᵢ`. In English notation row 0 is at the top and rows go
down; in French notation row 0 is at the bottom and rows go up; columns go right in both. Each
cell is the unit square `[j, j + 1] × [-(i + 1), -i]` (English) or `[j, j + 1] × [i, i + 1]`
(French).

A tableau is a filling: row `i` is the list of its entries, so its shape is the list of the rows'
lengths, and the entry of cell `(i, j)` is written at the cell's centre.

## Main definitions

* `Convention`, `cellBox`, `cellList`
* `YoungDiagram'`: a shape and a convention; `Tableau`: a filling and a convention
* `Tableau.IsSemistandard`, `Tableau.IsStandard` (decidable)
* `draw`, `figure`, `Faithful` for both

## Main results

* `mem_cellList`: `(i, j)` is a cell exactly when `j < λᵢ`.
* `YoungDiagram'.draw_faithful`, `Tableau.draw_faithful`: the drawn cells are exactly
  `cellList λ`, in order, each the unit square of its convention; a tableau's entries are its
  filling, cell by cell.
-/

namespace PILean.Diagram

/-- How a Young diagram is laid out: English (row 0 at the top) or French (row 0 at the
bottom). -/
inductive Convention where
  /-- Row 0 at the top, rows going down. -/
  | english
  /-- Row 0 at the bottom, rows going up. -/
  | french
  deriving DecidableEq, Repr, Inhabited

/-- The unit square of cell `(i, j)` in a convention, as its lower-left and upper-right
corners. -/
def cellBox : Convention → Nat → Nat → QPoint × QPoint
  | .english, i, j => (((j : Rat), -((i : Rat) + 1)), ((j : Rat) + 1, -(i : Rat)))
  | .french, i, j => (((j : Rat), (i : Rat)), ((j : Rat) + 1, (i : Rat) + 1))

/-- The centre of the cell `(i, j)` in a convention. -/
def cellCentre (c : Convention) (i j : Nat) : QPoint :=
  let (lo, hi) := cellBox c i j
  ((lo.1 + hi.1) / 2, (lo.2 + hi.2) / 2)

/-- The cells of the shape `λ`, row by row and left to right. -/
def cellList (rows : List Nat) : List (Nat × Nat) :=
  (List.range rows.length).flatMap fun i => (List.range (rows.getD i 0)).map fun j => (i, j)

/-- `(i, j)` is a cell of `λ` exactly when row `i` exists and `j < λᵢ`. -/
theorem mem_cellList (rows : List Nat) (i j : Nat) :
    (i, j) ∈ cellList rows ↔ ∃ h : i < rows.length, j < rows[i] := by
  simp only [cellList, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi, j', hj, rfl, rfl⟩
    exact ⟨hi, by simpa [List.getD_eq_getElem?_getD, hi] using hj⟩
  · rintro ⟨hi, hj⟩
    exact ⟨i, hi, j, by simpa [List.getD_eq_getElem?_getD, hi] using hj, rfl, rfl⟩

/-- Each cell is listed once. -/
theorem cellList_nodup (rows : List Nat) : (cellList rows).Nodup := by
  unfold cellList
  rw [List.nodup_iff_pairwise_ne, List.pairwise_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp fun h h' => by simp only [Prod.mk.injEq] at h'; omega
  · refine List.pairwise_lt_range.imp fun {i i'} hlt => ?_
    intro p hp p' hp'
    simp only [List.mem_map] at hp hp'
    obtain ⟨j, _, rfl⟩ := hp
    obtain ⟨j', _, rfl⟩ := hp'
    intro h
    simp only [Prod.mk.injEq] at h
    omega

/-- The most cells `figure` draws. -/
def maxCells : Nat := 4096

/-- The mark of a cell in a convention: its unit square, in the ink `k`. -/
def cellMark (c : Convention) (k : Ink) (e : Nat × Nat) : Mark :=
  { part := .cell e.1 e.2, shape := .rect (cellBox c e.1 e.2).1 (cellBox c e.1 e.2).2, ink := k }

/-- Whether a mark is placed by the convention: a cell's rectangle is its unit square, an entry's
text is at its cell's centre. A mark of any other part is refused. -/
def placedCell (c : Convention) (m : Mark) : Bool :=
  match m.part, m.shape with
  | .cell i j, .rect lo hi => lo == (cellBox c i j).1 && hi == (cellBox c i j).2
  | .cell _ _, _ => false
  | .entry i j, .text _ p _ => p == cellCentre c i j
  | .entry _ _, _ => false
  | _, _ => false

/-- A Young diagram to draw: its row lengths and its convention. (Mathlib's `YoungDiagram`, a
lower set of cells, is bound to it in the package `pilean-mathlib`.) -/
structure YoungShape where
  /-- The row lengths `λ₀, λ₁, …`. -/
  rows : List Nat
  /-- English or French. -/
  convention : Convention := .english

namespace YoungShape

/-- The diagram: one unit square per cell, row by row, tinted with accent 0. -/
def draw (Y : YoungShape) : Diagram where
  marks := (cellList Y.rows).map (cellMark Y.convention (.tint 0))

/-- The diagram draws the shape faithfully: its cells are exactly `cellList λ`, in order, and
each is the unit square of its convention. -/
def Faithful (Y : YoungShape) (d : Diagram) : Prop :=
  d.cells = cellList Y.rows ∧ d.marks.all (placedCell Y.convention) = true

instance (Y : YoungShape) (d : Diagram) : Decidable (Y.Faithful d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The diagram of a shape is faithful. -/
theorem draw_faithful (Y : YoungShape) : Y.Faithful Y.draw := by
  refine ⟨?_, ?_⟩
  · simp [Diagram.cells, draw, cellMark, List.filterMap_map, Function.comp_def]
  · simp [draw, placedCell, cellMark]

/-- The figure: the diagram, or a note when the shape has more than `maxCells` cells (counted
up to the cap). -/
def figure (Y : YoungShape) : Diagram :=
  if Y.rows.foldl (fun s r => min (s + r) (maxCells + 1)) 0 ≤ maxCells then Y.draw
  else { marks := [{ part := .note 0, shape := .text "too many cells to draw" (0, 0) .center }] }

/-- A shape the figure draws is drawn faithfully. -/
theorem builder_faithful (Y : YoungShape)
    (h : Y.rows.foldl (fun s r => min (s + r) (maxCells + 1)) 0 ≤ maxCells) :
    Y.Faithful Y.figure := by
  unfold figure
  split
  · exact Y.draw_faithful
  · contradiction

end YoungShape

/-- A tableau: its rows of entries (so its shape is the list of their lengths) and a convention.
-/
structure Tableau where
  /-- The entries, row by row. -/
  entries : List (List Nat)
  /-- English or French. -/
  convention : Convention := .english

namespace Tableau

/-- The shape: the lengths of the rows. -/
def shape (T : Tableau) : List Nat := T.entries.map List.length

/-- The entry of cell `(i, j)` (0 outside the shape). -/
def entry (T : Tableau) (i j : Nat) : Nat := (T.entries.getD i []).getD j 0

/-- The entries as the diagram writes them: `((i, j), T(i, j))` for each cell, in order. -/
def entryTexts (T : Tableau) : List ((Nat × Nat) × String) :=
  (cellList T.shape).map fun (i, j) => ((i, j), toString (T.entry i j))

/-- Whether the rows weakly increase and the columns strictly increase (and the shape is a
partition: its rows weakly decrease). -/
def IsSemistandard (T : Tableau) : Prop :=
  (T.shape.zip T.shape.tail).all (fun (a, b) => b ≤ a) = true ∧
  (cellList T.shape).all (fun (i, j) =>
    (j + 1 < T.shape.getD i 0 → T.entry i j ≤ T.entry i (j + 1)) &&
    (j < T.shape.getD (i + 1) 0 → T.entry i j < T.entry (i + 1) j)) = true

instance (T : Tableau) : Decidable T.IsSemistandard :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Whether the tableau is standard: semistandard with entries `1, …, n`, each once, for its `n`
cells (each of `1, …, n` occurs exactly once among the `n` entries). -/
def IsStandard (T : Tableau) : Prop :=
  T.IsSemistandard ∧ (List.range (cellList T.shape).length).all (fun k =>
    ((cellList T.shape).map fun (i, j) => T.entry i j).count (k + 1) == 1) = true

instance (T : Tableau) : Decidable T.IsStandard :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The diagram: the unit square of each cell, then its entry at its centre. -/
def draw (T : Tableau) : Diagram where
  marks := (cellList T.shape).map (cellMark T.convention .ink) ++
    T.entryTexts.map fun e =>
      { part := .entry e.1.1 e.1.2,
        shape := .text e.2 (cellCentre T.convention e.1.1 e.1.2) .center }

/-- The diagram draws the tableau faithfully: its cells are exactly the cells of its shape, in
order, its written entries are the filling (`entryTexts`), cell by cell, and each mark is where
the convention puts it. -/
def Faithful (T : Tableau) (d : Diagram) : Prop :=
  d.cells = cellList T.shape ∧ d.entries = T.entryTexts ∧
    d.marks.all (placedCell T.convention) = true

instance (T : Tableau) (d : Diagram) : Decidable (T.Faithful d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The diagram of a tableau is faithful. -/
theorem draw_faithful (T : Tableau) : T.Faithful T.draw := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Diagram.cells, draw, cellMark, List.filterMap_append, List.filterMap_map,
      Function.comp_def]
  · simp [Diagram.entries, draw, cellMark, List.filterMap_append, List.filterMap_map,
      Function.comp_def]
  · simp [draw, placedCell, cellMark]

/-- The figure: the diagram, or a note for more than `maxCells` cells. -/
def figure (T : Tableau) : Diagram :=
  if T.entries.foldl (fun s r => min (s + r.length) (maxCells + 1)) 0 ≤ maxCells then T.draw
  else { marks := [{ part := .note 0, shape := .text "too many cells to draw" (0, 0) .center }] }

/-- A tableau the figure draws is drawn faithfully. -/
theorem builder_faithful (T : Tableau)
    (h : T.entries.foldl (fun s r => min (s + r.length) (maxCells + 1)) 0 ≤ maxCells) :
    T.Faithful T.figure := by
  unfold figure
  split
  · exact T.draw_faithful
  · contradiction

end Tableau

/-- The hypotheses can be met: the shape `(2, 1)` has the cells `(0, 0)`, `(0, 1)`, `(1, 0)`, and
the tableau `[[1, 2], [3]]` is standard. -/
example : cellList [2, 1] = [(0, 0), (0, 1), (1, 0)] ∧
    (Tableau.mk [[1, 2], [3]] .english).IsStandard := by decide

end PILean.Diagram
