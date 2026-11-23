/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Diagram.Basic

/-!
# Lattice paths, Dyck paths and polyominoes

A `LatticePath` is a list of integer steps from the origin; its `k`-th point is the sum of its
first `k` steps, and step `k` is drawn as the segment from point `k` to point `k + 1`, over the
unit grid of the box that holds the path. A north–east path has the steps `(1, 0)` and `(0, 1)`
(`LatticePath.ofNorthEast`); a Dyck path the steps `(1, 1)` and `(1, -1)` (`LatticePath.ofDyck`,
`true` for an up step).

A `Polyomino` is a list of cells `(x, y)`, each drawn as the unit square `[x, x + 1] × [y, y + 1]`;
the Ferrers board of a partition is the polyomino of its cells, rows going up.

## Main definitions

* `LatticePath`, `LatticePath.point`, `LatticePath.stepList`, `LatticePath.draw`,
  `LatticePath.Faithful`, `LatticePath.ofNorthEast`, `LatticePath.ofDyck`, `LatticePath.isDyck`
* `Polyomino`, `Polyomino.draw`, `Polyomino.Faithful`, `Polyomino.ferrers`

## Main results

* `LatticePath.draw_faithful`: the drawn steps are exactly `stepList`, in order.
* `LatticePath.point_succ`: point `k + 1` is point `k` plus step `k`, so a drawn step's vector is
  the path's step.
* `Polyomino.draw_faithful`: the drawn cells are exactly the polyomino's, in order, each its unit
  square.
-/

namespace PILean.Diagram

/-- The exact point of a pair of integers. -/
def ofInts (p : Int × Int) : QPoint := ((p.1 : Rat), (p.2 : Rat))

/-- A path in the integer lattice from the origin: its steps. -/
structure LatticePath where
  /-- The steps, as integer vectors. -/
  steps : List (Int × Int)

namespace LatticePath

/-- The most steps `figure` draws. -/
def maxSteps : Nat := 1024

/-- Point `k`: the sum of the first `k` steps. -/
def point (P : LatticePath) (k : Nat) : Int × Int :=
  (P.steps.take k).foldl (fun a s => (a.1 + s.1, a.2 + s.2)) (0, 0)

/-- Point `k + 1` is point `k` plus step `k`. -/
theorem point_succ (P : LatticePath) (k : Nat) (h : k < P.steps.length) :
    P.point (k + 1) = ((P.point k).1 + P.steps[k].1, (P.point k).2 + P.steps[k].2) := by
  rw [point, List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.foldl_append]
  rfl

/-- The steps as the diagram draws them: `(k, point k, point (k + 1))` for each step `k`. -/
def stepList (P : LatticePath) : List (Nat × QPoint × QPoint) :=
  (List.range P.steps.length).map fun k => (k, ofInts (P.point k), ofInts (P.point (k + 1)))

/-- The box of the path's points, `(xmin, ymin, xmax, ymax)`. -/
def box (P : LatticePath) : Int × Int × Int × Int :=
  let ps := (List.range (P.steps.length + 1)).map P.point
  (ps.foldl (fun m p => min m p.1) 0, ps.foldl (fun m p => min m p.2) 0,
    ps.foldl (fun m p => max m p.1) 0, ps.foldl (fun m p => max m p.2) 0)

/-- The grid lines of the box (guides): vertical, then horizontal. -/
def gridMarks (P : LatticePath) : List Mark :=
  let (x0, y0, x1, y1) := P.box
  ((List.range (x1 - x0 + 1).toNat).map fun (i : Nat) =>
      ({ part := .guide, ink := .faint,
         shape := .segment ((x0 : Rat) + i, (y0 : Rat)) ((x0 : Rat) + i, (y1 : Rat)) } : Mark)) ++
    (List.range (y1 - y0 + 1).toNat).map fun (j : Nat) =>
      { part := .guide, ink := .faint,
        shape := .segment ((x0 : Rat), (y0 : Rat) + j) ((x1 : Rat), (y0 : Rat) + j) }

/-- The diagram: the grid, then each step as a segment in accent 0. -/
def draw (P : LatticePath) : Diagram where
  marks := P.gridMarks ++
    P.stepList.map (fun (k, p, q) =>
      { part := .step k, shape := .segment p q, ink := .accent 0 })
  width := min 520 (36 * ((P.box.2.2.1 - P.box.1).toNat.toFloat + 1) + 24)

/-- The diagram draws the path faithfully: its steps are exactly `stepList`, in order. -/
def Faithful (P : LatticePath) (d : Diagram) : Prop := d.steps = P.stepList

instance (P : LatticePath) (d : Diagram) : Decidable (P.Faithful d) :=
  inferInstanceAs (Decidable (_ = _))

/-- The diagram of a path is faithful. -/
theorem draw_faithful (P : LatticePath) : P.Faithful P.draw := by
  simp [Faithful, Diagram.steps, draw, gridMarks, stepList, List.filterMap_append,
    List.filterMap_map, Function.comp_def]

/-- The figure: the diagram, or a note for more than `maxSteps` steps or a box wider or taller
than `maxSteps` (the grid's lines). -/
def figure (P : LatticePath) : Diagram :=
  if P.steps.length ≤ maxSteps ∧ P.steps.all (fun s => s.1.natAbs ≤ 4 ∧ s.2.natAbs ≤ 4) then P.draw
  else { marks := [{ part := .note 0, shape := .text "too many steps to draw" (0, 0) .center }] }

/-- A path the figure draws is drawn faithfully. -/
theorem builder_faithful (P : LatticePath)
    (h : P.steps.length ≤ maxSteps ∧ P.steps.all (fun s => s.1.natAbs ≤ 4 ∧ s.2.natAbs ≤ 4)) :
    P.Faithful P.figure := by
  unfold figure
  split
  · exact P.draw_faithful
  · contradiction

/-- The north–east path of a word: `true` a step north `(0, 1)`, `false` a step east `(1, 0)`. -/
def ofNorthEast (w : List Bool) : LatticePath :=
  ⟨w.map fun b => if b then (0, 1) else (1, 0)⟩

/-- The Dyck path of a word: `true` an up step `(1, 1)`, `false` a down step `(1, -1)`. -/
def ofDyck (w : List Bool) : LatticePath :=
  ⟨w.map fun b => if b then (1, 1) else (1, -1)⟩

/-- Whether a word of up (`true`) and down steps is a Dyck word: no prefix has more downs than
ups, and the whole has as many of each. -/
def isDyck (w : List Bool) : Bool :=
  (List.range (w.length + 1)).all (fun k =>
    ((w.take k).count false ≤ (w.take k).count true)) && w.count false == w.count true

/-- Step `k` of a Dyck path is drawn rising (from height `y` to `y + 1`) exactly when letter `k`
of the word is an up step. -/
theorem ofDyck_step_rises (w : List Bool) (k : Nat) (h : k < w.length) :
    ((ofDyck w).point (k + 1)).2 = ((ofDyck w).point k).2 + 1 ↔ w[k] = true := by
  rw [point_succ _ _ (by simpa [ofDyck] using h)]
  simp only [ofDyck, List.getElem_map]
  cases w[k] <;> simp <;> omega

end LatticePath

/-- A polyomino (or any finite set of cells): its cells `(x, y)`, column `x` and row `y`, rows
going up. -/
structure Polyomino where
  /-- The cells. -/
  cells : List (Nat × Nat)

namespace Polyomino

/-- The unit square of cell `(x, y)`: lower-left corner `(x, y)`, upper-right `(x + 1, y + 1)`. -/
def square (c : Nat × Nat) : QPoint × QPoint :=
  (((c.1 : Rat), (c.2 : Rat)), ((c.1 : Rat) + 1, (c.2 : Rat) + 1))

/-- The diagram: each cell's unit square, tinted with accent 1. -/
def draw (P : Polyomino) : Diagram where
  marks := P.cells.map fun c =>
    { part := .cell c.1 c.2, shape := .rect (square c).1 (square c).2, ink := .tint 1 }
  width := min 520 (36 * ((P.cells.foldl (fun m c => max m c.1) 0) + 1).toFloat + 24)

/-- The diagram draws the polyomino faithfully: its cells are exactly the polyomino's, in order,
each its unit square. -/
def Faithful (P : Polyomino) (d : Diagram) : Prop :=
  d.cells = P.cells ∧ d.marks.all (fun m => match m.part, m.shape with
    | .cell x y, .rect lo hi => lo == (square (x, y)).1 && hi == (square (x, y)).2
    | .cell _ _, _ => false
    | _, _ => true) = true

instance (P : Polyomino) (d : Diagram) : Decidable (P.Faithful d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The diagram of a polyomino is faithful. -/
theorem draw_faithful (P : Polyomino) : P.Faithful P.draw := by
  refine ⟨?_, ?_⟩
  · simp [Diagram.cells, draw, List.filterMap_map, Function.comp_def]
  · simp [draw]

/-- The Ferrers board of the row lengths `λ`: row `i` (from the bottom) has the cells
`(0, i), …, (λᵢ - 1, i)`. -/
def ferrers (rows : List Nat) : Polyomino :=
  ⟨(List.range rows.length).flatMap fun i => (List.range (rows.getD i 0)).map fun j => (j, i)⟩

end Polyomino

/-- The hypotheses can be met: `UUDD` is a Dyck word whose path rises at step 0. -/
example : LatticePath.isDyck [true, true, false, false] = true ∧
    (LatticePath.ofDyck [true, true, false, false]).point 1 = (1, 1) := by decide

end PILean.Diagram
