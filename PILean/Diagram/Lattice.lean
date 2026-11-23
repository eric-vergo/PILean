/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Diagram.Basic

/-!
# Lattices in the plane

A `PlaneLattice` is the lattice `ℤω₁ + ℤω₂` of two rational vectors (a lattice of the complex
plane, `ω₁` and `ω₂` read as complex numbers) with a window, a closed box. It is drawn as a dot at
each lattice point in the window, in accent 1 where a predicate on the coefficients marks it (the
Gaussian primes among the Gaussian integers, say), the fundamental parallelogram
`0, ω₁, ω₁ + ω₂, ω₂`, and the two axes.

The lattice points drawn are `points`: the points `m ω₁ + n ω₂` for the integers `m, n` with
`|m|, |n| ≤ bound` (in that order, `m` first) that lie in the window. `bound` is computed from the
window and the inverse of the matrix of `ω₁, ω₂`, so that every lattice point in the window has
coefficients within it; the package `pilean-mathlib` proves that, so the dots are exactly the
lattice points in the window.

`PlaneLattice.Faithful` accounts for every mark: the dots are exactly `points`, each in the ink of
its mark; the parallelogram and the axes are exactly the builder's; nothing else is drawn.

## Main definitions

* `PlaneLattice`, `PlaneLattice.det`, `PlaneLattice.bound`, `PlaneLattice.candidates`,
  `PlaneLattice.points`, `PlaneLattice.draw`, `PlaneLattice.figure`, `PlaneLattice.Faithful`
* `Diagram.dots`: the dots a diagram draws, with their parts and inks

## Main results

* `PlaneLattice.draw_faithful`, `PlaneLattice.builder_faithful`
* `PlaneLattice.mem_points`: a point is drawn exactly when it is `m ω₁ + n ω₂` for integers with
  `|m|, |n| ≤ bound` and lies in the window.
-/

namespace PILean.Diagram

/-- The dots a diagram draws: `(i, p, ink)` for each mark of the part `vertex i` that is a dot
at `p`, in order. -/
def Diagram.dots (d : Diagram) : List (Nat × QPoint × Ink) :=
  d.marks.filterMap fun m => match m.part, m.shape with
    | .vertex i, .dot p => some (i, p, m.ink)
    | _, _ => none

/-- A lattice of the plane with a window and a marking of its points. -/
structure PlaneLattice where
  /-- The first period. -/
  w1 : QPoint
  /-- The second period. -/
  w2 : QPoint
  /-- The lower left corner of the window. -/
  lo : QPoint
  /-- The upper right corner of the window. -/
  hi : QPoint
  /-- Which points `m ω₁ + n ω₂` are marked, by their coefficients. -/
  marked : Int → Int → Bool := fun _ _ => false
  /-- The ink of the points that are not marked (the faint ink when the marked ones are what the
  figure shows). -/
  plainInk : Ink := .ink

namespace PlaneLattice

/-- The most points a figure considers: `(2 bound + 1)²` at most. -/
def maxCandidates : Nat := 40000

/-- The determinant `ω₁ × ω₂` (zero when the periods are dependent: no lattice). -/
def det (Λ : PlaneLattice) : Rat := Λ.w1.1 * Λ.w2.2 - Λ.w1.2 * Λ.w2.1

/-- The absolute value. -/
def qabs (q : Rat) : Rat := if q < 0 then -q else q

/-- A bound on the coefficients of the lattice points in the window: with `X`, `Y` the largest
absolute coordinates of the window, `m = (x ω₂.y - y ω₂.x) / det` and
`n = (y ω₁.x - x ω₁.y) / det` give `|m| ≤ (|ω₂.y| X + |ω₂.x| Y) / |det|` and likewise `|n|`;
the bound is the larger, rounded up. -/
def bound (Λ : PlaneLattice) : Nat :=
  let X := max (qabs Λ.lo.1) (qabs Λ.hi.1)
  let Y := max (qabs Λ.lo.2) (qabs Λ.hi.2)
  let d := qabs Λ.det
  if d = 0 then 0 else
    let bm := (qabs Λ.w2.2 * X + qabs Λ.w2.1 * Y) / d
    let bn := (qabs Λ.w1.1 * Y + qabs Λ.w1.2 * X) / d
    (max bm bn).ceil.toNat

/-- The point `m ω₁ + n ω₂`. -/
def at_ (Λ : PlaneLattice) (m n : Int) : QPoint :=
  (m * Λ.w1.1 + n * Λ.w2.1, m * Λ.w1.2 + n * Λ.w2.2)

/-- Whether a point lies in the window (closed). -/
def inWindow (Λ : PlaneLattice) (p : QPoint) : Bool :=
  decide (Λ.lo.1 ≤ p.1) && decide (p.1 ≤ Λ.hi.1) && decide (Λ.lo.2 ≤ p.2) && decide (p.2 ≤ Λ.hi.2)

/-- The coefficients `(m, n)` with `|m|, |n| ≤ bound`, `m` first. -/
def candidates (Λ : PlaneLattice) : List (Int × Int) :=
  let b := (Λ.bound : Int)
  let r := (List.range (2 * Λ.bound + 1)).map fun (i : Nat) => (i : Int) - b
  r.flatMap fun m => r.map fun n => (m, n)

/-- The coefficients of the drawn points: the candidates whose point is in the window. -/
def points (Λ : PlaneLattice) : List (Int × Int) :=
  Λ.candidates.filter fun (m, n) => Λ.inWindow (Λ.at_ m n)

/-- The ink of the point `m ω₁ + n ω₂`: accent 1 when marked, `plainInk` otherwise. -/
def pointInk (Λ : PlaneLattice) (m n : Int) : Ink := if Λ.marked m n then .accent 1 else Λ.plainInk

/-- The marks of the points: the `i`-th drawn point is a dot at its exact position in its ink
(`pointInk`). -/
def pointMarks (Λ : PlaneLattice) : List Mark :=
  Λ.points.zipIdx.map fun ((m, n), i) =>
    { part := .vertex i, shape := .dot (Λ.at_ m n), ink := Λ.pointInk m n }

/-- The decorations with their inks: the real axis (`axis 0`) and the imaginary axis (`axis 1`)
across the window, faint, and the fundamental parallelogram `0, ω₁, ω₁ + ω₂, ω₂` (`note 0`) in
accent 0. -/
def decorations (Λ : PlaneLattice) : List (Part × Shape × Ink) :=
  let o : QPoint := (0, 0)
  let w12 : QPoint := (Λ.w1.1 + Λ.w2.1, Λ.w1.2 + Λ.w2.2)
  [(.axis 0, .segment (Λ.lo.1, 0) (Λ.hi.1, 0), .faint),
    (.axis 1, .segment (0, Λ.lo.2) (0, Λ.hi.2), .faint),
    (.note 0, .polyline [o, Λ.w1, w12, Λ.w2, o], .accent 0)]

/-- The marks of the decorations. -/
def decorationMarks (Λ : PlaneLattice) : List Mark :=
  Λ.decorations.map fun (p, s, i) => { part := p, shape := s, ink := i }

/-- The diagram: the decorations, then the points. -/
def draw (Λ : PlaneLattice) : Diagram where
  marks := Λ.decorationMarks ++ Λ.pointMarks

/-- The diagram draws the lattice faithfully: its dots are exactly the drawn points, at their
exact positions, each in accent 1 exactly when marked (`Diagram.dots`); its decorations are
exactly the axes and the parallelogram; there is nothing else. -/
def Faithful (Λ : PlaneLattice) (d : Diagram) : Prop :=
  d.dots = Λ.points.zipIdx.map (fun ((m, n), i) => (i, Λ.at_ m n, Λ.pointInk m n)) ∧
    d.marksWhere Part.isVertex = Λ.pointMarks ∧
    d.marksWhere Part.isDecoration = Λ.decorationMarks ∧
    d.marks.all (fun m => m.part.isVertex || m.part.isDecoration) = true

instance (Λ : PlaneLattice) (d : Diagram) : Decidable (Λ.Faithful d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Every mark of the points is a vertex's. -/
theorem isVertex_of_mem_pointMarks {Λ : PlaneLattice} {m : Mark} (h : m ∈ Λ.pointMarks) :
    ∃ i, m.part = .vertex i := by
  simp only [pointMarks, List.mem_map] at h
  obtain ⟨_, -, rfl⟩ := h
  exact ⟨_, rfl⟩

/-- Every mark of the decorations is an axis or a note. -/
theorem isDecoration_of_mem_decorationMarks {Λ : PlaneLattice} {m : Mark}
    (h : m ∈ Λ.decorationMarks) : m.part = .axis 0 ∨ m.part = .axis 1 ∨ m.part = .note 0 := by
  simp only [decorationMarks, decorations, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> simp

/-- The lattice is drawn faithfully. -/
theorem draw_faithful (Λ : PlaneLattice) : Λ.Faithful Λ.draw := by
  have hP := @isVertex_of_mem_pointMarks Λ
  have hD := @isDecoration_of_mem_decorationMarks Λ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Diagram.dots, draw, List.filterMap_append]
    rw [(List.filterMap_eq_nil_iff (l := Λ.decorationMarks)).2 fun m hm => by
      rcases hD hm with h | h | h <;> simp [h]]
    simp [pointMarks, List.filterMap_map, Function.comp_def]
  · simp only [Diagram.marksWhere, draw, List.filter_append]
    rw [(List.filter_eq_nil_iff (l := Λ.decorationMarks)).2 fun m hm => by
        rcases hD hm with h | h | h <;> simp [h, Part.isVertex],
      (List.filter_eq_self (l := Λ.pointMarks)).2 fun m hm => by
        obtain ⟨i, h⟩ := hP hm; simp [h, Part.isVertex]]
    simp
  · simp only [Diagram.marksWhere, draw, List.filter_append]
    rw [(List.filter_eq_self (l := Λ.decorationMarks)).2 fun m hm => by
        rcases hD hm with h | h | h <;> simp [h, Part.isDecoration],
      (List.filter_eq_nil_iff (l := Λ.pointMarks)).2 fun m hm => by
        obtain ⟨i, h⟩ := hP hm; simp [h, Part.isDecoration]]
    simp
  · simp only [draw, List.all_append, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true]
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · rcases hD hm with h | h | h <;> simp [h, Part.isDecoration]
    · obtain ⟨i, h⟩ := hP hm; simp [h, Part.isVertex]

/-- A pair of coefficients is drawn exactly when both are within `bound` and its point is in
the window. -/
theorem mem_points (Λ : PlaneLattice) (m n : Int) :
    (m, n) ∈ Λ.points ↔ m.natAbs ≤ Λ.bound ∧ n.natAbs ≤ Λ.bound ∧ Λ.inWindow (Λ.at_ m n) = true := by
  have hr : ∀ x : Int, (∃ a, a ∈ List.range (2 * Λ.bound + 1) ∧ (a : Int) - Λ.bound = x) ↔
      x.natAbs ≤ Λ.bound := by
    intro x
    simp only [List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      omega
    · intro hx
      exact ⟨(x + Λ.bound).toNat, by omega, by omega⟩
  simp only [points, candidates, List.mem_filter, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨m', hm', n', hn', rfl, rfl⟩, hw⟩
    exact ⟨(hr _).1 hm', (hr _).1 hn', hw⟩
  · rintro ⟨hm, hn, hw⟩
    exact ⟨⟨m, (hr _).2 hm, n, (hr _).2 hn, rfl, rfl⟩, hw⟩

/-- The diagram, or a note when the periods are dependent or there are more than `maxCandidates`
candidates. -/
def figure (Λ : PlaneLattice) : Diagram :=
  Diagram.capped (Λ.det ≠ 0 && (2 * Λ.bound + 1) * (2 * Λ.bound + 1) ≤ maxCandidates)
    "dependent periods, or too many points to draw" fun _ => { Λ.draw with width := 360 }

/-- Within the cap the lattice is drawn faithfully by `figure`. -/
theorem builder_faithful (Λ : PlaneLattice)
    (h : (Λ.det ≠ 0 && (2 * Λ.bound + 1) * (2 * Λ.bound + 1) ≤ maxCandidates) = true) :
    Λ.Faithful Λ.figure := by
  have e : Λ.figure.marks = Λ.draw.marks := by
    simp only [figure, Diagram.capped, h, ite_true]
  have hd := Λ.draw_faithful
  unfold Faithful Diagram.dots Diagram.marksWhere at hd ⊢
  rw [e]
  exact hd

end PlaneLattice

end PILean.Diagram
