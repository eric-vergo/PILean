/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Diagram.Basic

/-!
# Zeros and poles of a rational function

A `RationalPlot` is a rational function `p / q` with `p` and `q` given by their rational
coefficients (constant first), the zeros of `p` and the zeros of `q` (the poles) supplied as
Gaussian rationals `a + b i` (pairs `(a, b)`) with their multiplicities, and a window of the
plane. It is drawn as an open circle at each zero (accent 0) and a cross at each pole (accent 1),
each with its multiplicity written beside it when it is above 1, over the two axes, with the
function's name as the title above the window.

Two decidable statements are made about the data, in exact Gaussian rational arithmetic
(`evalAt`, `derivCoeffs`):

* `RationalPlot.Verified`: every supplied zero `z` of multiplicity `m` is a root of `p` of
  multiplicity exactly `m` (the derivatives of `p` of orders `0, …, m - 1` vanish at `z` and the
  derivative of order `m` does not), likewise every pole for `q`; the zeros are distinct, the
  poles are distinct, and no zero is a pole.
* `RationalPlot.Complete`: the multiplicities of the zeros add up to the degree of `p` and those
  of the poles to the degree of `q`, so that (by the count of roots, `pilean-mathlib`) the marks
  are all the zeros and all the poles.

`RationalPlot.Faithful` accounts for every mark: the circles are the zeros, in order, at their
exact positions; the crosses the poles; the written multiplicities those above 1, each beside its
point; the axes and the title the builder's; nothing else. `pilean-mathlib` states the two
statements for `Polynomial ℚ` over ℂ (`Polynomial.rootMultiplicity`, `Polynomial.roots`).

## Main definitions

* `Diagram.GaussQ`, `evalAt`, `derivCoeffs`, `iterDeriv`, `degreeOf`, `rootOfMultiplicity`.
* `RationalPlot`, `RationalPlot.Verified`, `RationalPlot.Complete`, `RationalPlot.draw`,
  `RationalPlot.figure`, `RationalPlot.Faithful`.

## Main results

* `RationalPlot.draw_faithful`, `RationalPlot.builder_faithful`.
-/

namespace PILean.Diagram

/-- A Gaussian rational `a + b i` as the pair `(a, b)`. -/
abbrev GaussQ := Rat × Rat

namespace GaussQ

/-- The sum. -/
def add (z w : GaussQ) : GaussQ := (z.1 + w.1, z.2 + w.2)

/-- The product: `(a + b i)(c + d i) = (ac - bd) + (ad + bc) i`. -/
def mul (z w : GaussQ) : GaussQ := (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- The number as text: `a`, `b i`, `a + b i` or `a − b i`, with `−` for a minus sign. -/
def text (z : GaussQ) : String :=
  let r := fun (q : Rat) => if q < 0 then "−" ++ toString (-q) else toString q
  if z.2 == 0 then r z.1
  else
    let im := if z.2 == 1 then "i" else if z.2 == -1 then "−i" else r z.2 ++ "i"
    if z.1 == 0 then im
    else r z.1 ++ (if z.2 < 0 then " − " ++ (if z.2 == -1 then "i" else toString (-z.2) ++ "i")
      else " + " ++ (if z.2 == 1 then "i" else toString z.2 ++ "i"))

end GaussQ

/-- The value at `z` of the polynomial with rational coefficients `cs` (constant first), by
Horner's rule in the Gaussian rationals. -/
def evalAt (cs : List Rat) (z : GaussQ) : GaussQ :=
  cs.foldr (fun c acc => GaussQ.add (c, 0) (GaussQ.mul z acc)) (0, 0)

/-- The coefficients of the derivative: `c₁, 2 c₂, 3 c₃, …`. -/
def derivCoeffs (cs : List Rat) : List Rat :=
  (cs.zipIdx.drop 1).map fun (c, i) => c * i

/-- The coefficients of the `k`-th derivative. -/
def iterDeriv : Nat → List Rat → List Rat
  | 0, cs => cs
  | k + 1, cs => iterDeriv k (derivCoeffs cs)

/-- The degree of the polynomial: the largest position of a nonzero coefficient (0 for the zero
polynomial). -/
def degreeOf (cs : List Rat) : Nat :=
  (List.range cs.length).foldr (fun i acc => if cs.getD i 0 != 0 then max i acc else acc) 0

/-- Whether `z` is a root of multiplicity exactly `m ≥ 1` of the polynomial `cs`: its derivatives of
orders `0, …, m - 1` vanish at `z` and that of order `m` does not. -/
def rootOfMultiplicity (cs : List Rat) (z : GaussQ) (m : Nat) : Bool :=
  1 ≤ m && (List.range m).all (fun j => evalAt (iterDeriv j cs) z == (0, 0)) &&
    evalAt (iterDeriv m cs) z != (0, 0)

/-- A rational function with its zeros and poles supplied, and a window. -/
structure RationalPlot where
  /-- The function as the title writes it. -/
  name : String
  /-- The numerator's coefficients, constant first. -/
  num : List Rat
  /-- The denominator's coefficients, constant first. -/
  den : List Rat
  /-- The zeros of the numerator, with their multiplicities. -/
  zeros : List (GaussQ × Nat)
  /-- The zeros of the denominator (the poles), with their multiplicities. -/
  poles : List (GaussQ × Nat)
  /-- The lower left corner of the window. -/
  lo : QPoint
  /-- The upper right corner of the window. -/
  hi : QPoint

namespace RationalPlot

/-- The most zeros and poles a figure draws. -/
def maxPoints : Nat := 200

/-- Every supplied zero is a root of the numerator of its multiplicity, every pole one of the
denominator; the zeros are distinct, the poles are distinct, and no zero is a pole. -/
def Verified (R : RationalPlot) : Bool :=
  R.zeros.all (fun (z, m) => rootOfMultiplicity R.num z m) &&
    R.poles.all (fun (z, m) => rootOfMultiplicity R.den z m) &&
    (R.zeros.map (·.1)).Nodup && (R.poles.map (·.1)).Nodup &&
    R.zeros.all (fun (z, _) => !(R.poles.map (·.1)).contains z)

/-- The numerator and the denominator are not zero, the multiplicities of the zeros add up to the
degree of the numerator and those of the poles to the degree of the denominator. -/
def Complete (R : RationalPlot) : Bool :=
  ((R.zeros.map (·.2)).sum == degreeOf R.num && R.num.any (· != 0)) &&
    ((R.poles.map (·.2)).sum == degreeOf R.den && R.den.any (· != 0))

/-- The radius of a zero's circle and the half width of a pole's cross: a sixtieth of the window's
width. -/
def markSize (R : RationalPlot) : Rat := (R.hi.1 - R.lo.1) / 60

/-- Whether a part is a zero's circle: `datum 0 k`. -/
def isZero : Part → Bool
  | .datum 0 _ => true
  | _ => false

/-- Whether a part is a pole's cross: `datum 1 k`. -/
def isPole : Part → Bool
  | .datum 1 _ => true
  | _ => false

/-- Whether a part is a written multiplicity: `entry 0 k` (of zero `k`) or `entry 1 k`. -/
def isLabel : Part → Bool
  | .entry 0 _ => true
  | .entry 1 _ => true
  | _ => false

/-- The circles of the zeros: zero `k` at `z`, accent 0. -/
def zeroMarks (R : RationalPlot) : List Mark :=
  R.zeros.zipIdx.map fun ((z, _), k) =>
    { part := .datum 0 k, shape := .circle z R.markSize, ink := .accent 0 }

/-- The crosses of the poles: two segments for pole `k` at `z`, accent 1. -/
def poleMarks (R : RationalPlot) : List Mark :=
  let s := R.markSize
  R.poles.zipIdx.flatMap fun ((z, _), k) =>
    [{ part := .datum 1 k, shape := .segment (z.1 - s, z.2 - s) (z.1 + s, z.2 + s),
       ink := .accent 1 },
     { part := .datum 1 k, shape := .segment (z.1 - s, z.2 + s) (z.1 + s, z.2 - s),
       ink := .accent 1 }]

/-- The multiplicities above 1, written above and to the right of their points: `entry 0 k` for
zero `k`, `entry 1 k` for pole `k`. -/
def labelMarks (R : RationalPlot) : List Mark :=
  let s := R.markSize
  let at_ := fun (z : GaussQ) => ((z.1 + s, z.2 + s) : QPoint)
  (R.zeros.zipIdx.filterMap fun ((z, m), k) => if m > 1 then
      some { part := .entry 0 k, shape := .text (toString m) (at_ z) .aboveRight, ink := .accent 0 }
    else none) ++
  (R.poles.zipIdx.filterMap fun ((z, m), k) => if m > 1 then
      some { part := .entry 1 k, shape := .text (toString m) (at_ z) .aboveRight, ink := .accent 1 }
    else none)

/-- The decorations: the real axis (`axis 0`) and the imaginary axis (`axis 1`) across the window,
faint, and the title (`note 0`, the function's name) beginning above the window's upper left
corner. -/
def decorationMarks (R : RationalPlot) : List Mark :=
  [{ part := .axis 0, shape := .segment (R.lo.1, 0) (R.hi.1, 0), ink := .faint },
   { part := .axis 1, shape := .segment (0, R.lo.2) (0, R.hi.2), ink := .faint },
   { part := .note 0, shape := .text R.name (R.lo.1, R.hi.2 + 6 * R.markSize) .right }]

/-- The diagram: the decorations, the zeros, the poles, the multiplicities. -/
def draw (R : RationalPlot) : Diagram where
  marks := R.decorationMarks ++ R.zeroMarks ++ R.poleMarks ++ R.labelMarks
  title := s!"Zeros and poles of {R.name}"

/-- The diagram draws the zeros and poles faithfully: its circles are exactly the zeros' (in
order, at their exact positions), its crosses the poles', its written multiplicities those above
1, its axes and title the builder's, and there is nothing else. -/
def Faithful (R : RationalPlot) (d : Diagram) : Prop :=
  d.marksWhere isZero = R.zeroMarks ∧ d.marksWhere isPole = R.poleMarks ∧
    d.marksWhere isLabel = R.labelMarks ∧ d.marksWhere Part.isDecoration = R.decorationMarks ∧
    d.marks.all (fun m => isZero m.part || isPole m.part || isLabel m.part ||
      m.part.isDecoration) = true

instance (R : RationalPlot) (d : Diagram) : Decidable (R.Faithful d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Every mark of the zeros is a zero's and of no other class. -/
theorem isZero_of_mem_zeroMarks {R : RationalPlot} {m : Mark} (h : m ∈ R.zeroMarks) :
    isZero m.part = true ∧ isPole m.part = false ∧ isLabel m.part = false ∧
      m.part.isDecoration = false := by
  simp only [zeroMarks, List.mem_map] at h
  obtain ⟨_, _, rfl⟩ := h
  simp [isZero, isPole, isLabel, Part.isDecoration]

/-- Every mark of the poles is a pole's and of no other class. -/
theorem isPole_of_mem_poleMarks {R : RationalPlot} {m : Mark} (h : m ∈ R.poleMarks) :
    isZero m.part = false ∧ isPole m.part = true ∧ isLabel m.part = false ∧
      m.part.isDecoration = false := by
  simp only [poleMarks, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨_, _, rfl | rfl⟩ := h <;> simp [isZero, isPole, isLabel, Part.isDecoration]

/-- Every written multiplicity is a label and of no other class. -/
theorem isLabel_of_mem_labelMarks {R : RationalPlot} {m : Mark} (h : m ∈ R.labelMarks) :
    isZero m.part = false ∧ isPole m.part = false ∧ isLabel m.part = true ∧
      m.part.isDecoration = false := by
  simp only [labelMarks, List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> split at h <;> cases h <;>
    simp [isZero, isPole, isLabel, Part.isDecoration]

/-- Every decoration is a decoration and of no other class. -/
theorem isDecoration_of_mem_decorationMarks {R : RationalPlot} {m : Mark}
    (h : m ∈ R.decorationMarks) :
    isZero m.part = false ∧ isPole m.part = false ∧ isLabel m.part = false ∧
      m.part.isDecoration = true := by
  simp only [decorationMarks, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> simp [isZero, isPole, isLabel, Part.isDecoration]

/-- The builder's diagram is faithful. -/
theorem draw_faithful (R : RationalPlot) : R.Faithful R.draw := by
  have hZ := @isZero_of_mem_zeroMarks R
  have hP := @isPole_of_mem_poleMarks R
  have hL := @isLabel_of_mem_labelMarks R
  have hD := @isDecoration_of_mem_decorationMarks R
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Diagram.marksWhere, draw, List.filter_append, List.all_append, Bool.and_eq_true]
  · rw [(List.filter_eq_nil_iff (l := R.decorationMarks)).2 fun m hm => by simp [(hD hm).1],
      (List.filter_eq_self (l := R.zeroMarks)).2 fun m hm => (hZ hm).1,
      (List.filter_eq_nil_iff (l := R.poleMarks)).2 fun m hm => by simp [(hP hm).1],
      (List.filter_eq_nil_iff (l := R.labelMarks)).2 fun m hm => by simp [(hL hm).1]]
    simp
  · rw [(List.filter_eq_nil_iff (l := R.decorationMarks)).2 fun m hm => by simp [(hD hm).2.1],
      (List.filter_eq_nil_iff (l := R.zeroMarks)).2 fun m hm => by simp [(hZ hm).2.1],
      (List.filter_eq_self (l := R.poleMarks)).2 fun m hm => (hP hm).2.1,
      (List.filter_eq_nil_iff (l := R.labelMarks)).2 fun m hm => by simp [(hL hm).2.1]]
    simp
  · rw [(List.filter_eq_nil_iff (l := R.decorationMarks)).2 fun m hm => by simp [(hD hm).2.2.1],
      (List.filter_eq_nil_iff (l := R.zeroMarks)).2 fun m hm => by simp [(hZ hm).2.2.1],
      (List.filter_eq_nil_iff (l := R.poleMarks)).2 fun m hm => by simp [(hP hm).2.2.1],
      (List.filter_eq_self (l := R.labelMarks)).2 fun m hm => (hL hm).2.2.1]
    simp
  · rw [(List.filter_eq_self (l := R.decorationMarks)).2 fun m hm => (hD hm).2.2.2,
      (List.filter_eq_nil_iff (l := R.zeroMarks)).2 fun m hm => by simp [(hZ hm).2.2.2],
      (List.filter_eq_nil_iff (l := R.poleMarks)).2 fun m hm => by simp [(hP hm).2.2.2],
      (List.filter_eq_nil_iff (l := R.labelMarks)).2 fun m hm => by simp [(hL hm).2.2.2]]
    simp
  · simp only [List.all_eq_true, Bool.or_eq_true]
    exact ⟨⟨⟨fun m hm => Or.inr (hD hm).2.2.2, fun m hm => Or.inl (Or.inl (Or.inl (hZ hm).1))⟩,
      fun m hm => Or.inl (Or.inl (Or.inr (hP hm).2.1))⟩,
      fun m hm => Or.inl (Or.inr (hL hm).2.2.1)⟩

/-- The diagram, or a note when there are more than `maxPoints` zeros and poles or the window is
empty. -/
def figure (R : RationalPlot) : Diagram :=
  Diagram.capped (R.zeros.length + R.poles.length ≤ maxPoints && R.lo.1 < R.hi.1 &&
      R.lo.2 < R.hi.2)
    "too many zeros and poles, or an empty window" fun _ => { R.draw with width := 360 }

/-- Within the cap the figure is the builder's faithful diagram. -/
theorem builder_faithful (R : RationalPlot)
    (h : (R.zeros.length + R.poles.length ≤ maxPoints && R.lo.1 < R.hi.1 && R.lo.2 < R.hi.2) =
      true) : R.Faithful R.figure := by
  have e : R.figure.marks = R.draw.marks := by simp only [figure, Diagram.capped, h, ite_true]
  have hd := R.draw_faithful
  unfold Faithful Diagram.marksWhere at hd ⊢
  rw [e]
  exact hd

/-- A zero is circled (in some position of the list) exactly when it is a supplied zero:
`(k, z)` is drawn as a circle of part `datum 0 k` exactly when `zeros[k]` is at `z`. -/
theorem mem_zeroMarks (R : RationalPlot) (k : Nat) (z : GaussQ) :
    { part := .datum 0 k, shape := .circle z R.markSize, ink := .accent 0 } ∈ R.zeroMarks ↔
      ∃ m, R.zeros[k]? = some (z, m) := by
  simp only [zeroMarks, List.mem_map]
  constructor
  · rintro ⟨⟨⟨z', m⟩, k'⟩, h, he⟩
    simp only [Mark.mk.injEq, Part.datum.injEq, Shape.circle.injEq] at he
    obtain ⟨⟨-, rfl⟩, ⟨rfl, -⟩, -⟩ := he
    exact ⟨m, List.mem_zipIdx_iff_getElem?.1 h⟩
  · rintro ⟨m, h⟩
    exact ⟨((z, m), k), List.mem_zipIdx_iff_getElem?.2 h, rfl⟩

end RationalPlot

end PILean.Diagram
