/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Trust.Attr

/-!
# Worked instances of the exact plane interface

Three representations of exact numbers with instances of `Exact.RealValue` and
`Exact.PlanePoint`, to show that the interface fits representations other than the rationals:

* `GaussQ`: Gaussian rationals `a + b i`, exact (radius 0), with a proof of the laws.
* `QSqrt5`: numbers `a + b √5` of the field ℚ(√5), with the golden ratio `φ`; their balls come
  from `Exact.sqrtBall` and are checked exactly by squaring (`QSqrt5.certifies`).
* `Zeta5`: elements of the ring ℤ[ζ₅] (`ζ₅ = e^{2πi/5}`) as arrays of four integer coefficients
  in the basis `1, ζ, ζ², ζ³`, the representation of a cyclotomic ring by integer coefficient
  arrays. The real part lies in ℚ(√5); the imaginary part is a combination of
  `sin 72° = √(10 + 2√5) / 4` and `sin 144° = √(10 - 2√5) / 4`, enclosed by nested square roots.

`zetaSteps` is a gallery figure drawn from exact points of ℤ[ζ₅]: the unit steps `ζʲ`, a window
disk with a rational centre and radius, and the steps that end in the window decided exactly in
ℚ(√5). `zetaSteps_spec` says what it holds and where its points are drawn.
-/

namespace PILeanTest.PlaneExact

open PILean PILean.Exact PILean.Plane

/-! ### Gaussian rationals -/

/-- The Gaussian rational `re + im i`. -/
structure GaussQ where
  /-- The real part. -/
  re : Rat
  /-- The imaginary part. -/
  im : Rat
  deriving BEq, Repr, Inhabited

/-- A Gaussian rational is its own ball. -/
instance : PlanePoint GaussQ where
  re z _ := ⟨z.re, 0⟩
  im z _ := ⟨z.im, 0⟩

/-- Gaussian rationals are exact. -/
instance : LawfulPlanePoint GaussQ where
  re_nonneg _ _ := Rat.le_refl
  im_nonneg _ _ := Rat.le_refl
  re_le _ k := by show (0 : Rat) * 2 ^ k ≤ 1; simp; decide
  im_le _ k := by show (0 : Rat) * 2 ^ k ≤ 1; simp; decide

/-! ### The field ℚ(√5) -/

/-- The number `a + b √5`. -/
structure QSqrt5 where
  /-- The rational part. -/
  a : Rat
  /-- The coefficient of `√5`. -/
  b : Rat := 0
  deriving BEq, Repr, Inhabited

namespace QSqrt5

/-- The sum. -/
def add (x y : QSqrt5) : QSqrt5 := ⟨x.a + y.a, x.b + y.b⟩

/-- The difference. -/
def sub (x y : QSqrt5) : QSqrt5 := ⟨x.a - y.a, x.b - y.b⟩

/-- The product: `(a + b√5)(c + d√5) = (ac + 5bd) + (ad + bc)√5`. -/
def mul (x y : QSqrt5) : QSqrt5 := ⟨x.a * y.a + 5 * x.b * y.b, x.a * y.b + x.b * y.a⟩

/-- The golden ratio `φ = (1 + √5) / 2`. -/
def phi : QSqrt5 := ⟨1 / 2, 1 / 2⟩

/-- The absolute value of a rational. -/
def absQ (q : Rat) : Rat := if q < 0 then -q else q

/-- Whether `a + b √5 ≥ 0`, decided exactly: by the signs of `a` and `b` and, when they differ, by
comparing `a²` with `5 b²`. -/
def nonneg (x : QSqrt5) : Bool :=
  if x.a ≥ 0 && x.b ≥ 0 then true
  else if x.a ≤ 0 && x.b ≤ 0 then x.a == 0 && x.b == 0
  else if x.a > 0 then x.a * x.a ≥ 5 * x.b * x.b
  else 5 * x.b * x.b ≥ x.a * x.a

/-- Whether `x ≤ y`, exactly. -/
def le (x y : QSqrt5) : Bool := nonneg (sub y x)

/-- The bits needed above `|q|`: `log₂ ⌈|q|⌉ + 1`. -/
def bitsAbove (q : Rat) : Nat := ((absQ q).ceil.toNat).log2 + 1

/-- The ball at precision `k`: `a + b · sqrtBall 5 k'` with `k'` large enough that `|b|` times the
radius of the ball of `√5` is at most `2⁻ᵏ`. -/
def ball (x : QSqrt5) (k : Nat) : RatBall :=
  ((sqrtBall 5 (k + bitsAbove x.b + 1)).smul x.b).add ⟨x.a, 0⟩

/-- Whether a ball holds `a + b √5`, checked exactly: with `t = (v - a) / b` for each end `v`, the
lower end's `t` is at most `√5` and the upper end's at least `√5` (reversed for `b < 0`), each
decided by squaring; for `b = 0` the ball holds `a`. -/
def certifies (x : QSqrt5) (r : RatBall) : Bool :=
  let belowRoot := fun (t : Rat) => t ≤ 0 || t * t ≤ 5
  let aboveRoot := fun (t : Rat) => t ≥ 0 && t * t ≥ 5
  if x.b == 0 then r.contains x.a
  else
    let tl := (r.lo - x.a) / x.b
    let th := (r.hi - x.a) / x.b
    if x.b > 0 then belowRoot tl && aboveRoot th else belowRoot th && aboveRoot tl

end QSqrt5

/-- A number of ℚ(√5) as a real value. -/
instance : RealValue QSqrt5 where
  ball := QSqrt5.ball

/-- A pair of numbers of ℚ(√5) as a point. -/
instance : PlanePoint (QSqrt5 × QSqrt5) where
  re p k := QSqrt5.ball p.1 k
  im p k := QSqrt5.ball p.2 k

/-! ### The ring ℤ[ζ₅] -/

/-- An element `c₀ + c₁ ζ + c₂ ζ² + c₃ ζ³` of ℤ[ζ₅], `ζ = e^{2πi/5}` (missing coefficients are
0). -/
structure Zeta5 where
  /-- The coefficients in the basis `1, ζ, ζ², ζ³`. -/
  c : Array Int
  deriving BEq, Repr, Inhabited

namespace Zeta5

/-- Coefficient `i`. -/
def coeff (z : Zeta5) (i : Nat) : Int := z.c.getD i 0

/-- The sum. -/
def add (x y : Zeta5) : Zeta5 := ⟨(List.range 4).toArray.map fun i => x.coeff i + y.coeff i⟩

/-- The negation. -/
def neg (x : Zeta5) : Zeta5 := ⟨(List.range 4).toArray.map fun i => -x.coeff i⟩

/-- `0`. -/
def zero : Zeta5 := ⟨#[0, 0, 0, 0]⟩

/-- `ζʲ`: `ζ⁴ = -1 - ζ - ζ² - ζ³`, and `ζ⁵ = 1`. -/
def pow (j : Nat) : Zeta5 :=
  match j % 5 with
  | 0 => ⟨#[1, 0, 0, 0]⟩
  | 1 => ⟨#[0, 1, 0, 0]⟩
  | 2 => ⟨#[0, 0, 1, 0]⟩
  | 3 => ⟨#[0, 0, 0, 1]⟩
  | _ => ⟨#[-1, -1, -1, -1]⟩

/-- The real part, in ℚ(√5): `cos 72° = (√5 - 1)/4`, `cos 144° = cos 216° = -(1 + √5)/4`. -/
def realPart (z : Zeta5) : QSqrt5 :=
  let c1 : Rat := z.coeff 1
  let c23 : Rat := z.coeff 2 + z.coeff 3
  ⟨z.coeff 0 - c1 / 4 - c23 / 4, c1 / 4 - c23 / 4⟩

/-- A ball around `√X` for `X` in the ball `x` (`x.lo ≥ 0`): from the lower end's square root's
lower end to the upper end's square root's upper end. -/
def sqrtOfBall (x : RatBall) (k : Nat) : RatBall :=
  RatBall.ofBounds (sqrtBall x.lo k).lo (sqrtBall x.hi k).hi

/-- A ball around `sin 72° = √(10 + 2√5) / 4` (`plus`) or `sin 144° = √(10 - 2√5) / 4`. -/
def sinBall (plus : Bool) (k : Nat) : RatBall :=
  (sqrtOfBall (QSqrt5.ball ⟨10, if plus then 2 else -2⟩ (k + 2)) (k + 2)).smul (1 / 4)

/-- The imaginary part's ball: `c₁ sin 72° + (c₂ - c₃) sin 144°`, at a precision raised by the
size of the coefficients. -/
def imBall (z : Zeta5) (k : Nat) : RatBall :=
  let c1 : Rat := z.coeff 1
  let d : Rat := z.coeff 2 - z.coeff 3
  let k' := k + QSqrt5.bitsAbove c1 + QSqrt5.bitsAbove d + 2
  ((sinBall true k').smul c1).add ((sinBall false k').smul d)

end Zeta5

/-- An element of ℤ[ζ₅] as a point of the complex plane. -/
instance : PlanePoint Zeta5 where
  re z k := QSqrt5.ball z.realPart k
  im z k := Zeta5.imBall z k

/-! ### A figure from exact points -/

/-- The centre of the window: `1/2`. -/
def windowCentre : Rat × Rat := (1 / 2, 0)

/-- The radius of the window: `39/40`. -/
def windowRadius : Rat := 39 / 40

/-- Whether `ζʲ` lies in the window, decided exactly: `|ζʲ - 1/2|² = 5/4 - Re ζʲ ≤ (39/40)²`,
that is `Re ζʲ ≥ 5/4 - 1521/1600`, compared in ℚ(√5). -/
def inWindow (j : Nat) : Bool :=
  QSqrt5.le ⟨5 / 4 - windowRadius * windowRadius, 0⟩ (Zeta5.pow j).realPart

/-- The labels of the steps. -/
def stepLabel (j : Nat) : String := #["1", "ζ", "ζ²", "ζ³", "ζ⁴"].getD j ""

/-- The items of step `j`: the segment from the origin to `ζʲ` (accent 0 when `ζʲ` is in the window,
faint otherwise) and its label, outside the circle in the direction of the step. -/
def stepItems (j : Nat) : Array Item :=
  let t : Tone := if inWindow j then .accent 0 else .faint
  #[(Plane.Exact.segment Zeta5.zero (Zeta5.pow j)).tone t,
    (Plane.Exact.label (stepLabel j) (Zeta5.pow j) (.toward (2 * pi * j.toFloat / 5))).tone t]

/-- The window disk. -/
def window : Item :=
  (Plane.Exact.disk windowCentre windowRadius).accent 0 |>.named "the window" |>.describedBy
    "the closed disk of radius 39/40 about 1/2"

/-- The point `ζʲ`, with where it stands relative to the window decided exactly
(`Plane.Exact.pointNearDisk`): `ζ` and `ζ⁴` are inside it, a fraction of a pixel from its
boundary at the gallery's scale, so the figure must say so. -/
def stepPoint (j : Nat) : Item :=
  Plane.Exact.pointNearDisk (Zeta5.pow j) windowCentre windowRadius "the window"

/-- The unit steps `ζʲ` of ℤ[ζ₅] and a window: the steps ending in the window are coloured. -/
@[figure]
def zetaSteps : Plane.Figure where
  width := 420
  items := #[window] ++ ((List.range 5).toArray.flatMap stepItems) ++
    ((List.range 5).toArray.map stepPoint) ++
    #[Plane.Exact.point ((0, 0) : Int × Int),
      Plane.Exact.point windowCentre |>.incident .on "the step to 1"]
  info := { title := "Unit steps of ℤ[ζ₅] and a window",
            leanDecl := "PILeanTest.PlaneExact.zetaSteps" }

/-- What the figure holds and where its points are drawn: a window disk, the segments and labels
of the five steps, then the points `ζʲ`, `0` and the window's centre; each point `ζʲ` is a point
item at the conversion of the exact point, so it is drawn as a marker at the frame's image of
that conversion (`Plane.drawItem_point`). The steps in the window are exactly `1`, `ζ` and `ζ⁴`
(decided in ℚ(√5)). -/
theorem zetaSteps_spec :
    zetaSteps.items = #[window] ++ ((List.range 5).toArray.flatMap stepItems) ++
      ((List.range 5).toArray.map stepPoint) ++
      #[Plane.Exact.point ((0, 0) : Int × Int),
        Plane.Exact.point windowCentre |>.incident .on "the step to 1"] ∧
    (∀ j, ∃ (l : Look) (i : Canvas.ShapeInfo),
      stepPoint j = .shape (.point (PlanePoint.toPoint (Zeta5.pow j))) l i) ∧
    ((List.range 5).filter inWindow) = [0, 1, 4] := by
  refine ⟨rfl, fun j => Plane.Exact.pointNearDisk_eq .., by decide +kernel⟩

figure_proves zetaSteps zetaSteps_spec

end PILeanTest.PlaneExact
