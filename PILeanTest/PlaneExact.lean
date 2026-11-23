/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Trust.Attr

/-!
# Worked instances of the exact plane interface

Representations of exact numbers with instances of `Exact.RealValue` and
`Exact.PlanePoint`, to show that the interface fits representations other than the rationals:

* `GaussQ`: Gaussian rationals `a + b i`, exact (radius 0), with a proof of the laws.
* `QSqrt5` and `Zeta5`, the library's ℚ(√5) and ℤ[ζ₅] (`PILean.Exact.Algebraic`), whose balls the
  tests check exactly by squaring.

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

/-! ### ℚ(√5) and ℤ[ζ₅]

The worked instances for ℚ(√5) and ℤ[ζ₅] are the library's (`PILean.Exact.Algebraic`): `QSqrt5`
and `Zeta5`, used here and checked in `PILeanTest.Plane`. -/

/-! ### A figure from exact points -/

/-- The centre of the window: `1/2`. -/
def windowCentre : Rat × Rat := (1 / 2, 0)

/-- The radius of the window: `39/40`. -/
def windowRadius : Rat := 39 / 40

/-- Whether `ζʲ` lies in the window, decided exactly: `|ζʲ - 1/2|² = 5/4 - Re ζʲ ≤ (39/40)²`,
that is `Re ζʲ ≥ 5/4 - 1521/1600`, compared in ℚ(√5). -/
def inWindow (j : Nat) : Bool :=
  QSqrt.le (⟨5 / 4 - windowRadius * windowRadius, 0⟩ : QSqrt5) (Zeta5.pow j).realPart

/-- The labels of the steps. -/
def stepLabel (j : Nat) : String := #["1", "ζ", "ζ²", "ζ³", "ζ⁴"].getD j ""

/-- The items of step `j`: the segment from the origin to `ζʲ` (accent 0 when `ζʲ` is in the window,
faint otherwise), titled `the step to` and its label, and its label, outside the circle in the
direction of the step. -/
def stepItems (j : Nat) : Array Item :=
  let t : Tone := if inWindow j then .accent 0 else .faint
  #[(Plane.Exact.segment Zeta5.zero (Zeta5.pow j)).tone t |>.named s!"the step to {stepLabel j}",
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

/-- What the figure draws, item for item, and which steps end in the window. The window is the
closed disk of radius `39/40` about `1/2`, in accent 0, titled "the window". The items are
written out in drawing order: the window; for each step `ζʲ` (`j = 0, …, 4`) the segment from `0`
to `ζʲ`, titled "the step to" and its label, and its label "1", "ζ", "ζ²", "ζ³" or "ζ⁴" outside
the circle in the direction of the step, both in accent 0 for `1`, `ζ` and `ζ⁴` and faint for
`ζ²` and `ζ³`; then the points `ζʲ`, each recording where it stands relative to the window as
`Plane.Exact.pointNearDisk` decides it: inside for `1`, `ζ` and `ζ⁴` (the last two a fraction of a
pixel from the boundary), outside for `ζ²` and `ζ³`; then `0` and the window's centre, recording
being on the step to 1. The steps in the window are exactly `1`, `ζ` and `ζ⁴` (decided in ℚ(√5),
`inWindow`), which is why those are in accent 0. Not stated: how the builders and modifiers draw,
the layout, the fonts, the style's colour values and the pixels. -/
theorem zetaSteps_spec :
    windowCentre = (1 / 2, 0) ∧ windowRadius = 39 / 40 ∧
    zetaSteps.items = #[
      Plane.Exact.disk windowCentre windowRadius |>.accent 0 |>.named "the window"
        |>.describedBy "the closed disk of radius 39/40 about 1/2",
      (Plane.Exact.segment Zeta5.zero (Zeta5.pow 0)).tone (.accent 0) |>.named "the step to 1",
      (Plane.Exact.label "1" (Zeta5.pow 0)
        (.toward (2 * pi * (0 : Nat).toFloat / 5))).tone (.accent 0),
      (Plane.Exact.segment Zeta5.zero (Zeta5.pow 1)).tone (.accent 0) |>.named "the step to ζ",
      (Plane.Exact.label "ζ" (Zeta5.pow 1)
        (.toward (2 * pi * (1 : Nat).toFloat / 5))).tone (.accent 0),
      (Plane.Exact.segment Zeta5.zero (Zeta5.pow 2)).tone .faint |>.named "the step to ζ²",
      (Plane.Exact.label "ζ²" (Zeta5.pow 2)
        (.toward (2 * pi * (2 : Nat).toFloat / 5))).tone .faint,
      (Plane.Exact.segment Zeta5.zero (Zeta5.pow 3)).tone .faint |>.named "the step to ζ³",
      (Plane.Exact.label "ζ³" (Zeta5.pow 3)
        (.toward (2 * pi * (3 : Nat).toFloat / 5))).tone .faint,
      (Plane.Exact.segment Zeta5.zero (Zeta5.pow 4)).tone (.accent 0) |>.named "the step to ζ⁴",
      (Plane.Exact.label "ζ⁴" (Zeta5.pow 4)
        (.toward (2 * pi * (4 : Nat).toFloat / 5))).tone (.accent 0),
      Plane.Exact.pointNearDisk (Zeta5.pow 0) windowCentre windowRadius "the window",
      Plane.Exact.pointNearDisk (Zeta5.pow 1) windowCentre windowRadius "the window",
      Plane.Exact.pointNearDisk (Zeta5.pow 2) windowCentre windowRadius "the window",
      Plane.Exact.pointNearDisk (Zeta5.pow 3) windowCentre windowRadius "the window",
      Plane.Exact.pointNearDisk (Zeta5.pow 4) windowCentre windowRadius "the window",
      Plane.Exact.point ((0, 0) : Int × Int),
      Plane.Exact.point windowCentre |>.incident .on "the step to 1"] ∧
    ((List.range 5).map (fun j => diskIncidence? (Zeta5.pow j) windowCentre windowRadius) ==
      [some .inside, some .inside, some .outside, some .outside, some .inside]) = true ∧
    (List.range 5).filter inWindow = [0, 1, 4] := by
  refine ⟨rfl, rfl, ?_, by decide +kernel, by decide +kernel⟩
  have h0 : inWindow 0 = true := by decide +kernel
  have h1 : inWindow 1 = true := by decide +kernel
  have h2 : inWindow 2 = false := by decide +kernel
  have h3 : inWindow 3 = false := by decide +kernel
  have h4 : inWindow 4 = true := by decide +kernel
  rw [show zetaSteps.items = #[window] ++ ((#[0, 1, 2, 3, 4] : Array Nat).flatMap stepItems) ++
    ((#[0, 1, 2, 3, 4] : Array Nat).map stepPoint) ++ #[Plane.Exact.point ((0, 0) : Int × Int),
      Plane.Exact.point windowCentre |>.incident .on "the step to 1"] from rfl,
    show (#[0, 1, 2, 3, 4] : Array Nat).flatMap stepItems =
      stepItems 0 ++ stepItems 1 ++ stepItems 2 ++ stepItems 3 ++ stepItems 4 by simp]
  simp only [stepItems, h0, h1, h2, h3, h4, ite_true, Bool.false_eq_true, ite_false]
  apply Array.toList_inj.mp
  simp only [Array.toList_append, Array.toList_map]
  rfl

figure_proves zetaSteps zetaSteps_spec

/-! ### The reference figure of the diagrammatic house style

Two closed disks of radius `R = √(3 + φ)` about `-1` and `1` as plain outlines, the lens where they
overlap as a region of its own with a strong outline, the chord from `-E` to `E` (`E = ζ - ζ²`) in
three pieces of three role colours with small labels beside them, round markers with halos, the
lens's corners `±(ζ - ζ⁴)`; every point exact in ℤ[ζ₅], the radius an exact square root, light and
dark from the roles, and a narrow rendition at 360 pixels. -/

namespace Reference

/-- `E = ζ - ζ²`. -/
def E : Zeta5 := Zeta5.pow 1 - Zeta5.pow 2

/-- `φ⁻¹ = ζ + ζ⁴ = -1 - ζ² - ζ³`. -/
def phiInv : Zeta5 := ⟨#[-1, 0, -1, -1]⟩

/-- `F = φ⁻¹ E`, where the first piece ends. -/
def F : Zeta5 := phiInv * E

/-- `G = φ⁻³ E`, where the second piece ends. -/
def G : Zeta5 := phiInv * phiInv * phiInv * E

/-- The lens's upper corner `ζ - ζ⁴`. -/
def corner : Zeta5 := Zeta5.pow 1 - Zeta5.pow 4

/-- The centres `-1` and `1`. -/
def left : Zeta5 := Zeta5.ofInt (-1)

/-- The centre `1`. -/
def right : Zeta5 := Zeta5.ofInt 1

/-- `3 + φ` in ℚ(√5). -/
def threePlusPhi : QSqrt5 := ⟨7 / 2, 1 / 2⟩

/-- The radius `R = √(3 + φ)`. -/
def R : SqrtOf QSqrt5 := ⟨threePlusPhi⟩

/-- The house style: the default colours with four named roles, thicker lines, larger markers
with wider halos. -/
def houseStyle : Style :=
  { Style.light with plane := { PlaneStyle.light with
      lineWidth := 2.5, markerRadius := 4.5, markerRing := 2, labelSize := 15,
      roles := #[⟨"lens", ⟨154, 69, 0, 255⟩, ⟨245, 184, 61, 255⟩⟩,
        ⟨"s1", ⟨29, 78, 216, 255⟩, ⟨143, 176, 252, 255⟩⟩,
        ⟨"s2", ⟨162, 28, 175, 255⟩, ⟨239, 166, 247, 255⟩⟩,
        ⟨"s3", ⟨13, 107, 99, 255⟩, ⟨94, 224, 200, 255⟩⟩] } }

/-- The left circle: the closed disk of radius `R` about `-1`, outlined, untinted. -/
def leftCircle : Item :=
  Plane.Exact.disk left R |>.noFill |>.width 1.5 |>.named "the left circle"

/-- The right circle: the closed disk of radius `R` about `1`, outlined, untinted. -/
def rightCircle : Item :=
  Plane.Exact.disk right R |>.noFill |>.width 1.5 |>.named "the right circle"

/-- The lens: the intersection of the two closed disks, a region of its own in the role
`lens`. -/
def lens : Item :=
  Plane.Exact.lens left right R R |>.role "lens" |>.fillOpacity 0.14 |>.named "the lens"

/-- The piece of the chord from `a` to `b` in a role, with a title. -/
def piece (a b : Zeta5) (role title : String) : Item :=
  Plane.Exact.segment a b |>.role role |>.width 6 |>.named title

/-- The label of a piece, beside it, in its role. -/
def pieceLabel (a b : Zeta5) (role label : String) : Item :=
  Plane.Exact.labelBeside label a b |>.role role |>.size 14

/-- The first piece, from `-E` to `-F`. -/
def pieceS1 : Item := piece (-E) (-F) "s1" "the piece S₁"

/-- The second piece, from `-F` to `-G`. -/
def pieceS2 : Item := piece (-F) (-G) "s2" "the piece S₂"

/-- The third piece, from `-G` to `E`, through `0`. -/
def pieceS3 : Item := piece (-G) E "s3" "the piece S₃"

/-- The point `0`, on the third piece. -/
def pointZero : Item := Plane.Exact.point Zeta5.zero |>.incident .on "the piece S₃"

/-- The point `E`, on the left circle and so on the lens's boundary. -/
def pointE : Item :=
  Plane.Exact.point E |>.incident .on "the left circle" |>.incident .on "the lens"

/-- The point `-E`, on the right circle and so on the lens's boundary. -/
def pointNegE : Item :=
  Plane.Exact.point (-E) |>.incident .on "the right circle" |>.incident .on "the lens"

/-- A corner `c` of the lens, on both circles. -/
def cornerPoint (c : Zeta5) : Item :=
  Plane.Exact.point c |>.incident .on "the left circle" |>.incident .on "the right circle"
    |>.incident .on "the lens"

/-- The items of the reference figure. -/
def items : Array Item :=
  #[leftCircle, rightCircle, lens, pieceS1, pieceLabel (-E) (-F) "s1" "S₁", pieceS2,
    pieceLabel (-F) (-G) "s2" "S₂", pieceS3, pieceLabel (-G) E "s3" "S₃",
    Plane.Exact.point left, Plane.Exact.point right, pointZero, pointE, pointNegE,
    cornerPoint corner, cornerPoint (-corner),
    Plane.Exact.label "−1" left .auto, Plane.Exact.label "+1" right .auto,
    Plane.Exact.label "0" Zeta5.zero .auto, Plane.Exact.label "E" E .auto,
    Plane.Exact.label "−E" (-E) .auto]

end Reference

/-- The reference figure of the diagrammatic house style (see the section's docstring). -/
@[figure]
def reference : Plane.Figure where
  width := 720
  narrowWidth := some 360
  padding := 24
  style := Reference.houseStyle
  items := Reference.items
  info := { title := "Two disks, their lens and the chord in three pieces" }

open Reference in
/-- What the reference figure draws, item for item, and why its records are right. The data are
`E = ζ - ζ²`, `φ⁻¹ = ζ + ζ⁴`, `F = φ⁻¹ E`, `G = φ⁻³ E`, the corner `ζ - ζ⁴`, the centres `-1` and
`1` and the radius `R = √(3 + φ)` (`3 + φ = 7/2 + √5/2`). The items are written out in drawing
order, each with its colour (a role or the ink), its title, its width and the incidences it
records: the left and right circles (the closed disks of radius `R` about `-1` and `1`, outlined
and untinted), the lens (their intersection) in the role `lens`, the chord's pieces from `-E` to
`-F`, from `-F` to `-G` and from `-G` to `E` in the roles `s1`, `s2`, `s3`, each followed by its
label "S₁", "S₂", "S₃" beside it in its role, the centres, the point `0` recording being on the
third piece, `E` recording being on the left circle and the lens, `-E` on the right circle and
the lens, the corners `±(ζ - ζ⁴)` on both circles and the lens, and the labels "−1", "+1", "0",
"E" and "−E" at their points. The records hold, exactly in ℚ(√5): `|E + 1|² = 3 + φ` and
`|E - 1|² < 3 + φ` (`E` is on the left circle and inside the right disk, so on the lens's
boundary), the same for `-E` with the sides exchanged, `|ζ - ζ⁴ ± 1|² = 3 + φ` for both corners;
and `φ⁻¹ = ζ + ζ⁴` is real and between 0 and 1, so `-G = -φ⁻³ E` lies between `-E` and `0` and
the third piece passes through `0`. Not stated: how the builders and modifiers draw, the layout,
the fonts, the style's colour values (`houseStyle`) and the pixels. -/
theorem reference_spec :
    E = Zeta5.pow 1 - Zeta5.pow 2 ∧ phiInv = ⟨#[-1, 0, -1, -1]⟩ ∧ F = phiInv * E ∧
    G = phiInv * phiInv * phiInv * E ∧ corner = Zeta5.pow 1 - Zeta5.pow 4 ∧
    left = Zeta5.ofInt (-1) ∧ right = Zeta5.ofInt 1 ∧ R = ⟨⟨7 / 2, 1 / 2⟩⟩ ∧
    reference.items = #[
      Plane.Exact.disk left R |>.noFill |>.width 1.5 |>.named "the left circle",
      Plane.Exact.disk right R |>.noFill |>.width 1.5 |>.named "the right circle",
      Plane.Exact.lens left right R R |>.role "lens" |>.fillOpacity 0.14 |>.named "the lens",
      Plane.Exact.segment (-E) (-F) |>.role "s1" |>.width 6 |>.named "the piece S₁",
      Plane.Exact.labelBeside "S₁" (-E) (-F) |>.role "s1" |>.size 14,
      Plane.Exact.segment (-F) (-G) |>.role "s2" |>.width 6 |>.named "the piece S₂",
      Plane.Exact.labelBeside "S₂" (-F) (-G) |>.role "s2" |>.size 14,
      Plane.Exact.segment (-G) E |>.role "s3" |>.width 6 |>.named "the piece S₃",
      Plane.Exact.labelBeside "S₃" (-G) E |>.role "s3" |>.size 14,
      Plane.Exact.point left, Plane.Exact.point right,
      Plane.Exact.point Zeta5.zero |>.incident .on "the piece S₃",
      Plane.Exact.point E |>.incident .on "the left circle" |>.incident .on "the lens",
      Plane.Exact.point (-E) |>.incident .on "the right circle" |>.incident .on "the lens",
      Plane.Exact.point corner |>.incident .on "the left circle"
        |>.incident .on "the right circle" |>.incident .on "the lens",
      Plane.Exact.point (-corner) |>.incident .on "the left circle"
        |>.incident .on "the right circle" |>.incident .on "the lens",
      Plane.Exact.label "−1" left .auto, Plane.Exact.label "+1" right .auto,
      Plane.Exact.label "0" Zeta5.zero .auto, Plane.Exact.label "E" E .auto,
      Plane.Exact.label "−E" (-E) .auto] ∧
    (E - left).normSq = R.radicand ∧ QSqrt.lt (E - right).normSq R.radicand = true ∧
    (-E - right).normSq = R.radicand ∧ QSqrt.lt (-E - left).normSq R.radicand = true ∧
    (corner - left).normSq = R.radicand ∧ (corner - right).normSq = R.radicand ∧
    (-corner - left).normSq = R.radicand ∧ (-corner - right).normSq = R.radicand ∧
    (phiInv.conj == phiInv) = true ∧ QSqrt.lt ⟨0, 0⟩ phiInv.realPart = true ∧
    QSqrt.lt phiInv.realPart ⟨1, 0⟩ = true ∧ (G == phiInv * phiInv * phiInv * E) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_proves reference reference_spec

end PILeanTest.PlaneExact
