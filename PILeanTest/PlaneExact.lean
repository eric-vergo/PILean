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

/-- A piece of the chord in a role, with its label beside it. -/
def piece (a b : Zeta5) (role label : String) : Array Item :=
  #[Plane.Exact.segment a b |>.role role |>.width 6,
    Plane.Exact.labelBeside label a b |>.role role |>.size 14]

/-- The items of the reference figure. -/
def items : Array Item :=
  #[Plane.Exact.disk left R |>.noFill |>.width 1.5 |>.named "the left disk",
    Plane.Exact.disk right R |>.noFill |>.width 1.5 |>.named "the right disk",
    Plane.Exact.lens left right R R |>.role "lens" |>.fillOpacity 0.14 |>.named "the lens"] ++
  piece (-E) (-F) "s1" "S₁" ++ piece (-F) (-G) "s2" "S₂" ++ piece (-G) E "s3" "S₃" ++
  #[Plane.Exact.point left, Plane.Exact.point right,
    Plane.Exact.point Zeta5.zero |>.incident .on "the chord",
    Plane.Exact.point E |>.incident .on "the left circle",
    Plane.Exact.point (-E) |>.incident .on "the right circle",
    Plane.Exact.point corner |>.incident .on "both circles",
    Plane.Exact.point (-corner) |>.incident .on "both circles",
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

/-- What the reference figure holds, and the incidences its points record, decided exactly in
ℚ(√5): `E` is on the left circle and `-E` on the right one (`|E + 1|² = |-E - 1|² = 3 + φ`), and
the corners are on both (`|ζ - ζ⁴ ± 1|² = 3 + φ`). -/
theorem reference_spec :
    reference.items = Reference.items ∧
    (Reference.E + Reference.right).normSq = Reference.threePlusPhi ∧
    (-Reference.E - Reference.right).normSq = Reference.threePlusPhi ∧
    (Reference.corner + Reference.right).normSq = Reference.threePlusPhi ∧
    (Reference.corner - Reference.right).normSq = Reference.threePlusPhi := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

figure_proves reference reference_spec

end PILeanTest.PlaneExact
