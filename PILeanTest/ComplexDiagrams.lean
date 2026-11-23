/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Trust.Attr

/-!
# Figures of complex analysis

* `rationalFigure`: the zeros and poles of
  `f(z) = (z² + 1)(z − 1/2)² / ((z² − 2z + 2)(z + 3/2))`. `rationalFigure_spec`: the supplied
  zeros `i`, `−i` (simple) and `1/2` (double) and poles `1 + i`, `1 − i`, `−3/2` (simple) are
  roots of the numerator and the denominator of exactly those multiplicities (checked by the
  kernel in Gaussian rational arithmetic), their multiplicities add up to the degrees (4 and 3),
  the figure draws them faithfully with the multiplicity `2` written beside `1/2` and nothing
  else, and its title names `f`. `pilean-mathlib` reads the same coefficients as `Polynomial ℚ`
  over ℂ (`PILeanMathlib.Examples.rationalFigure_roots`): each mark is a root of
  `Polynomial.rootMultiplicity` its stated multiplicity, and every complex root is marked.
* `domainColouring`: the same function painted by domain colouring, in floating point; an
  illustration, marked `@[figure illustration]`, with no theorem.
-/

namespace PILeanTest.ComplexDiagrams

open PILean PILean.Diagram

/-- `f(z) = (z² + 1)(z − 1/2)² / ((z² − 2z + 2)(z + 3/2))`: the numerator
`z⁴ − z³ + 5/4 z² − z + 1/4`, the denominator `z³ − 1/2 z² − z + 3`, the zeros and poles
supplied, the window `[-2, 2] × [-3/2, 3/2]`. -/
def rationalData : RationalPlot where
  name := "f(z) = (z² + 1)(z − 1/2)² / ((z² − 2z + 2)(z + 3/2))"
  num := [1 / 4, -1, 5 / 4, -1, 1]
  den := [3, -1, -1 / 2, 1]
  zeros := [((0, 1), 1), ((0, -1), 1), ((1 / 2, 0), 2)]
  poles := [((1, 1), 1), ((1, -1), 1), ((-3 / 2, 0), 1)]
  lo := (-2, -3 / 2)
  hi := (2, 3 / 2)

/-- The zeros and poles of `f`. -/
@[figure]
def rationalFigure : Diagram := rationalData.figure

/-- **The zeros and poles of `f`.** The zeros are `i`, `−i` (simple) and `1/2` (double) and the
poles `1 + i`, `1 − i` and `−3/2` (simple), each a root of the numerator or the denominator of
exactly that multiplicity (`RationalPlot.Verified`), the multiplicities adding up to the degrees
(`RationalPlot.Complete`); the figure draws them faithfully, writes `2` beside `1/2` and no other
multiplicity, and its title names `f`. -/
theorem rationalFigure_spec :
    rationalData.zeros = [((0, 1), 1), ((0, -1), 1), ((1 / 2, 0), 2)] ∧
    rationalData.poles = [((1, 1), 1), ((1, -1), 1), ((-3 / 2, 0), 1)] ∧
    rationalData.num = [1 / 4, -1, 5 / 4, -1, 1] ∧ rationalData.den = [3, -1, -1 / 2, 1] ∧
    rationalData.Verified = true ∧ rationalData.Complete = true ∧
    rationalData.Faithful rationalFigure ∧
    rationalFigure.marksWhere RationalPlot.isLabel =
      [{ part := .entry 0 2, shape := .text "2" (1 / 2 + 1 / 15, 1 / 15) .aboveRight,
         ink := .accent 0 }] ∧
    rationalFigure.title = "Zeros and poles of f(z) = (z² + 1)(z − 1/2)² / ((z² − 2z + 2)(z + 3/2))" := by
  have h : rationalData.Faithful rationalFigure := rationalData.builder_faithful (by decide +kernel)
  refine ⟨rfl, rfl, rfl, rfl, by decide +kernel, by decide +kernel, h, ?_, ?_⟩
  · rw [h.2.2.1]; decide +kernel
  · unfold rationalFigure RationalPlot.figure; rw [Diagram.capped_of (by decide +kernel)]; rfl

figure_proves rationalFigure rationalFigure_spec

/-! ### The same function, painted -/

/-- The product of two complex numbers as pairs of floats. -/
def cmul (z w : Float × Float) : Float × Float := (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- The quotient of two complex numbers as pairs of floats (not finite at `w = 0`). -/
def cdiv (z w : Float × Float) : Float × Float :=
  let d := w.1 * w.1 + w.2 * w.2
  ((z.1 * w.1 + z.2 * w.2) / d, (z.2 * w.1 - z.1 * w.2) / d)

/-- `f` in floating point. -/
def fFloat (x y : Float) : Float × Float :=
  let z := (x, y)
  let z2 := cmul z z
  let h := (x - 0.5, y)
  let num := cmul (z2.1 + 1, z2.2) (cmul h h)
  let den := cmul (z2.1 - 2 * x + 2, z2.2 - 2 * y) (x + 1.5, y)
  cdiv num den

/-- `f` painted over the window of `rationalFigure` by domain colouring: an illustration, computed
in floating point, with no theorem. -/
@[figure illustration]
def domainColouring : DomainColouring :=
  { name := "f(z) = (z² + 1)(z − 1/2)² / ((z² − 2z + 2)(z + 3/2))", f := fFloat,
    lo := ⟨-2, -1.5⟩, hi := ⟨2, 1.5⟩, width := 480, height := 360 }

/-- The figures by file stem. -/
def figures : Array (String × Diagram) := #[("diagram-zeros-poles", rationalFigure)]

/-- The gallery's files: each figure as a plane figure, light and dark. -/
def gallery : Array (String × Plane.Figure) :=
  figures.map (fun (n, d) => (n ++ ".svg", d.toPlane)) ++
    figures.map (fun (n, d) => (n ++ "-dark.svg", d.dark.toPlane))

/-- The checks: the figure passes the layout checks in both themes, its PDF the structural check,
and the domain colouring renders its PNG and PDF and is an illustration by the build's table. -/
def checks : Array (String × Bool) :=
  let os := Trust.ToOutputs.outputs domainColouring
  #[("zeros and poles: no layout problem, light and dark",
      rationalFigure.toPlane.problems.isEmpty && rationalFigure.dark.toPlane.problems.isEmpty),
    ("zeros and poles: the PDF passes the structural check",
      (Pdf.check rationalFigure.toPlane.toPdf).isOk),
    ("domain colouring: a PNG and a PDF, both render, the PDF passes the structural check",
      os.map (·.format.name) == #["png", "pdf"] && os.all (fun o => (o.bytes ()).isOk) &&
        match (os[1]?.map (·.bytes ()) : Option (Except String ByteArray)) with
        | some (.ok b) => (Pdf.check b).isOk
        | _ => false),
    ("domain colouring: every hue around the zero at 1/2, red on the positive reals",
      match domainColouring.toImage with
      | some im =>
        let at_ := fun (x y : Nat) => im.getpixel x y
        -- the zero at 1/2 is near pixel (300, 180): four points around it have four colours;
        -- far right on the real axis f is positive, so the hue is red
        let around := [at_ 306 180, at_ 300 174, at_ 294 180, at_ 300 186]
        im.width == 480 && im.height == 360 && around.eraseDups.length == 4 &&
          (at_ 479 180).r > (at_ 479 180).g
      | none => false)]

end PILeanTest.ComplexDiagrams
