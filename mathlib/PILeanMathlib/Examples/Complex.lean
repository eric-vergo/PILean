/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanMathlib.RationalPlot
import PILeanTest.ComplexDiagrams

/-!
# The zeros and poles of the gallery's rational function, against Mathlib

`rationalFigure_roots` reads the numerator and the denominator of the gallery's figure
`PILeanTest.ComplexDiagrams.rationalFigure` as polynomials over ℚ (`ofCoeffs`) and states, over ℂ,
what its marks are: each circled point is a root of the numerator of exactly the written
multiplicity (`Polynomial.rootMultiplicity`), each cross a root of the denominator, and every
complex root of either is marked.
-/

open Polynomial PILean.Diagram PILeanTest.ComplexDiagrams

namespace PILeanMathlib.Examples

/-- **The marks are the zeros and the poles, with their multiplicities.** The figure draws its
data (written out) faithfully, with the one multiplicity it writes, and its title names the
function; with `p` and `q` the numerator and the denominator read as polynomials over ℚ and then
over ℂ, every supplied zero `(z, m)` has `rootMultiplicity z p = m`, every supplied pole `(z, m)`
has `rootMultiplicity z q = m`, and every complex root of `p` (of `q`) is a supplied zero
(pole).
The statement begins with the figure written out, with the definitions it is built from, so that it
determines the whole figure (`PILean.Trust.figurePinProblem?`). -/
theorem rationalFigure_roots :
    rationalFigure = (rationalData.figure : Diagram) ∧
    rationalData = ({
      name := "f(z) = (z² + 1)(z − 1/2)² / ((z² − 2z + 2)(z + 3/2))"
      num := [1 / 4, -1, 5 / 4, -1, 1]
      den := [3, -1, -1 / 2, 1]
      zeros := [((0, 1), 1), ((0, -1), 1), ((1 / 2, 0), 2)]
      poles := [((1, 1), 1), ((1, -1), 1), ((-3 / 2, 0), 1)]
      lo := (-2, -3 / 2)
      hi := (2, 3 / 2) } : RationalPlot) ∧
    rationalData.zeros = [((0, 1), 1), ((0, -1), 1), ((1 / 2, 0), 2)] ∧
    rationalData.poles = [((1, 1), 1), ((1, -1), 1), ((-3 / 2, 0), 1)] ∧
    rationalData.num = [1 / 4, -1, 5 / 4, -1, 1] ∧ rationalData.den = [3, -1, -1 / 2, 1] ∧
    rationalData.Faithful rationalFigure ∧
    rationalFigure.marksWhere RationalPlot.isLabel =
      [{ part := .entry 0 2, shape := .text "2" (1 / 2 + 1 / 15, 1 / 15) .aboveRight,
         ink := .accent 0 }] ∧
    rationalFigure.title =
      "Zeros and poles of f(z) = (z² + 1)(z − 1/2)² / ((z² − 2z + 2)(z + 3/2))" ∧
    (∀ zm ∈ rationalData.zeros, (ofCoeffsC rationalData.num).rootMultiplicity (toC zm.1) = zm.2) ∧
    (∀ zm ∈ rationalData.poles, (ofCoeffsC rationalData.den).rootMultiplicity (toC zm.1) = zm.2) ∧
    (∀ w : ℂ, (ofCoeffsC rationalData.num).IsRoot w → ∃ zm ∈ rationalData.zeros, w = toC zm.1) ∧
    (∀ w : ℂ, (ofCoeffsC rationalData.den).IsRoot w → ∃ zm ∈ rationalData.poles, w = toC zm.1) := by
  obtain ⟨p1, p2, h1, h2, h3, h4, hv, hc, hf, hl, ht⟩ := rationalFigure_spec
  exact ⟨p1, p2, h1, h2, h3, h4, hf, hl, ht, fun zm h => RationalPlot.zero_rootMultiplicity hv h,
    fun zm h => RationalPlot.pole_rootMultiplicity hv h,
    fun w hw => RationalPlot.zeros_complete hv hc hw,
    fun w hw => RationalPlot.poles_complete hv hc hw⟩

figure_links rationalFigure rationalFigure_roots

end PILeanMathlib.Examples
