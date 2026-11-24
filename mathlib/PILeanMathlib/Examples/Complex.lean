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
data faithfully; with `p` and `q` the numerator and the denominator read as polynomials over ℚ
and then over ℂ, every supplied zero `(z, m)` has `rootMultiplicity z p = m`, every supplied pole
`(z, m)` has `rootMultiplicity z q = m`, and every complex root of `p` (of `q`) is a supplied zero
(pole). -/
theorem rationalFigure_roots :
    rationalData.Faithful rationalFigure ∧
    (∀ zm ∈ rationalData.zeros, (ofCoeffsC rationalData.num).rootMultiplicity (toC zm.1) = zm.2) ∧
    (∀ zm ∈ rationalData.poles, (ofCoeffsC rationalData.den).rootMultiplicity (toC zm.1) = zm.2) ∧
    (∀ w : ℂ, (ofCoeffsC rationalData.num).IsRoot w → ∃ zm ∈ rationalData.zeros, w = toC zm.1) ∧
    (∀ w : ℂ, (ofCoeffsC rationalData.den).IsRoot w → ∃ zm ∈ rationalData.poles, w = toC zm.1) := by
  obtain ⟨-, -, -, -, hv, hc, hf, -⟩ := rationalFigure_spec
  exact ⟨hf, fun zm h => RationalPlot.zero_rootMultiplicity hv h,
    fun zm h => RationalPlot.pole_rootMultiplicity hv h,
    fun w hw => RationalPlot.zeros_complete hv hc hw,
    fun w hw => RationalPlot.poles_complete hv hc hw⟩

figure_links rationalFigure rationalFigure_roots

end PILeanMathlib.Examples
