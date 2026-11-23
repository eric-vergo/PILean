/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import PILean.Plot.Exact
import PILeanMathlib.CertifiedPlotBound
import PILeanMathlib.Examples.RealFigures

/-!
# Certified plots of real functions: the theorems

Each figure of `PILeanMathlib.Examples.RealFigures` is linked by `figure_proves` to a theorem
that names the function, the interval, the number of steps and the bound, pins the figure's title
and its one curve, and proves the bound: the polyline through the exact samples is vertically
within `delta` of the graph over the interval (`CertifiedPlot.Certifies`).

## Main results

* `expFigure_spec`: `exp` on `[-2, 2]`, 128 steps, within `1/1000`.
* `cosFigure_spec`: `cos` on `[-3, 3]`, 96 steps, within `1/2000`.
* `logFigure_spec`: `log` on `[1/2, 3/2]`, 64 steps, within `1/8000`.
* `arctanFigure_spec`: `arctan` on `[-3/4, 3/4]`, 48 steps, within `1/5000`.
* `sqrtFigure_spec`: `√` on `[1/4, 4]`, 120 steps, within `1/4000`.

Each bound is the error of the approximant at the grid points (at most about `10⁻⁵`) plus
`M h² / 8`, the error of joining the samples by segments where `|f''| ≤ M` on the whole interval;
the second term is most of it, and it is loose where `|f''|` is smaller than its maximum (the
exponential near `-2`, the logarithm near `3/2`, the square root near `4`).
-/

open Set
open scoped Nat

namespace PILeanMathlib.Examples

open PILean PILean.Plot PILeanMathlib

/-- **exp x within 1 / 1000.** The figure is the certified plot of `Real.exp` on `[-2, 2]` with 128
steps and the bound `1 / 1000`, as its title says; its one curve is the series of exact samples,
converted one by one; and the polyline through the exact samples is vertically within `1 / 1000` of
the graph of `Real.exp` over `[-2, 2]`. -/
theorem expFigure_spec :
    expFigure = expPlot.figure ∧ expPlot.name = "exp x" ∧
    expPlot.lo = -2 ∧ expPlot.hi = 2 ∧ expPlot.steps = 128 ∧ expPlot.delta = 1 / 1000 ∧
    expFigure.title =
      "exp x on [-2, 2] from \
      129 exact samples, within 1/1000 of the graph" ∧
    expFigure.panels.map (·.series) = #[#[expPlot.series]] ∧
    expPlot.series.points =
      ((Exact.samples expPlot.approx expPlot.lo expPlot.hi
        expPlot.steps).map Exact.toPoint).toArray ∧
    expPlot.Certifies Real.exp := by
  sorry

figure_proves expFigure expFigure_spec

/-- **cos x within 1 / 2000.** The figure is the certified plot of `Real.cos` on `[-3, 3]` with 96
steps and the bound `1 / 2000`, as its title says; its one curve is the series of exact samples,
converted one by one; and the polyline through the exact samples is vertically within `1 / 2000` of
the graph of `Real.cos` over `[-3, 3]`. -/
theorem cosFigure_spec :
    cosFigure = cosPlot.figure ∧ cosPlot.name = "cos x" ∧
    cosPlot.lo = -3 ∧ cosPlot.hi = 3 ∧ cosPlot.steps = 96 ∧ cosPlot.delta = 1 / 2000 ∧
    cosFigure.title =
      "cos x on [-3, 3] from \
      97 exact samples, within 1/2000 of the graph" ∧
    cosFigure.panels.map (·.series) = #[#[cosPlot.series]] ∧
    cosPlot.series.points =
      ((Exact.samples cosPlot.approx cosPlot.lo cosPlot.hi
        cosPlot.steps).map Exact.toPoint).toArray ∧
    cosPlot.Certifies Real.cos := by
  sorry

figure_proves cosFigure cosFigure_spec

/-- **log x within 1 / 8000.** The figure is the certified plot of `Real.log` on `[1 / 2, 3 / 2]`
with 64 steps and the bound `1 / 8000`, as its title says; its one curve is the series of exact
samples, converted one by one; and the polyline through the exact samples is vertically within `1 /
8000` of the graph of `Real.log` over `[1 / 2, 3 / 2]`. -/
theorem logFigure_spec :
    logFigure = logPlot.figure ∧ logPlot.name = "log x" ∧
    logPlot.lo = 1 / 2 ∧ logPlot.hi = 3 / 2 ∧ logPlot.steps = 64 ∧ logPlot.delta = 1 / 8000 ∧
    logFigure.title =
      "log x on [1/2, 3/2] from \
      65 exact samples, within 1/8000 of the graph" ∧
    logFigure.panels.map (·.series) = #[#[logPlot.series]] ∧
    logPlot.series.points =
      ((Exact.samples logPlot.approx logPlot.lo logPlot.hi
        logPlot.steps).map Exact.toPoint).toArray ∧
    logPlot.Certifies Real.log := by
  sorry

figure_proves logFigure logFigure_spec

/-- **arctan x within 1 / 5000.** The figure is the certified plot of `Real.arctan` on `[-3 / 4, 3 /
4]` with 48 steps and the bound `1 / 5000`, as its title says; its one curve is the series of exact
samples, converted one by one; and the polyline through the exact samples is vertically within `1 /
5000` of the graph of `Real.arctan` over `[-3 / 4, 3 / 4]`. -/
theorem arctanFigure_spec :
    arctanFigure = arctanPlot.figure ∧ arctanPlot.name = "arctan x" ∧
    arctanPlot.lo = -3 / 4 ∧ arctanPlot.hi = 3 / 4 ∧ arctanPlot.steps = 48 ∧
    arctanPlot.delta = 1 / 5000 ∧
    arctanFigure.title =
      "arctan x on [-3/4, 3/4] from \
      49 exact samples, within 1/5000 of the graph" ∧
    arctanFigure.panels.map (·.series) = #[#[arctanPlot.series]] ∧
    arctanPlot.series.points =
      ((Exact.samples arctanPlot.approx arctanPlot.lo arctanPlot.hi
        arctanPlot.steps).map Exact.toPoint).toArray ∧
    arctanPlot.Certifies Real.arctan := by
  sorry

figure_proves arctanFigure arctanFigure_spec

/-- **√x within 1 / 4000.** The figure is the certified plot of `Real.sqrt` on `[1 / 4, 4]` with 120
steps and the bound `1 / 4000`, as its title says; its one curve is the series of exact samples,
converted one by one; and the polyline through the exact samples is vertically within `1 / 4000` of
the graph of `Real.sqrt` over `[1 / 4, 4]`. -/
theorem sqrtFigure_spec :
    sqrtFigure = sqrtPlot.figure ∧ sqrtPlot.name = "√x" ∧
    sqrtPlot.lo = 1 / 4 ∧ sqrtPlot.hi = 4 ∧ sqrtPlot.steps = 120 ∧
    sqrtPlot.delta = 1 / 4000 ∧
    sqrtFigure.title =
      "√x on [1/4, 4] from \
      121 exact samples, within 1/4000 of the graph" ∧
    sqrtFigure.panels.map (·.series) = #[#[sqrtPlot.series]] ∧
    sqrtPlot.series.points =
      ((Exact.samples sqrtPlot.approx sqrtPlot.lo sqrtPlot.hi
        sqrtPlot.steps).map Exact.toPoint).toArray ∧
    sqrtPlot.Certifies Real.sqrt := by
  sorry

figure_proves sqrtFigure sqrtFigure_spec

end PILeanMathlib.Examples
