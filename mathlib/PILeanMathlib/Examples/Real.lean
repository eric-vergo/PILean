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

Each figure of `PILeanMathlib.Examples.RealFigures` is linked by `figure_links` to a theorem
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

/-- **The exponential within 1/1000.** The figure is the certified plot of `Real.exp` on `[-2, 2]`
with 128 steps and the bound `1/1000`, as its title says; its one panel has the axes `x` and `y`,
linear and with no domain set (so that they span the data), and one curve, the series of exact
samples of the Taylor polynomial of degree 15, converted one by one; and the polyline through the
exact samples is vertically within `1/1000` of the graph of `Real.exp` over `[-2, 2]`. -/
theorem expFigure_spec :
    expFigure = expPlot.figure ∧ expPlot.curve = "Taylor polynomial of degree 15" ∧
    expPlot.name = "exp x" ∧
    expPlot.lo = -2 ∧ expPlot.hi = 2 ∧ expPlot.steps = 128 ∧ expPlot.delta = 1 / 1000 ∧
    expFigure.title =
      "exp x on [−2, 2] from \
      129 exact samples, within 1/1000 of the graph" ∧
    expFigure = { title := expFigure.title, panels := #[{
      x := { label := "x", scale := .linear, domain := none },
      y := { label := "y", scale := .linear, domain := none },
      series := #[.ofExact expPlot.curve expPlot.approx expPlot.lo expPlot.hi expPlot.steps] }] } ∧
    expPlot.series.points =
      ((Exact.samples expPlot.approx expPlot.lo expPlot.hi
        expPlot.steps).map Exact.toPoint).toArray ∧
    expPlot.Certifies Real.exp := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide +kernel,
    rfl, Series.ofExact_points .., ?_⟩
  have hlo : ((expPlot.lo : ℚ) : ℝ) = -2 := by norm_num [expPlot]
  have hhi : ((expPlot.hi : ℚ) : ℝ) = 2 := by norm_num [expPlot]
  refine expPlot.certifies_of (f' := Real.exp) (f'' := Real.exp) (M := 15 / 2)
    (ε := 15 / 2 * 2 ^ 16 / 16 !) (by decide) (by decide +kernel)
    Real.continuous_exp.continuousOn (fun x _ => Real.hasDerivAt_exp x)
    (fun x _ => Real.hasDerivAt_exp x) (fun x hx => ?_) (fun x hx => ?_) ?_
  · rw [hlo, hhi] at hx
    rw [abs_of_pos (Real.exp_pos x)]
    exact (Real.exp_le_exp.2 hx.2.le).trans exp_two_le
  · have hx' := expPlot.mem_Icc_of_mem_grid (by decide) (by decide +kernel) hx
    rw [hlo, hhi] at hx'
    have hc : (expPlot.approx x : ℝ) =
        ∑ k ∈ Finset.range 16, iteratedDeriv k Real.exp 0 * (x : ℝ) ^ k / k ! := by
      simp [Finset.sum_range_succ, expPlot, expTaylor, iteratedDeriv_exp_zero, Nat.factorial]
    rw [hc, abs_sub_comm]
    refine (abs_sub_taylor_le (fun m => Real.contDiff_exp) 15 x (15 / 2) fun y hy => ?_).trans ?_
    · rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, abs_of_pos (Real.exp_pos y)]
      have : y ≤ 2 := by
        rcases le_total 0 (x : ℝ) with h | h
        · rw [uIoo_of_le h] at hy; linarith [hy.2]
        · rw [uIoo_of_ge h] at hy; linarith [hy.2]
      exact (Real.exp_le_exp.2 this).trans exp_two_le
    · gcongr
      exact abs_le.2 ⟨by linarith, by linarith⟩
  · rw [hlo, hhi]; norm_num [expPlot, Nat.factorial]

figure_links expFigure expFigure_spec

/-- **The cosine within 1/2000.** The figure is the certified plot of `Real.cos` on `[-3, 3]` with
96 steps and the bound `1/2000`, as its title says; its one panel has the axes `x` and `y`, linear
and with no domain set (so that they span the data), and one curve, the series of exact samples of
the Taylor polynomial of degree 16, converted one by one; and the polyline through the exact samples
is vertically within `1/2000` of the graph of `Real.cos` over `[-3, 3]`. -/
theorem cosFigure_spec :
    cosFigure = cosPlot.figure ∧ cosPlot.curve = "Taylor polynomial of degree 16" ∧
    cosPlot.name = "cos x" ∧
    cosPlot.lo = -3 ∧ cosPlot.hi = 3 ∧ cosPlot.steps = 96 ∧ cosPlot.delta = 1 / 2000 ∧
    cosFigure.title =
      "cos x on [−3, 3] from \
      97 exact samples, within 1/2000 of the graph" ∧
    cosFigure = { title := cosFigure.title, panels := #[{
      x := { label := "x", scale := .linear, domain := none },
      y := { label := "y", scale := .linear, domain := none },
      series := #[.ofExact cosPlot.curve cosPlot.approx cosPlot.lo cosPlot.hi cosPlot.steps] }] } ∧
    cosPlot.series.points =
      ((Exact.samples cosPlot.approx cosPlot.lo cosPlot.hi
        cosPlot.steps).map Exact.toPoint).toArray ∧
    cosPlot.Certifies Real.cos := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide +kernel,
    rfl, Series.ofExact_points .., ?_⟩
  have hlo : ((cosPlot.lo : ℚ) : ℝ) = -3 := by norm_num [cosPlot]
  have hhi : ((cosPlot.hi : ℚ) : ℝ) = 3 := by norm_num [cosPlot]
  refine cosPlot.certifies_of (f' := fun x => -Real.sin x) (f'' := fun x => -Real.cos x) (M := 1)
    (ε := 3 ^ 17 / 17 !) (by decide) (by decide +kernel) Real.continuous_cos.continuousOn
    (fun x _ => Real.hasDerivAt_cos x) (fun x _ => (Real.hasDerivAt_sin x).neg)
    (fun x _ => by simpa using Real.abs_cos_le_one x) (fun x hx => ?_) ?_
  · have hx' := cosPlot.mem_Icc_of_mem_grid (by decide) (by decide +kernel) hx
    rw [hlo, hhi] at hx'
    have hc : (cosPlot.approx x : ℝ) =
        ∑ k ∈ Finset.range 17, iteratedDeriv k Real.cos 0 * (x : ℝ) ^ k / k ! := by
      simp [Finset.sum_range_succ, cosPlot, cosTaylor, Nat.factorial]
      ring
    rw [hc, abs_sub_comm]
    refine (abs_sub_taylor_le (fun m => Real.contDiff_cos) 16 x 1
      fun y _ => Real.abs_iteratedDeriv_cos_le_one _ _).trans ?_
    rw [one_mul]
    gcongr
    exact abs_le.2 ⟨by linarith, by linarith⟩
  · rw [hlo, hhi]; norm_num [cosPlot, Nat.factorial]

figure_links cosFigure cosFigure_spec

/-- **The logarithm within 1/8000.** The figure is the certified plot of `Real.log` on `[1/2, 3/2]`
with 64 steps and the bound `1/8000`, as its title says; its one panel has the axes `x` and `y`,
linear and with no domain set (so that they span the data), and one curve, the series of exact
samples of 20 terms of the logarithm's series at `1`, converted one by one; and the polyline through
the exact samples is vertically within `1/8000` of the graph of `Real.log` over `[1/2, 3/2]`. -/
theorem logFigure_spec :
    logFigure = logPlot.figure ∧ logPlot.curve = "20 terms of its series at 1" ∧
    logPlot.name = "log x" ∧
    logPlot.lo = 1 / 2 ∧ logPlot.hi = 3 / 2 ∧ logPlot.steps = 64 ∧
    logPlot.delta = 1 / 8000 ∧
    logFigure.title =
      "log x on [1/2, 3/2] from \
      65 exact samples, within 1/8000 of the graph" ∧
    logFigure = { title := logFigure.title, panels := #[{
      x := { label := "x", scale := .linear, domain := none },
      y := { label := "y", scale := .linear, domain := none },
      series := #[.ofExact logPlot.curve logPlot.approx logPlot.lo logPlot.hi logPlot.steps] }] } ∧
    logPlot.series.points =
      ((Exact.samples logPlot.approx logPlot.lo logPlot.hi
        logPlot.steps).map Exact.toPoint).toArray ∧
    logPlot.Certifies Real.log := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide +kernel,
    rfl, Series.ofExact_points .., ?_⟩
  have hlo : ((logPlot.lo : ℚ) : ℝ) = 1 / 2 := by norm_num [logPlot]
  have hhi : ((logPlot.hi : ℚ) : ℝ) = 3 / 2 := by norm_num [logPlot]
  have hcast : ∀ (n : ℕ) (u : ℚ), (logSum n u : ℝ) =
      ∑ i ∈ Finset.range n, (u : ℝ) ^ (i + 1) / (i + 1) := by
    intro n u
    induction n with
    | zero => simp [logSum]
    | succ n ih => rw [logSum, Finset.sum_range_succ, ← ih]; push_cast; ring
  refine logPlot.certifies_of (f' := fun x => x⁻¹) (f'' := fun x => -(x ^ 2)⁻¹) (M := 4)
    (ε := (1 / 2) ^ 20) (by decide) (by decide +kernel) ?_ (fun x hx => ?_) (fun x hx => ?_)
    (fun x hx => ?_) (fun x hx => ?_) ?_
  · rw [hlo, hhi]
    exact Real.continuousOn_log.mono fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hx.1]
  · rw [hlo, hhi] at hx
    exact Real.hasDerivAt_log (by linarith [hx.1])
  · rw [hlo, hhi] at hx
    exact hasDerivAt_inv (by linarith [hx.1])
  · rw [hlo, hhi] at hx
    have h0 : 0 < x := by linarith [hx.1]
    rw [abs_neg, abs_of_pos (by positivity), inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith [hx.1]
  · have hx' := logPlot.mem_Icc_of_mem_grid (by decide) (by decide +kernel) hx
    rw [hlo, hhi] at hx'
    have hu : |(1 : ℝ) - x| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    have h := Real.abs_log_sub_add_sum_range_le (x := 1 - (x : ℝ)) (by linarith) 20
    rw [sub_sub_cancel] at h
    have e : (logPlot.approx x : ℝ) =
        -∑ i ∈ Finset.range 20, (1 - (x : ℝ)) ^ (i + 1) / (i + 1) := by
      simp only [logPlot, logApprox, Rat.cast_neg, hcast, Rat.cast_sub, Rat.cast_one]
    rw [e, show -∑ i ∈ Finset.range 20, (1 - (x : ℝ)) ^ (i + 1) / (i + 1) - Real.log x =
      -((∑ i ∈ Finset.range 20, (1 - (x : ℝ)) ^ (i + 1) / (i + 1)) + Real.log x) by ring, abs_neg]
    refine h.trans ?_
    calc |1 - (x : ℝ)| ^ (20 + 1) / (1 - |1 - (x : ℝ)|) ≤ (1 / 2) ^ 21 / (1 / 2) := by
          gcongr
          linarith
      _ = (1 / 2) ^ 20 := by norm_num
  · rw [hlo, hhi]; norm_num [logPlot]

figure_links logFigure logFigure_spec

/-- **The arctangent within 1/5000.** The figure is the certified plot of `Real.arctan` on `[-3/4,
3/4]` with 48 steps and the bound `1/5000`, as its title says; its one panel has the axes `x` and
`y`, linear and with no domain set (so that they span the data), and one curve, the series of exact
samples of 20 terms of the arctangent's series, converted one by one; and the polyline through the
exact samples is vertically within `1/5000` of the graph of `Real.arctan` over `[-3/4, 3/4]`. -/
theorem arctanFigure_spec :
    arctanFigure = arctanPlot.figure ∧ arctanPlot.curve = "20 terms of its series at 0" ∧
    arctanPlot.name = "arctan x" ∧
    arctanPlot.lo = -3 / 4 ∧ arctanPlot.hi = 3 / 4 ∧ arctanPlot.steps = 48 ∧
    arctanPlot.delta = 1 / 5000 ∧
    arctanFigure.title =
      "arctan x on [−3/4, 3/4] from \
      49 exact samples, within 1/5000 of the graph" ∧
    arctanFigure = { title := arctanFigure.title, panels := #[{
      x := { label := "x", scale := .linear, domain := none },
      y := { label := "y", scale := .linear, domain := none },
      series := #[.ofExact arctanPlot.curve arctanPlot.approx arctanPlot.lo arctanPlot.hi
        arctanPlot.steps] }] } ∧
    arctanPlot.series.points =
      ((Exact.samples arctanPlot.approx arctanPlot.lo arctanPlot.hi
        arctanPlot.steps).map Exact.toPoint).toArray ∧
    arctanPlot.Certifies Real.arctan := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide +kernel,
    rfl, Series.ofExact_points .., ?_⟩
  have hlo : ((arctanPlot.lo : ℚ) : ℝ) = -3 / 4 := by norm_num [arctanPlot]
  have hhi : ((arctanPlot.hi : ℚ) : ℝ) = 3 / 4 := by norm_num [arctanPlot]
  have hcast : ∀ (n : ℕ) (x : ℚ), (arctanSum n x : ℝ) = arctanSumR n x := by
    intro n x
    induction n with
    | zero => simp [arctanSum, arctanSumR]
    | succ n ih =>
      rw [arctanSum, arctanSumR, Finset.sum_range_succ, ← arctanSumR, ← ih]
      push_cast
      ring
  refine arctanPlot.certifies_of (f' := fun x => (1 + x ^ 2)⁻¹)
    (f'' := fun x => -(2 * x) / (1 + x ^ 2) ^ 2) (M := 1) (ε := (3 / 4) ^ 41) (by decide)
    (by decide +kernel) Real.continuous_arctan.continuousOn (fun x _ => ?_) (fun x _ => ?_)
    (fun x _ => ?_) (fun x hx => ?_) ?_
  · simpa [one_div] using Real.hasDerivAt_arctan x
  · have h := ((hasDerivAt_pow 2 x).const_add 1).inv (by positivity : (1 : ℝ) + x ^ 2 ≠ 0)
    convert h using 1
    simp
  · have h1 : 0 < 1 + x ^ 2 := by positivity
    rw [abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (1 + x ^ 2) ^ 2),
      div_le_one (by positivity)]
    rw [abs_mul, abs_two]
    nlinarith [abs_nonneg x, sq_abs x, sq_nonneg (|x| - 1), sq_nonneg x]
  · have hx' := arctanPlot.mem_Icc_of_mem_grid (by decide) (by decide +kernel) hx
    rw [hlo, hhi] at hx'
    have hax : |(x : ℝ)| ≤ 3 / 4 := abs_le.2 ⟨by linarith, by linarith⟩
    rw [show arctanPlot.approx = arctanSum 20 from rfl, hcast, abs_sub_comm]
    refine (abs_arctan_sub_arctanSumR_le 20 hax).trans ?_
    calc (3 / 4 : ℝ) ^ (2 * 20) * |(x : ℝ)| ≤ (3 / 4) ^ (2 * 20) * (3 / 4) := by gcongr
      _ = (3 / 4) ^ 41 := by norm_num
  · rw [hlo, hhi]; norm_num [arctanPlot]

figure_links arctanFigure arctanFigure_spec

/-- **The square root within 1/4000.** The figure is the certified plot of `Real.sqrt` on `[1/4, 4]`
with 120 steps and the bound `1/4000`, as its title says; its one panel has the axes `x` and `y`,
linear and with no domain set (so that they span the data), and one curve, the series of exact
samples of the square roots to 30 binary digits, converted one by one; and the polyline through the
exact samples is vertically within `1/4000` of the graph of `Real.sqrt` over `[1/4, 4]`. -/
theorem sqrtFigure_spec :
    sqrtFigure = sqrtPlot.figure ∧ sqrtPlot.curve = "square roots to 30 binary digits" ∧
    sqrtPlot.name = "√x" ∧
    sqrtPlot.lo = 1 / 4 ∧ sqrtPlot.hi = 4 ∧ sqrtPlot.steps = 120 ∧
    sqrtPlot.delta = 1 / 4000 ∧
    sqrtFigure.title =
      "√x on [1/4, 4] from \
      121 exact samples, within 1/4000 of the graph" ∧
    sqrtFigure = { title := sqrtFigure.title, panels := #[{
      x := { label := "x", scale := .linear, domain := none },
      y := { label := "y", scale := .linear, domain := none },
      series := #[.ofExact sqrtPlot.curve sqrtPlot.approx sqrtPlot.lo sqrtPlot.hi
        sqrtPlot.steps] }] } ∧
    sqrtPlot.series.points =
      ((Exact.samples sqrtPlot.approx sqrtPlot.lo sqrtPlot.hi
        sqrtPlot.steps).map Exact.toPoint).toArray ∧
    sqrtPlot.Certifies Real.sqrt := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide +kernel,
    rfl, Series.ofExact_points .., ?_⟩
  have hlo : ((sqrtPlot.lo : ℚ) : ℝ) = 1 / 4 := by norm_num [sqrtPlot]
  have hhi : ((sqrtPlot.hi : ℚ) : ℝ) = 4 := by norm_num [sqrtPlot]
  have hcheck : (Exact.grid sqrtPlot.lo sqrtPlot.hi sqrtPlot.steps).all (fun x =>
      0 ≤ sqrtApprox x && sqrtApprox x ^ 2 - x ≤ 1 / 10 ^ 8 &&
        x - sqrtApprox x ^ 2 ≤ 1 / 10 ^ 8) = true := by
    decide +kernel
  have hs : ∀ x : ℝ, 1 / 4 ≤ x → 1 / 2 ≤ √x := fun x hx =>
    Real.le_sqrt_of_sq_le (by linarith)
  refine sqrtPlot.certifies_of (f' := fun x => (2 * √x)⁻¹)
    (f'' := fun x => -(2 * (1 / (2 * √x))) / (2 * √x) ^ 2) (M := 2) (ε := 2 / 10 ^ 8)
    (by decide) (by decide +kernel) Real.continuous_sqrt.continuousOn (fun x hx => ?_)
    (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_) ?_
  · rw [hlo, hhi] at hx
    simpa [one_div] using Real.hasDerivAt_sqrt (by linarith [hx.1] : x ≠ 0)
  · rw [hlo, hhi] at hx
    have h2 : 2 * √x ≠ 0 := by have := hs x hx.1.le; positivity
    exact ((Real.hasDerivAt_sqrt (by linarith [hx.1] : x ≠ 0)).const_mul 2).inv h2
  · rw [hlo, hhi] at hx
    have h0 : 0 < x := by linarith [hx.1]
    have hsx := hs x hx.1.le
    have e : -(2 * (1 / (2 * √x))) / (2 * √x) ^ 2 = -(1 / (4 * x * √x)) := by
      have : √x ^ 2 = x := Real.sq_sqrt h0.le
      field_simp
      rw [this]
      ring
    rw [e, abs_neg, abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
    nlinarith [hx.1]
  · have hx' := sqrtPlot.mem_Icc_of_mem_grid (by decide) (by decide +kernel) hx
    rw [hlo, hhi] at hx'
    have hc := List.all_eq_true.1 hcheck x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨h0, h1⟩, h2⟩ := hc
    have hpos : (0 : ℝ) < x := by linarith
    refine (abs_sub_sqrt_le (by exact_mod_cast h0) hpos).trans ?_
    rw [div_le_iff₀ (Real.sqrt_pos.2 hpos)]
    have hsq : |(sqrtApprox x : ℝ) ^ 2 - x| ≤ 1 / 10 ^ 8 := by
      rw [abs_le]
      constructor
      · have : ((x - sqrtApprox x ^ 2 : ℚ) : ℝ) ≤ ((1 / 10 ^ 8 : ℚ) : ℝ) := by exact_mod_cast h2
        push_cast at this; linarith
      · have : ((sqrtApprox x ^ 2 - x : ℚ) : ℝ) ≤ ((1 / 10 ^ 8 : ℚ) : ℝ) := by exact_mod_cast h1
        push_cast at this; linarith
    have := hs x hx'.1
    change |((sqrtApprox x : ℚ) : ℝ) ^ 2 - x| ≤ 2 / 10 ^ 8 * √x
    linarith
  · rw [hlo, hhi]; norm_num [sqrtPlot]

figure_links sqrtFigure sqrtFigure_spec

end PILeanMathlib.Examples
