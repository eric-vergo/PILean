/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import PILeanMathlib.CertifiedPlot
import PILeanMathlib.ExactPlot

/-!
# Certified plots of real functions: what the bound means and how to prove it

`CertifiedPlot.Certifies c f` says that the polyline through the exact samples of the approximant
of `c` is vertically within `c.delta` of the graph of `f : ℝ → ℝ` over `[c.lo, c.hi]`: it lies
over the interval, has a point over every abscissa of it, and each of its points `(x, y)` has
`|y - f x| ≤ c.delta` (`IsVerticallyWithin`). `CertifiedPlot.certifies_of` proves it from the
error `ε` of the approximant at the grid points, a bound `M` on `|f''|` and
`ε + M h² / 8 ≤ c.delta`, where `h` is the step of the grid (`Exact.isVerticallyWithin_plot`).

Three ways to bound `ε`, each with minimal hypotheses:

* `abs_sub_taylor_le`: Taylor's theorem at `0` with the Lagrange remainder, for a function with
  continuous derivatives of every order and a bound on the next derivative (the exponential, the
  cosine);
* `abs_arctan_sub_arctanSum_le`: the series of the arctangent to `n` terms differs from it by at
  most `r ^ (2 n) |x|` for `|x| ≤ r`, by the mean value theorem;
* `abs_sub_sqrt_le`: a rational `r ≥ 0` differs from `√x` by at most `|r² - x| / √x`, so a
  square checked by the kernel bounds the error of a square root.

The logarithm uses Mathlib's `Real.abs_log_sub_add_sum_range_le`.

## Main definitions

* `CertifiedPlot.Certifies`

## Main results

* `CertifiedPlot.certifies_of`, `abs_sub_taylor_le`, `abs_arctan_sub_arctanSum_le`,
  `abs_sub_sqrt_le`, `iteratedDeriv_exp_zero`, `exp_two_le`
-/

open Set
open scoped Nat

namespace PILeanMathlib

open PILean

/-- The polyline through the exact samples of the approximant is vertically within `delta` of
the graph of `f` over `[lo, hi]`. -/
def CertifiedPlot.Certifies (c : CertifiedPlot) (f : ℝ → ℝ) : Prop :=
  IsVerticallyWithin (Exact.plot c.approx c.lo c.hi c.steps) f (Icc (c.lo : ℝ) c.hi) c.delta

/-- **A certified plot from two bounds.** If the approximant is within `ε` of `f` at every grid
point, `f` is continuous on `[lo, hi]` and twice differentiable on `(lo, hi)` with `|f''| ≤ M`
there, and `ε + M h² / 8 ≤ delta` for the step `h = (hi - lo) / steps`, then the plot certifies
`f`. -/
theorem CertifiedPlot.certifies_of (c : CertifiedPlot) {f f' f'' : ℝ → ℝ} {ε M : ℝ}
    (hn : 0 < c.steps) (hlohi : c.lo < c.hi)
    (hf : ContinuousOn f (Icc (c.lo : ℝ) c.hi))
    (hf' : ∀ x ∈ Ioo (c.lo : ℝ) c.hi, HasDerivAt f (f' x) x)
    (hf'' : ∀ x ∈ Ioo (c.lo : ℝ) c.hi, HasDerivAt f' (f'' x) x)
    (hM : ∀ x ∈ Ioo (c.lo : ℝ) c.hi, |f'' x| ≤ M)
    (hg : ∀ x ∈ Exact.grid c.lo c.hi c.steps, |(c.approx x : ℝ) - f x| ≤ ε)
    (hδ : ε + M * (((c.hi : ℝ) - c.lo) / c.steps) ^ 2 / 8 ≤ c.delta) : c.Certifies f :=
  (Exact.isVerticallyWithin_plot hn hlohi hf hf' hf'' hM hg).mono hδ

/-- The grid points lie in `[lo, hi]`. -/
theorem CertifiedPlot.mem_Icc_of_mem_grid (c : CertifiedPlot) (hn : 0 < c.steps)
    (hlohi : c.lo ≤ c.hi) {x : ℚ} (hx : x ∈ Exact.grid c.lo c.hi c.steps) :
    (c.lo : ℝ) ≤ x ∧ (x : ℝ) ≤ c.hi :=
  Exact.cast_mem_Icc_of_mem_grid hn hlohi hx

/-- **Taylor's theorem at `0`** with a bound `B` on the `(n + 1)`-th derivative between `0` and
`x`, for a function with continuous derivatives of every order. -/
theorem abs_sub_taylor_le {f : ℝ → ℝ} (hf : ∀ m : ℕ, ContDiff ℝ m f) (n : ℕ) (x B : ℝ)
    (hB : ∀ y ∈ uIoo 0 x, |iteratedDeriv (n + 1) f y| ≤ B) :
    |f x - ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f 0 * x ^ k / k !| ≤
      B * |x| ^ (n + 1) / (n + 1)! := by
  rcases eq_or_ne 0 x with rfl | hx
  · rw [Finset.sum_range_succ']
    simp
  obtain ⟨ξ, hξ, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := n) hx
    (by exact_mod_cast (hf (n + 1)).contDiffOn)
  have hsum : taylorWithinEval f n (uIcc 0 x) 0 x =
      ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f 0 * x ^ k / k ! := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx) (hf k).contDiffAt
      left_mem_uIcc, sub_zero, smul_eq_mul]
    ring
  rw [← hsum, h, sub_zero, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  gcongr
  exact hB ξ hξ

/-- The derivatives of the exponential at `0` are `1`. -/
theorem iteratedDeriv_exp_zero (k : ℕ) : iteratedDeriv k Real.exp 0 = 1 := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.exp_zero]

/-- `e² ≤ 15/2`, from `e < 2.7182818286`. -/
theorem exp_two_le : Real.exp 2 ≤ 15 / 2 := by
  have h := Real.exp_one_lt_d9
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]
  nlinarith [Real.exp_pos 1]

/-- The partial sums `∑ i < n, (-1) ^ i y ^ (2 i + 1) / (2 i + 1)` of the arctangent's series, over
ℝ. -/
noncomputable def arctanSumR (n : ℕ) (y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, (-1) ^ i * y ^ (2 * i + 1) / (2 * i + 1)

/-- The derivative of the difference of the arctangent and its partial sum. -/
theorem hasDerivAt_arctan_sub_arctanSumR (n : ℕ) (y : ℝ) :
    HasDerivAt (fun y => Real.arctan y - arctanSumR n y) ((-y ^ 2) ^ n / (1 + y ^ 2)) y := by
  have hs : HasDerivAt (arctanSumR n) (∑ i ∈ Finset.range n, (-y ^ 2) ^ i) y := by
    unfold arctanSumR
    have : ∀ i ∈ Finset.range n, HasDerivAt (fun y : ℝ => (-1) ^ i * y ^ (2 * i + 1) / (2 * i + 1))
        ((-y ^ 2) ^ i) y := fun i _ => by
      have h := ((hasDerivAt_pow (2 * i + 1) y).const_mul ((-1 : ℝ) ^ i)).div_const
        (2 * (i : ℝ) + 1)
      convert h using 1
      have : (2 * (i : ℝ) + 1) ≠ 0 := by positivity
      rw [neg_pow, ← pow_mul]
      push_cast
      field_simp
    exact HasDerivAt.fun_sum this
  have h1 : (1 : ℝ) + y ^ 2 ≠ 0 := by positivity
  convert (Real.hasDerivAt_arctan y).sub hs using 1
  rw [geom_sum_eq (by nlinarith [sq_nonneg y] : -y ^ 2 ≠ 1),
    show -y ^ 2 - 1 = -(1 + y ^ 2) by ring]
  field_simp
  ring

/-- **The arctangent's series.** For `|x| ≤ r`, its partial sum to `n` terms differs from the
arctangent by at most `r ^ (2 n) |x|`. -/
theorem abs_arctan_sub_arctanSumR_le (n : ℕ) {x r : ℝ} (hx : |x| ≤ r) :
    |Real.arctan x - arctanSumR n x| ≤ r ^ (2 * n) * |x| := by
  have hr : 0 ≤ r := (abs_nonneg x).trans hx
  have hD : ∀ y ∈ Set.uIcc 0 x, |(-y ^ 2) ^ n / (1 + y ^ 2)| ≤ r ^ (2 * n) := by
    intro y hy
    have hy' : |y| ≤ r := by
      rcases le_total 0 x with h | h
      · rw [Set.uIcc_of_le h] at hy
        rw [abs_of_nonneg hy.1]; exact hy.2.trans (le_abs_self x |>.trans hx)
      · rw [Set.uIcc_of_ge h] at hy
        rw [abs_of_nonpos hy.2]; linarith [neg_le_abs x, hy.1]
    rw [abs_div, abs_pow, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 + y ^ 2), pow_mul]
    calc |y ^ 2| ^ n / (1 + y ^ 2) ≤ |y ^ 2| ^ n := div_le_self (by positivity) (by nlinarith)
      _ ≤ (r ^ 2) ^ n := by
        gcongr
        rw [abs_of_nonneg (sq_nonneg y)]
        nlinarith [abs_nonneg y, sq_abs y]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y => Real.arctan y - arctanSumR n y) (s := Set.uIcc 0 x)
    (fun y _ => (hasDerivAt_arctan_sub_arctanSumR n y).hasDerivWithinAt) (fun y hy => hD y hy)
    (convex_uIcc 0 x) Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [arctanSumR, Real.norm_eq_abs] using this

/-- A rational `r ≥ 0` is within `|r² - x| / √x` of the square root of `x > 0`. -/
theorem abs_sub_sqrt_le {r x : ℝ} (hr : 0 ≤ r) (hx : 0 < x) :
    |r - √x| ≤ |r ^ 2 - x| / √x := by
  have hs : 0 < √x := Real.sqrt_pos.2 hx
  rw [le_div_iff₀ hs]
  have e : r ^ 2 - x = (r - √x) * (r + √x) := by
    rw [show (r - √x) * (r + √x) = r ^ 2 - √x ^ 2 by ring, Real.sq_sqrt hx.le]
  rw [e, abs_mul, abs_of_pos (by positivity : 0 < r + √x)]
  gcongr
  linarith

end PILeanMathlib
