/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# The error of linear interpolation

A function on an interval `[u, v]` and the chord through the two ends of its graph. If the
function is continuous on `[u, v]`, twice differentiable on the open interval `(u, v)`, and its
second derivative is bounded there by `M` in absolute value, then the chord is within
`M (v - u)² / 8` of the function at every point of the interval.

The hypotheses name the derivatives: `f'` is a derivative of `f` and `f''` a derivative of `f'` at
every point of the open interval (`HasDerivAt`). Nothing is assumed at the two ends beyond the
continuity of `f`, and `f'` need not be continuous at the ends.

## Main results

* `exists_chord_sub_eq`: the error at an interior point is `f'' ξ / 2 * (x - u) * (v - x)` for
  some `ξ` in the open interval.
* `abs_chord_sub_le`: the error is at most `M * (v - u) ^ 2 / 8`.
* `abs_chord_sub_le_of_deriv`: the same with `deriv f` and `deriv (deriv f)`.

## Implementation notes

The proof is the classical one: the function `f` minus the chord minus a multiple of
`(s - u) (s - v)` chosen to vanish at `x` vanishes at `u`, `x` and `v`; by Rolle's theorem its
derivative vanishes twice and its second derivative once.
-/

open Set

namespace PILean

variable {f f' f'' : ℝ → ℝ} {u v M : ℝ}

/-- **The error of linear interpolation**, with the second derivative at an intermediate point.
For `f` continuous on `[u, v]` and twice differentiable on `(u, v)`, the chord through
`(u, f u)` and `(v, f v)`, taken at the point `x = (1 - t) u + t v` with `0 < t < 1`, exceeds
`f x` by `f'' ξ / 2 * (x - u) * (v - x)` for some `ξ` in `(u, v)`. -/
theorem exists_chord_sub_eq (huv : u < v) (hf : ContinuousOn f (Icc u v))
    (hf' : ∀ x ∈ Ioo u v, HasDerivAt f (f' x) x)
    (hf'' : ∀ x ∈ Ioo u v, HasDerivAt f' (f'' x) x) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ ξ ∈ Ioo u v, (1 - t) * f u + t * f v - f ((1 - t) * u + t * v) =
      f'' ξ / 2 * (t * (1 - t) * (v - u) ^ 2) := by
  obtain ⟨ht0, ht1⟩ := ht
  have hvu : 0 < v - u := sub_pos.2 huv
  set x : ℝ := (1 - t) * u + t * v with hx
  have hxu : x - u = t * (v - u) := by rw [hx]; ring
  have hvx : v - x = (1 - t) * (v - u) := by rw [hx]; ring
  have hux : u < x := sub_pos.1 (hxu ▸ mul_pos ht0 hvu)
  have hxv : x < v := sub_pos.1 (hvx ▸ mul_pos (sub_pos.2 ht1) hvu)
  -- the slope of the chord, and the multiple `K` of `(s - u) (s - v)` that makes `φ x = 0`
  set c : ℝ := (f v - f u) / (v - u) with hc
  set K : ℝ := (f x - f u - c * (x - u)) / ((x - u) * (x - v)) with hK
  have hden : (x - u) * (x - v) ≠ 0 :=
    mul_ne_zero (sub_pos.2 hux).ne' (sub_neg.2 hxv).ne
  set φ : ℝ → ℝ := fun s => f s - f u - c * (s - u) - K * ((s - u) * (s - v)) with hφ
  set φ' : ℝ → ℝ := fun s => f' s - c - K * (2 * s - u - v) with hφ'
  have hφu : φ u = 0 := by simp [hφ]
  have hφv : φ v = 0 := by
    have : c * (v - u) = f v - f u := div_mul_cancel₀ _ hvu.ne'
    simp only [hφ, sub_self, mul_zero, sub_zero]
    linarith
  have hφx : φ x = 0 := by
    have : K * ((x - u) * (x - v)) = f x - f u - c * (x - u) := div_mul_cancel₀ _ hden
    simp only [hφ]
    linarith
  have hφc : ContinuousOn φ (Icc u v) := by
    simp only [hφ]
    fun_prop
  have hφd : ∀ s ∈ Ioo u v, HasDerivAt φ (φ' s) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => c * (s - u)) c s := by
      simpa using ((hasDerivAt_id' s).sub_const u).const_mul c
    have h2 : HasDerivAt (fun s : ℝ => K * ((s - u) * (s - v))) (K * (2 * s - u - v)) s := by
      have h := (((hasDerivAt_id' s).sub_const u).mul ((hasDerivAt_id' s).sub_const v)).const_mul K
      exact h.congr_deriv (by ring)
    exact (((hf' s hs).sub_const (f u)).sub h1).sub h2
  have hφ'd : ∀ s ∈ Ioo u v, HasDerivAt φ' (f'' s - 2 * K) s := by
    intro s hs
    have h2 : HasDerivAt (fun s : ℝ => K * (2 * s - u - v)) (2 * K) s := by
      have h := ((((hasDerivAt_id' s).const_mul 2).sub_const u).sub_const v).const_mul K
      exact h.congr_deriv (by ring)
    exact ((hf'' s hs).sub_const c).sub h2
  -- Rolle's theorem on `[u, x]` and on `[x, v]`, then on the interval between the two points
  obtain ⟨ξ₁, hξ₁, h₁⟩ := exists_hasDerivAt_eq_zero hux
    (hφc.mono (Icc_subset_Icc_right hxv.le)) (hφu.trans hφx.symm)
    fun s hs => hφd s ⟨hs.1, hs.2.trans hxv⟩
  obtain ⟨ξ₂, hξ₂, h₂⟩ := exists_hasDerivAt_eq_zero hxv
    (hφc.mono (Icc_subset_Icc_left hux.le)) (hφx.trans hφv.symm)
    fun s hs => hφd s ⟨hux.trans hs.1, hs.2⟩
  have hsub : Icc ξ₁ ξ₂ ⊆ Ioo u v := fun s hs =>
    ⟨hξ₁.1.trans_le hs.1, hs.2.trans_lt hξ₂.2⟩
  obtain ⟨ξ, hξ, h⟩ := exists_hasDerivAt_eq_zero (hξ₁.2.trans hξ₂.1)
    (fun s hs => (hφ'd s (hsub hs)).continuousAt.continuousWithinAt) (h₁.trans h₂.symm)
    fun s hs => hφ'd s (hsub (Ioo_subset_Icc_self hs))
  refine ⟨ξ, hsub (Ioo_subset_Icc_self hξ), ?_⟩
  have hfξ : f'' ξ = 2 * K := by linarith
  have hKx : K * ((x - u) * (x - v)) = f x - f u - c * (x - u) := div_mul_cancel₀ _ hden
  have hcv : c * (v - u) = f v - f u := div_mul_cancel₀ _ hvu.ne'
  have hcx : c * (x - u) = t * (f v - f u) := by rw [hxu]; linear_combination t * hcv
  have hxv' : x - v = -((1 - t) * (v - u)) := by rw [← hvx]; ring
  rw [hfξ]
  rw [hcx, hxu, hxv'] at hKx
  linear_combination hKx

/-- **The error of linear interpolation.** Let `f` be continuous on `[u, v]` and twice
differentiable on `(u, v)`, with first derivative `f'` and second derivative `f''` there, and
`|f''| ≤ M` on `(u, v)`. Then at every point `(1 - t) u + t v` of the interval, `0 ≤ t ≤ 1`, the
chord through `(u, f u)` and `(v, f v)` is within `M (v - u)² / 8` of `f`. -/
theorem abs_chord_sub_le (huv : u < v) (hf : ContinuousOn f (Icc u v))
    (hf' : ∀ x ∈ Ioo u v, HasDerivAt f (f' x) x)
    (hf'' : ∀ x ∈ Ioo u v, HasDerivAt f' (f'' x) x) (hM : ∀ x ∈ Ioo u v, |f'' x| ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |(1 - t) * f u + t * f v - f ((1 - t) * u + t * v)| ≤ M * (v - u) ^ 2 / 8 := by
  have hM0 : 0 ≤ M :=
    (abs_nonneg _).trans (hM ((u + v) / 2) ⟨by linarith, by linarith⟩)
  have hbound : 0 ≤ M * (v - u) ^ 2 / 8 := by positivity
  rcases eq_or_lt_of_le ht.1 with rfl | ht0
  · simpa using hbound
  rcases eq_or_lt_of_le ht.2 with rfl | ht1
  · simpa using hbound
  obtain ⟨ξ, hξ, h⟩ := exists_chord_sub_eq huv hf hf' hf'' ⟨ht0, ht1⟩
  have ht' : 0 ≤ t * (1 - t) := mul_nonneg ht0.le (sub_nonneg.2 ht1.le)
  have h4 : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
  rw [h, abs_mul, abs_div, abs_two, abs_of_nonneg (mul_nonneg ht' (sq_nonneg _))]
  calc |f'' ξ| / 2 * (t * (1 - t) * (v - u) ^ 2)
      ≤ M / 2 * (1 / 4 * (v - u) ^ 2) := by
        gcongr
        exact hM ξ hξ
    _ = M * (v - u) ^ 2 / 8 := by ring

/-- **The error of linear interpolation**, stated with `deriv`. Let `f` be continuous on
`[u, v]` and differentiable on `(u, v)`, let its derivative `deriv f` be differentiable on
`(u, v)`, and let `|deriv (deriv f)| ≤ M` there. Then at every point `(1 - t) u + t v` of the
interval, `0 ≤ t ≤ 1`, the chord through `(u, f u)` and `(v, f v)` is within `M (v - u)² / 8` of
`f`. -/
theorem abs_chord_sub_le_of_deriv (huv : u < v) (hf : ContinuousOn f (Icc u v))
    (hf' : DifferentiableOn ℝ f (Ioo u v)) (hf'' : DifferentiableOn ℝ (deriv f) (Ioo u v))
    (hM : ∀ x ∈ Ioo u v, |deriv (deriv f) x| ≤ M) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |(1 - t) * f u + t * f v - f ((1 - t) * u + t * v)| ≤ M * (v - u) ^ 2 / 8 :=
  abs_chord_sub_le huv hf
    (fun x hx => ((hf' x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt)
    (fun x hx => ((hf'' x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt) hM ht

/-- The hypotheses can be met, and the constant `1 / 8` cannot be improved: for `f x = x ^ 2` on
`[0, 1]`, where `f'' = 2`, the chord exceeds `f` at the midpoint by `2 * (1 - 0) ^ 2 / 8`. -/
example : |(1 - 1 / 2) * (0 : ℝ) ^ 2 + 1 / 2 * (1 : ℝ) ^ 2 - ((1 - 1 / 2) * 0 + 1 / 2 * 1) ^ 2| ≤
      2 * (1 - 0) ^ 2 / 8 ∧
    |(1 - 1 / 2) * (0 : ℝ) ^ 2 + 1 / 2 * (1 : ℝ) ^ 2 - ((1 - 1 / 2) * 0 + 1 / 2 * 1) ^ 2| =
      2 * (1 - 0) ^ 2 / 8 := by
  refine ⟨abs_chord_sub_le (f := fun x => x ^ 2) (f' := fun x => 2 * x) (f'' := fun _ => 2)
    one_pos (by fun_prop) (fun x _ => ?_) (fun x _ => ?_) (fun x _ => by simp)
    ⟨by norm_num, by norm_num⟩, by norm_num⟩
  · simpa using hasDerivAt_pow 2 x
  · simpa using (hasDerivAt_id' x).const_mul 2

end PILean
