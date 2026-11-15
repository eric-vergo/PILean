/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import PILean.Exact
import PILeanMathlib.Interpolation
import PILeanMathlib.Polyline

/-!
# The plot of an exact function against a real function

PILean plots an exact function `g : ℚ → ℚ` on `[lo, hi]` with `n` steps as the polyline through
its exact samples `PILean.Exact.samples g lo hi n`: the points `(x, g x)` for `x` on the grid
`lo + k (hi - lo) / n`, `k = 0, …, n`. This file reads those samples as points of the real plane
and bounds the vertical distance from the polyline to the graph of a real function `f` that `g`
approximates at the grid points.

## Main definitions

* `PILean.Exact.realSamples g lo hi n`: the exact samples as points of `ℝ × ℝ`.
* `PILean.Exact.plot g lo hi n`: the polyline through them.

## Main results

* `PILean.Exact.isVerticallyWithin_plot`: if `|g x - f x| ≤ ε` at every grid point, `f` is
  continuous on `[lo, hi]` and twice differentiable on `(lo, hi)` with `|f''| ≤ M` there, then
  the polyline is vertically within `ε + M h² / 8` of the graph of `f` over `[lo, hi]`, where
  `h = (hi - lo) / n` is the step of the grid.

* `PILean.Exact.isVerticallyWithin_plot_of_deriv`: the same with `deriv f` and
  `deriv (deriv f)`.

The statement is about the exact samples, which are rational numbers. What PILean then does with
them (conversion to floating point, the axes, the rasteriser) is outside it.
-/

open Set

namespace PILean.Exact

/-- The exact samples of `g` on the grid of `n` steps from `lo` to `hi`, as points of the real
plane. -/
def realSamples (g : ℚ → ℚ) (lo hi : ℚ) (n : ℕ) : List (ℝ × ℝ) :=
  (samples g lo hi n).map fun p => ((p.1 : ℝ), (p.2 : ℝ))

/-- The plot of the exact function `g` on the grid of `n` steps from `lo` to `hi`, as a subset of
the real plane: the polyline through its exact samples. -/
def plot (g : ℚ → ℚ) (lo hi : ℚ) (n : ℕ) : Set (ℝ × ℝ) :=
  polyline (realSamples g lo hi n)

variable {g : ℚ → ℚ} {lo hi : ℚ} {n : ℕ}

/-- There are `n + 1` samples. -/
@[simp]
theorem length_realSamples (g : ℚ → ℚ) (lo hi : ℚ) (n : ℕ) :
    (realSamples g lo hi n).length = n + 1 := by
  simp [realSamples, samples_length]

/-- The `k`-th sample is the `k`-th grid point with the value of `g` there. -/
theorem getElem_realSamples (g : ℚ → ℚ) (lo hi : ℚ) (n k : ℕ)
    (h : k < (realSamples g lo hi n).length) :
    (realSamples g lo hi n)[k] = ((gridPoint lo hi n k : ℝ), (g (gridPoint lo hi n k) : ℝ)) := by
  simp [realSamples, samples, grid]

/-- The `k`-th grid point, as a real number, is `lo + k h` with `h = (hi - lo) / n`. -/
theorem cast_gridPoint (lo hi : ℚ) {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (gridPoint lo hi n k : ℝ) = lo + k * (((hi : ℝ) - lo) / n) := by
  rw [gridPoint_eq lo hi n k hn]
  push_cast
  rfl

/-- The `k`-th grid point, `k ≤ n`, is a point of the grid. -/
theorem gridPoint_mem_grid (lo hi : ℚ) {n k : ℕ} (hk : k ≤ n) :
    gridPoint lo hi n k ∈ grid lo hi n :=
  List.mem_map.2 ⟨k, List.mem_range.2 (Nat.lt_succ_of_le hk), rfl⟩

/-- The points of the grid from `lo` to `hi`, `lo ≤ hi`, lie in `[lo, hi]`. -/
theorem cast_mem_Icc_of_mem_grid {x : ℚ} (hn : 0 < n) (hlohi : lo ≤ hi) (hx : x ∈ grid lo hi n) :
    (x : ℝ) ∈ Icc (lo : ℝ) hi := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  have hk' : (k : ℝ) ≤ n := Nat.cast_le.2 (Nat.lt_succ_iff.1 (List.mem_range.1 hk))
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hd : 0 ≤ ((hi : ℝ) - lo) / n := div_nonneg (sub_nonneg.2 (Rat.cast_le.2 hlohi)) hn'.le
  have hnh : n * (((hi : ℝ) - lo) / n) = hi - lo := mul_div_cancel₀ _ hn'.ne'
  rw [cast_gridPoint lo hi hn]
  constructor
  · nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  · nlinarith

/-- **The plot of an exact function is near the graph of the real function it approximates.**
Let `g : ℚ → ℚ` be plotted on the grid of `n ≥ 1` steps from `lo` to `hi`, `lo < hi`, and let
`f : ℝ → ℝ` be continuous on `[lo, hi]` and twice differentiable on `(lo, hi)`, with derivative
`f'` and second derivative `f''` there, `|f''| ≤ M` on `(lo, hi)`. If `|g x - f x| ≤ ε` at every
point `x` of the grid, then the polyline through the exact samples of `g` is vertically within
`ε + M h² / 8` of the graph of `f` over `[lo, hi]`, where `h = (hi - lo) / n`: it lies over
`[lo, hi]`, has a point over every abscissa of `[lo, hi]`, and each of its points `(x, y)` has
`|y - f x| ≤ ε + M h² / 8`. -/
theorem isVerticallyWithin_plot {f f' f'' : ℝ → ℝ} {ε M : ℝ} (hn : 0 < n) (hlohi : lo < hi)
    (hf : ContinuousOn f (Icc (lo : ℝ) hi))
    (hf' : ∀ x ∈ Ioo (lo : ℝ) hi, HasDerivAt f (f' x) x)
    (hf'' : ∀ x ∈ Ioo (lo : ℝ) hi, HasDerivAt f' (f'' x) x)
    (hM : ∀ x ∈ Ioo (lo : ℝ) hi, |f'' x| ≤ M)
    (hg : ∀ x ∈ grid lo hi n, |(g x : ℝ) - f x| ≤ ε) :
    IsVerticallyWithin (plot g lo hi n) f (Icc (lo : ℝ) hi)
      (ε + M * (((hi : ℝ) - lo) / n) ^ 2 / 8) := by
  set h : ℝ := ((hi : ℝ) - lo) / n with hh
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hlohi' : (lo : ℝ) < hi := Rat.cast_lt.2 hlohi
  have hpos : 0 < h := div_pos (sub_pos.2 hlohi') hn'
  have hnh : n * h = hi - lo := mul_div_cancel₀ _ hn'.ne'
  -- the abscissae of the samples, and where they lie
  set X : ℕ → ℝ := fun k => lo + k * h with hX
  have hXsucc : ∀ k, X (k + 1) - X k = h := fun k => by simp only [hX]; push_cast; ring
  have hXlo : ∀ k, (lo : ℝ) ≤ X k := fun k => by
    simp only [hX]; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hXhi : ∀ k, k ≤ n → X k ≤ hi := fun k hk => by
    have : (k : ℝ) ≤ n := Nat.cast_le.2 hk
    simp only [hX]; nlinarith
  have hsample : ∀ (k : ℕ) (hk : k < (realSamples g lo hi n).length),
      (realSamples g lo hi n)[k] = (X k, (g (gridPoint lo hi n k) : ℝ)) := fun k hk => by
    rw [getElem_realSamples, cast_gridPoint lo hi hn]
  have hgk : ∀ k, k ≤ n → |(g (gridPoint lo hi n k) : ℝ) - f (X k)| ≤ ε := fun k hk => by
    have := hg _ (gridPoint_mem_grid lo hi hk)
    rwa [cast_gridPoint lo hi hn] at this
  -- a point of the `k`-th segment
  have key : ∀ z ∈ plot g lo hi n, z.1 ∈ Icc (lo : ℝ) hi ∧ |z.2 - f z.1| ≤ ε + M * h ^ 2 / 8 := by
    rintro z ⟨k, hk, hz⟩
    have hkn : k + 1 ≤ n := by simpa using hk
    rw [hsample k (Nat.lt_of_succ_lt hk), hsample (k + 1) hk] at hz
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    obtain rfl : a = 1 - b := by linarith
    have hb1 : b ≤ 1 := by linarith
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    have hx : (1 - b) * X k + b * X (k + 1) = X k + b * h := by
      linear_combination b * hXsucc k
    have hbh : 0 ≤ b * h := mul_nonneg hb hpos.le
    have hbh' : b * h ≤ h := mul_le_of_le_one_left hpos.le hb1
    have hlt : X k < X (k + 1) := by linarith [hXsucc k]
    have hsub : Icc (X k) (X (k + 1)) ⊆ Icc (lo : ℝ) hi :=
      Icc_subset_Icc (hXlo k) (hXhi _ hkn)
    have hsub' : Ioo (X k) (X (k + 1)) ⊆ Ioo (lo : ℝ) hi :=
      Ioo_subset_Ioo (hXlo k) (hXhi _ hkn)
    refine ⟨hsub ⟨by linarith, by linarith [hXsucc k]⟩, ?_⟩
    have hchord := abs_chord_sub_le hlt (hf.mono hsub) (fun x hx => hf' x (hsub' hx))
      (fun x hx => hf'' x (hsub' hx)) (fun x hx => hM x (hsub' hx)) (t := b) ⟨hb, hb1⟩
    rw [hXsucc k] at hchord
    have h1 := hgk k (Nat.le_of_succ_le hkn)
    have h2 := hgk (k + 1) hkn
    calc |(1 - b) * (g (gridPoint lo hi n k) : ℝ) + b * (g (gridPoint lo hi n (k + 1)) : ℝ)
          - f ((1 - b) * X k + b * X (k + 1))|
        = |(1 - b) * ((g (gridPoint lo hi n k) : ℝ) - f (X k))
            + b * ((g (gridPoint lo hi n (k + 1)) : ℝ) - f (X (k + 1)))
            + ((1 - b) * f (X k) + b * f (X (k + 1)) - f ((1 - b) * X k + b * X (k + 1)))| := by
          congr 1; ring
      _ ≤ (|1 - b| * |(g (gridPoint lo hi n k) : ℝ) - f (X k)|
            + |b| * |(g (gridPoint lo hi n (k + 1)) : ℝ) - f (X (k + 1))|) + M * h ^ 2 / 8 := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) hchord)
          rw [abs_mul, abs_mul]
      _ ≤ ((1 - b) * ε + b * ε) + M * h ^ 2 / 8 := by
          rw [abs_of_nonneg ha, abs_of_nonneg hb]
          gcongr
      _ = ε + M * h ^ 2 / 8 := by ring
  refine ⟨fun z hz => (key z hz).1, fun x hx => ?_, fun z hz => (key z hz).2⟩
  -- the segment over a given abscissa
  obtain ⟨k, hkn, hk1, hk2⟩ : ∃ k, k + 1 ≤ n ∧ X k ≤ x ∧ x ≤ X (k + 1) := by
    have hq : 0 ≤ (x - lo) / h := div_nonneg (sub_nonneg.2 hx.1) hpos.le
    rcases Nat.lt_or_ge ⌊(x - lo) / h⌋₊ n with hlt | hge
    · refine ⟨⌊(x - lo) / h⌋₊, hlt, ?_, ?_⟩
      · have := (le_div_iff₀ hpos).1 (Nat.floor_le hq)
        simp only [hX]; linarith
      · have := (div_lt_iff₀ hpos).1 (Nat.lt_floor_add_one ((x - lo) / h))
        simp only [hX]; push_cast; linarith
    · refine ⟨n - 1, by omega, ?_, ?_⟩
      · have h1 : (n : ℝ) ≤ (x - lo) / h := (Nat.cast_le.2 hge).trans (Nat.floor_le hq)
        have h2 := (le_div_iff₀ hpos).1 h1
        have h3 : ((n - 1 : ℕ) : ℝ) ≤ n := Nat.cast_le.2 (Nat.sub_le n 1)
        simp only [hX]; nlinarith
      · have : n - 1 + 1 = n := by omega
        rw [this]
        simp only [hX]; linarith [hx.2]
  have hk : k + 1 < (realSamples g lo hi n).length := by simpa using hkn
  set t : ℝ := (x - X k) / h with ht
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.2 hk1) hpos.le
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one hpos]; linarith [hXsucc k]
  have hth : t * h = x - X k := div_mul_cancel₀ _ hpos.ne'
  refine ⟨(1 - t) * (g (gridPoint lo hi n k) : ℝ) + t * (g (gridPoint lo hi n (k + 1)) : ℝ),
    k, hk, ?_⟩
  rw [hsample k (Nat.lt_of_succ_lt hk), hsample (k + 1) hk]
  refine ⟨1 - t, t, sub_nonneg.2 ht1, ht0, by ring, ?_⟩
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq, and_true]
  linear_combination (hXsucc k) * t + hth

/-- `isVerticallyWithin_plot` stated with `deriv`: `f` is continuous on `[lo, hi]` and
differentiable on `(lo, hi)`, its derivative `deriv f` is differentiable on `(lo, hi)`, and
`|deriv (deriv f)| ≤ M` there. -/
theorem isVerticallyWithin_plot_of_deriv {f : ℝ → ℝ} {ε M : ℝ} (hn : 0 < n) (hlohi : lo < hi)
    (hf : ContinuousOn f (Icc (lo : ℝ) hi)) (hf' : DifferentiableOn ℝ f (Ioo (lo : ℝ) hi))
    (hf'' : DifferentiableOn ℝ (deriv f) (Ioo (lo : ℝ) hi))
    (hM : ∀ x ∈ Ioo (lo : ℝ) hi, |deriv (deriv f) x| ≤ M)
    (hg : ∀ x ∈ grid lo hi n, |(g x : ℝ) - f x| ≤ ε) :
    IsVerticallyWithin (plot g lo hi n) f (Icc (lo : ℝ) hi)
      (ε + M * (((hi : ℝ) - lo) / n) ^ 2 / 8) :=
  isVerticallyWithin_plot hn hlohi hf
    (fun x hx => ((hf' x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt)
    (fun x hx => ((hf'' x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt) hM hg

/-- The hypotheses can be met: the exact function `x ↦ x * x` on the grid of 4 steps from `0` to
`1` against the real function `x ↦ x ^ 2`, with `ε = 0` and `M = 2`. The polyline is vertically
within `2 * (1 / 4) ^ 2 / 8 = 1 / 64` of the parabola. -/
example : IsVerticallyWithin (plot (fun x => x * x) 0 1 4) (fun x => x ^ 2) (Icc 0 1) (1 / 64) := by
  have h := isVerticallyWithin_plot (g := fun x => x * x) (lo := 0) (hi := 1) (n := 4)
    (f := fun x => x ^ 2) (f' := fun x => 2 * x) (f'' := fun _ => 2) (ε := 0) (M := 2)
    (by decide) (by decide +kernel) (by fun_prop) (fun x _ => by simpa using hasDerivAt_pow 2 x)
    (fun x _ => by simpa using (hasDerivAt_id' x).const_mul 2) (fun x _ => by simp)
    (fun x _ => by simp [sq])
  simp only [Rat.cast_zero, Rat.cast_one] at h
  exact h.mono (by norm_num)

end PILean.Exact
