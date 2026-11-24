/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import PILean.Plot.Exact
import PILeanMathlib.ExactPlot
import PILeanMathlib.Examples.SineFigure

/-!
# A plot of the sine with a proved error bound: the theorem

`sineFigure` (in `PILeanMathlib.Examples.SineFigure`) plots the Taylor polynomial `sineTaylor`
of degree 15 on the grid of 96 steps from `-3` to `3`.

## Main results

* `PILeanMathlib.abs_sin_sub_taylor_le`: the sine differs from its Taylor polynomial of degree
  `n` at `0` by at most `|x| ^ (n + 1) / (n + 1)!`.
* `abs_sineTaylor_sub_sin_le`: on `[-3, 3]`, `sineTaylor` is within `3 ^ 17 / 17!` of the sine.
* `sineFigure_spec`: the figure's only series is `sineSeries`, its points are the exact samples
  of `sineTaylor` converted one by one, and the polyline through the exact samples is vertically
  within `1 / 2000` of the graph of the sine over `[-3, 3]`.

The bound `1 / 2000` is `3 ^ 17 / 17! + (1 / 16) ^ 2 / 8` rounded up: the error of the polynomial
at the grid points, and the error of joining samples `1 / 16` apart by straight segments when
the second derivative is at most `1` in absolute value.
-/

open Set
open scoped Nat

/-- The sine differs from its Taylor polynomial of degree `n` at `0` by at most
`|x| ^ (n + 1) / (n + 1)!`. -/
theorem PILeanMathlib.abs_sin_sub_taylor_le (n : ℕ) (x : ℝ) :
    |Real.sin x - ∑ k ∈ Finset.range (n + 1), iteratedDeriv k Real.sin 0 * x ^ k / k !| ≤
      |x| ^ (n + 1) / (n + 1)! := by
  rcases eq_or_ne 0 x with rfl | hx
  · rw [Finset.sum_range_succ']
    simp
  obtain ⟨ξ, -, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := n) hx
    Real.contDiff_sin.contDiffOn
  have hsum : taylorWithinEval Real.sin n (uIcc 0 x) 0 x =
      ∑ k ∈ Finset.range (n + 1), iteratedDeriv k Real.sin 0 * x ^ k / k ! := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx) Real.contDiff_sin.contDiffAt
      left_mem_uIcc, sub_zero, smul_eq_mul]
    ring
  rw [← hsum, h, sub_zero, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  gcongr
  exact mul_le_of_le_one_left (by positivity) (Real.abs_iteratedDeriv_sin_le_one _ _)

namespace PILeanMathlib.Examples

open PILean PILean.Plot

/-- `sineTaylor`, read in the real numbers, is the Taylor polynomial of the sine at `0` of
degree 16 (whose term of degree 16 vanishes). -/
theorem cast_sineTaylor (x : ℚ) :
    (sineTaylor x : ℝ) =
      ∑ k ∈ Finset.range 17, iteratedDeriv k Real.sin 0 * (x : ℝ) ^ k / k ! := by
  simp [Finset.sum_range_succ, sineTaylor, Nat.factorial]
  ring

/-- On `[-3, 3]` the polynomial `sineTaylor` is within `3 ^ 17 / 17!` of the sine. -/
theorem abs_sineTaylor_sub_sin_le {x : ℚ} (hx : |(x : ℝ)| ≤ 3) :
    |(sineTaylor x : ℝ) - Real.sin x| ≤ 3 ^ 17 / 17 ! := by
  rw [cast_sineTaylor, abs_sub_comm]
  refine (abs_sin_sub_taylor_le 16 x).trans ?_
  gcongr

/-- **The sine figure is within `1 / 2000` of the sine.** The figure `sineFigure` has its title
and one panel, with the axes `x` and `y`, linear and with no domain set, whose only series is
`sineSeries`, and no other setting. The points of `sineSeries` are the exact samples of the
polynomial `sineTaylor` on the grid of 96 steps from `-3` to `3`, converted one by one to floating
point; and the polyline through those exact samples, as a subset of the real plane, is vertically
within `1 / 2000` of the graph of the real sine over `[-3, 3]`: it lies over `[-3, 3]`, has a
point over every abscissa of `[-3, 3]`, and each of its points `(x, y)` has
`|y - sin x| ≤ 1 / 2000`.

The last statement is about the exact samples. The floating-point steps from them to the
picture are not part of it. -/
theorem sineFigure_spec :
    sineFigure = { title := "The sine from 97 exact samples", panels := #[{
      x := { label := "x", scale := .linear, domain := none },
      y := { label := "y", scale := .linear, domain := none },
      series := #[sineSeries] }] } ∧
    sineFigure.panels.map (·.series) = #[#[sineSeries]] ∧
    sineSeries.points = ((Exact.samples sineTaylor lo hi steps).map Exact.toPoint).toArray ∧
    IsVerticallyWithin (Exact.plot sineTaylor lo hi steps) Real.sin (Icc (-3) 3) (1 / 2000) := by
  refine ⟨rfl, by simp [sineFigure], Series.ofExact_points .., ?_⟩
  have hlo : ((lo : ℚ) : ℝ) = -3 := by norm_num [lo]
  have hhi : ((hi : ℚ) : ℝ) = 3 := by norm_num [hi]
  have h := Exact.isVerticallyWithin_plot (g := sineTaylor) (lo := lo) (hi := hi) (n := steps)
    (f := Real.sin) (f' := Real.cos) (f'' := fun x => -Real.sin x) (ε := 3 ^ 17 / 17 !) (M := 1)
    (by decide) (by decide +kernel) Real.continuous_sin.continuousOn
    (fun x _ => Real.hasDerivAt_sin x) (fun x _ => Real.hasDerivAt_cos x)
    (fun x _ => by simpa using Real.abs_sin_le_one x)
    (fun x hx => abs_sineTaylor_sub_sin_le ?_)
  · rw [hlo, hhi] at h
    exact h.mono (by norm_num [steps, Nat.factorial])
  · have := Exact.cast_mem_Icc_of_mem_grid (by decide) (by decide +kernel) hx
    rw [hlo, hhi] at this
    exact abs_le.2 this

figure_links sineFigure sineFigure_spec

/-- The points of `sineSeries`, a statement that does not name the figure. -/
theorem sineSeries_points :
    sineSeries.points = ((Exact.samples sineTaylor lo hi steps).map Exact.toPoint).toArray :=
  Series.ofExact_points ..

/--
error: the statement of PILeanMathlib.Examples.sineSeries_points does not mention the figure
PILeanMathlib.Examples.sineFigure. A theorem linked to a figure must be a statement about the
figure itself: state it of PILeanMathlib.Examples.sineFigure or of its fields (for instance,
begin with an equation that says which series, edges or frames PILeanMathlib.Examples.sineFigure
holds), not only of definitions it is built from
-/
#guard_msgs in
figure_links sineFigure sineSeries_points

/-- The statement has content: the same polyline is not vertically within `1 / 2000` of the graph
of the cosine, since its point `(0, 0)` (the sample of index 48) is at vertical distance `1`. -/
example :
    ¬ IsVerticallyWithin (Exact.plot sineTaylor lo hi steps) Real.cos (Icc (-3) 3) (1 / 2000) := by
  intro h
  have hmem : ((0 : ℝ), (0 : ℝ)) ∈ Exact.plot sineTaylor lo hi steps := by
    have h48 := getElem_mem_polyline (ps := Exact.realSamples sineTaylor lo hi steps)
      (by simp [steps]) (k := 48) (by simp [steps])
    have hx : Exact.gridPoint lo hi steps 48 = 0 := by decide +kernel
    have hy : sineTaylor 0 = 0 := by decide +kernel
    rwa [Exact.getElem_realSamples, hx, hy, Rat.cast_zero] at h48
  have := h.abs_sub_le _ hmem
  norm_num at this

end PILeanMathlib.Examples
