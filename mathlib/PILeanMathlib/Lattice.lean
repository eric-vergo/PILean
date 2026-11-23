/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Mathlib.Data.List.ProdSigma
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic
import PILean.Diagram.Lattice

/-!
# Lattices in the plane bound to Mathlib

A `PlaneLattice` of independent periods `ω₁, ω₂` draws exactly the points of the lattice
`ℤ ω₁ + ℤ ω₂` (`Submodule.span ℤ {ω₁, ω₂}` in `ℚ × ℚ`) that lie in its window, each once.

## Main results

* `PlaneLattice.natAbs_le_bound`: every lattice point in the window has coefficients within
  `bound`, so the candidates the figure considers include all of them.
* `PlaneLattice.mem_points_iff`: a pair of coefficients is drawn exactly when its point is in the
  window.
* `PlaneLattice.mem_dots_iff`: a faithful figure's dots are exactly the points of
  `Submodule.span ℤ {ω₁, ω₂}` in the window.
* `PlaneLattice.nodup_dots`: no point is drawn twice.
-/

namespace PILean.Diagram

/-- `qabs` is the absolute value. -/
theorem PlaneLattice.qabs_eq (q : ℚ) : PlaneLattice.qabs q = |q| := by
  unfold PlaneLattice.qabs
  split_ifs with h
  · exact (abs_of_neg h).symm
  · exact (abs_of_nonneg (not_lt.1 h)).symm

/-- Every lattice point in the window has coefficients within `bound`. -/
theorem PlaneLattice.natAbs_le_bound (Λ : PlaneLattice) (hdet : Λ.det ≠ 0) (m n : ℤ)
    (hw : Λ.inWindow (Λ.at_ m n) = true) : m.natAbs ≤ Λ.bound ∧ n.natAbs ≤ Λ.bound := by
  simp only [PlaneLattice.inWindow, PlaneLattice.at_, Bool.and_eq_true] at hw
  obtain ⟨⟨⟨hx1, hx2⟩, hy1⟩, hy2⟩ := hw
  replace hx1 := of_decide_eq_true hx1
  replace hx2 := of_decide_eq_true hx2
  replace hy1 := of_decide_eq_true hy1
  replace hy2 := of_decide_eq_true hy2
  set x := (m : ℚ) * Λ.w1.1 + n * Λ.w2.1 with hx
  set y := (m : ℚ) * Λ.w1.2 + n * Λ.w2.2 with hy
  set X := max |Λ.lo.1| |Λ.hi.1|
  set Y := max |Λ.lo.2| |Λ.hi.2|
  have hX : |x| ≤ X := abs_le.2 ⟨by
    have := le_max_left |Λ.lo.1| |Λ.hi.1|; have := neg_abs_le Λ.lo.1; linarith, by
    have := le_max_right |Λ.lo.1| |Λ.hi.1|; have := le_abs_self Λ.hi.1; linarith⟩
  have hY : |y| ≤ Y := abs_le.2 ⟨by
    have := le_max_left |Λ.lo.2| |Λ.hi.2|; have := neg_abs_le Λ.lo.2; linarith, by
    have := le_max_right |Λ.lo.2| |Λ.hi.2|; have := le_abs_self Λ.hi.2; linarith⟩
  have hd : 0 < |Λ.det| := abs_pos.2 hdet
  have em : (m : ℚ) * Λ.det = x * Λ.w2.2 - y * Λ.w2.1 := by
    simp only [hx, hy, PlaneLattice.det]; ring
  have en : (n : ℚ) * Λ.det = y * Λ.w1.1 - x * Λ.w1.2 := by
    simp only [hx, hy, PlaneLattice.det]; ring
  have bm : |(m : ℚ)| ≤ (|Λ.w2.2| * X + |Λ.w2.1| * Y) / |Λ.det| := by
    rw [le_div_iff₀ hd, ← abs_mul, em]
    calc |x * Λ.w2.2 - y * Λ.w2.1| ≤ |x * Λ.w2.2| + |y * Λ.w2.1| := abs_sub _ _
      _ = |Λ.w2.2| * |x| + |Λ.w2.1| * |y| := by rw [abs_mul, abs_mul]; ring
      _ ≤ |Λ.w2.2| * X + |Λ.w2.1| * Y := by gcongr
  have bn : |(n : ℚ)| ≤ (|Λ.w1.1| * Y + |Λ.w1.2| * X) / |Λ.det| := by
    rw [le_div_iff₀ hd, ← abs_mul, en]
    calc |y * Λ.w1.1 - x * Λ.w1.2| ≤ |y * Λ.w1.1| + |x * Λ.w1.2| := abs_sub _ _
      _ = |Λ.w1.1| * |y| + |Λ.w1.2| * |x| := by rw [abs_mul, abs_mul]; ring
      _ ≤ |Λ.w1.1| * Y + |Λ.w1.2| * X := by gcongr
  have key : ∀ k : ℤ, |(k : ℚ)| ≤ max ((|Λ.w2.2| * X + |Λ.w2.1| * Y) / |Λ.det|)
      ((|Λ.w1.1| * Y + |Λ.w1.2| * X) / |Λ.det|) → k.natAbs ≤ Λ.bound := by
    intro k hk
    unfold PlaneLattice.bound
    simp only [PlaneLattice.qabs_eq, abs_eq_zero, hdet, ite_false]
    change k.natAbs ≤ (max ((|Λ.w2.2| * X + |Λ.w2.1| * Y) / |Λ.det|)
        ((|Λ.w1.1| * Y + |Λ.w1.2| * X) / |Λ.det|)).ceil.toNat
    have h1 : ((k.natAbs : ℤ) : ℚ) ≤ ((max ((|Λ.w2.2| * X + |Λ.w2.1| * Y) / |Λ.det|)
        ((|Λ.w1.1| * Y + |Λ.w1.2| * X) / |Λ.det|)).ceil : ℚ) := by
      rw [Int.natCast_natAbs, Int.cast_abs]
      exact le_trans hk Rat.le_ceil
    have h2 := Int.cast_le.1 h1
    omega
  exact ⟨key m (le_max_of_le_left bm), key n (le_max_of_le_right bn)⟩

/-- A pair of coefficients is drawn exactly when its point is in the window (for independent
periods). -/
theorem PlaneLattice.mem_points_iff (Λ : PlaneLattice) (hdet : Λ.det ≠ 0) (m n : ℤ) :
    (m, n) ∈ Λ.points ↔ Λ.inWindow (Λ.at_ m n) = true := by
  rw [PlaneLattice.mem_points]
  exact ⟨fun h => h.2.2, fun h => ⟨(Λ.natAbs_le_bound hdet m n h).1,
    (Λ.natAbs_le_bound hdet m n h).2, h⟩⟩

/-- The point `m ω₁ + n ω₂` is the lattice combination with those coefficients. -/
theorem PlaneLattice.at_eq (Λ : PlaneLattice) (m n : ℤ) : Λ.at_ m n = m • Λ.w1 + n • Λ.w2 := by
  simp [PlaneLattice.at_, Prod.ext_iff, zsmul_eq_mul]

/-- For independent periods, distinct coefficients give distinct points. -/
theorem PlaneLattice.at_injective (Λ : PlaneLattice) (hdet : Λ.det ≠ 0) {m n m' n' : ℤ}
    (h : Λ.at_ m n = Λ.at_ m' n') : m = m' ∧ n = n' := by
  simp only [PlaneLattice.at_, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have em : ((m : ℚ) - m') * Λ.det = 0 := by
    simp only [PlaneLattice.det]; linear_combination Λ.w2.2 * h1 - Λ.w2.1 * h2
  have en : ((n : ℚ) - n') * Λ.det = 0 := by
    simp only [PlaneLattice.det]; linear_combination Λ.w1.1 * h2 - Λ.w1.2 * h1
  rcases mul_eq_zero.1 em with hm | hm
  · rcases mul_eq_zero.1 en with hn | hn
    · exact ⟨by exact_mod_cast sub_eq_zero.1 hm, by exact_mod_cast sub_eq_zero.1 hn⟩
    · exact absurd hn hdet
  · exact absurd hm hdet

/-- The candidates are distinct. -/
theorem PlaneLattice.candidates_nodup (Λ : PlaneLattice) : Λ.candidates.Nodup := by
  have hr : ((List.range (2 * Λ.bound + 1)).map fun (i : ℕ) => (i : ℤ) - Λ.bound).Nodup :=
    List.nodup_range.map fun a b h => by simpa using h
  exact hr.product hr

/-- **The drawn points are the lattice points in the window.** In a faithful figure of a lattice
of independent periods, a point is drawn (in some colour, at some position of the list) exactly
when it lies in `Submodule.span ℤ {ω₁, ω₂}` and in the window. -/
theorem PlaneLattice.mem_dots_iff (Λ : PlaneLattice) (hdet : Λ.det ≠ 0) {d : Diagram}
    (h : Λ.Faithful d) (p : ℚ × ℚ) :
    (∃ i col, (i, p, col) ∈ d.dots) ↔
      p ∈ Submodule.span ℤ {Λ.w1, Λ.w2} ∧ Λ.inWindow p = true := by
  rw [h.1, Submodule.mem_span_pair]
  simp only [List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨i, col, ⟨⟨m, n⟩, j⟩, hmem, rfl, rfl, rfl⟩
    have hp := List.fst_mem_of_mem_zipIdx hmem
    exact ⟨⟨m, n, (Λ.at_eq m n).symm⟩, (Λ.mem_points_iff hdet m n).1 hp⟩
  · rintro ⟨⟨m, n, rfl⟩, hw⟩
    rw [← Λ.at_eq] at hw ⊢
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ((Λ.mem_points_iff hdet m n).2 hw)
    exact ⟨k, Λ.pointInk m n, ((m, n), k), List.mk_mem_zipIdx_iff_getElem?.2 hk, rfl, rfl, rfl⟩

/-- **Each lattice point is drawn once.** The positions of a faithful figure's dots are
distinct. -/
theorem PlaneLattice.nodup_dots (Λ : PlaneLattice) (hdet : Λ.det ≠ 0) {d : Diagram}
    (h : Λ.Faithful d) : (d.dots.map (·.2.1)).Nodup := by
  rw [h.1, List.map_map]
  have hp : Λ.points.Nodup := Λ.candidates_nodup.filter _
  have e : (Λ.points.zipIdx.map ((·.2.1) ∘ fun x : (ℤ × ℤ) × ℕ =>
      (x.2, Λ.at_ x.1.1 x.1.2, Λ.pointInk x.1.1 x.1.2))) =
      Λ.points.map fun q => Λ.at_ q.1 q.2 := by
    conv_rhs => rw [← List.zipIdx_map_fst 0 Λ.points, List.map_map]
    rfl
  rw [e]
  refine hp.map_on fun x _ y _ hxy => ?_
  obtain ⟨h1, h2⟩ := Λ.at_injective hdet hxy
  exact Prod.ext h1 h2

end PILean.Diagram
