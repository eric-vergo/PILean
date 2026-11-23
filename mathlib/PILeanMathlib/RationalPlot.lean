/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Basic
import PILean.Diagram.ZeroPole

/-!
# Zeros and poles against Mathlib's polynomials

The figure of a rational function (`PILean.Diagram.RationalPlot`) is drawn from the coefficients
of its numerator and denominator and the zeros and poles supplied with their multiplicities. Here
those coefficients are Mathlib's polynomials over ℚ (`ofCoeffs`), read over ℂ (`ofCoeffsC`), and
the two decidable statements of the core are statements about them:

* `rootMultiplicity_of`: a supplied root of multiplicity `m` that passes the core's test
  (`rootOfMultiplicity`: the derivatives of orders below `m` vanish at it, that of order `m` does
  not) has `Polynomial.rootMultiplicity` exactly `m` over ℂ.
* `RationalPlot.zeros_complete`: when the multiplicities add up to the degree of a nonzero
  polynomial (`RationalPlot.Complete`), every complex root of it is one of the supplied ones, so
  the figure marks all the zeros (and, for the denominator, all the poles).

## Main definitions

* `ofCoeffs`, `ofCoeffsC`, `toC`.

## Main results

* `eval_ofCoeffsC`, `ofCoeffs_iterDeriv`, `natDegree_ofCoeffs_le`, `rootMultiplicity_of`.
* `RationalPlot.zero_rootMultiplicity`, `RationalPlot.pole_rootMultiplicity`,
  `RationalPlot.zeros_complete`, `RationalPlot.poles_complete`.
-/

namespace PILeanMathlib

open Polynomial PILean.Diagram

/-- The polynomial with the rational coefficients `cs`, constant first. -/
noncomputable def ofCoeffs : List ℚ → ℚ[X]
  | [] => 0
  | c :: cs => C c + X * ofCoeffs cs

/-- The polynomial with the coefficients `cs`, read over ℂ. -/
noncomputable def ofCoeffsC (cs : List ℚ) : ℂ[X] := (ofCoeffs cs).map (algebraMap ℚ ℂ)

/-- The Gaussian rational `(a, b)` as the complex number `a + b i`. -/
def toC (z : GaussQ) : ℂ := ⟨z.1, z.2⟩

theorem toC_add (z w : GaussQ) : toC (GaussQ.add z w) = toC z + toC w := by
  apply Complex.ext <;> simp [GaussQ.add, toC]

theorem toC_mul (z w : GaussQ) : toC (GaussQ.mul z w) = toC z * toC w := by
  apply Complex.ext <;> simp [GaussQ.mul, toC]

theorem toC_injective : Function.Injective toC := by
  intro z w h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [toC, Rat.cast_inj] at h1 h2
  exact Prod.ext h1 h2

theorem toC_eq_zero (z : GaussQ) : toC z = 0 ↔ z = (0, 0) := by
  have : (0 : ℂ) = toC (0, 0) := by apply Complex.ext <;> simp [toC]
  rw [this]
  exact toC_injective.eq_iff

/-- The value of the polynomial at `a + b i` is the core's Horner evaluation, read in ℂ. -/
theorem eval_ofCoeffsC (cs : List ℚ) (z : GaussQ) :
    (ofCoeffsC cs).eval (toC z) = toC (evalAt cs z) := by
  induction cs with
  | nil =>
    simp only [ofCoeffsC, ofCoeffs, Polynomial.map_zero, eval_zero, evalAt, List.foldr_nil]
    apply Complex.ext <;> simp [toC]
  | cons c cs ih =>
    have e : evalAt (c :: cs) z = GaussQ.add (c, 0) (GaussQ.mul z (evalAt cs z)) := rfl
    simp only [ofCoeffsC, ofCoeffs, Polynomial.map_add, Polynomial.map_mul, map_C, map_X,
      eval_add, eval_C, eval_mul, eval_X] at ih ⊢
    rw [ih, e, toC_add, toC_mul]
    congr 1

/-- The coefficients of the polynomial are the list's. -/
theorem coeff_ofCoeffs (cs : List ℚ) (n : ℕ) : (ofCoeffs cs).coeff n = cs.getD n 0 := by
  induction cs generalizing n with
  | nil => simp [ofCoeffs]
  | cons c cs ih =>
    cases n with
    | zero => simp [ofCoeffs]
    | succ n => simp [ofCoeffs, coeff_X_mul, ih]

/-- The coefficients of the derivative, as the core computes them. -/
theorem getD_derivCoeffs (cs : List ℚ) (n : ℕ) :
    (derivCoeffs cs).getD n 0 = cs.getD (n + 1) 0 * (n + 1) := by
  have h : (derivCoeffs cs)[n]? = cs[n + 1]?.map (· * ((n + 1 : ℕ) : ℚ)) := by
    simp only [derivCoeffs, List.getElem?_map, List.getElem?_drop, List.getElem?_zipIdx]
    rw [show 1 + n = n + 1 by omega]
    cases cs[n + 1]? <;> simp
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, h]
  cases cs[n + 1]? <;> simp

/-- The core's derivative is the derivative. -/
theorem ofCoeffs_derivCoeffs (cs : List ℚ) :
    ofCoeffs (derivCoeffs cs) = derivative (ofCoeffs cs) := by
  ext n
  rw [coeff_ofCoeffs, getD_derivCoeffs, coeff_derivative, coeff_ofCoeffs]

/-- The core's derivative of order `k` is the iterated derivative. -/
theorem ofCoeffs_iterDeriv (k : ℕ) (cs : List ℚ) :
    ofCoeffs (iterDeriv k cs) = derivative^[k] (ofCoeffs cs) := by
  induction k generalizing cs with
  | zero => rfl
  | succ k ih =>
    rw [iterDeriv, ih, ofCoeffs_derivCoeffs, Function.iterate_succ_apply]

/-- The iterated derivative over ℂ is the core's, read over ℂ. -/
theorem ofCoeffsC_iterDeriv (k : ℕ) (cs : List ℚ) :
    ofCoeffsC (iterDeriv k cs) = derivative^[k] (ofCoeffsC cs) := by
  rw [ofCoeffsC, ofCoeffs_iterDeriv, ofCoeffsC, iterate_derivative_map]

/-- The largest index of the list holds: every index of a nonzero coefficient is at most the
core's degree. -/
theorem le_foldr_max {l : List ℕ} {P : ℕ → Bool} {i : ℕ} (hi : i ∈ l) (hp : P i = true) :
    i ≤ l.foldr (fun j acc => if P j then max j acc else acc) 0 := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hi with rfl | h
    · simp [hp]
    · have := ih h
      split <;> omega

/-- The polynomial has degree at most the core's degree. -/
theorem natDegree_ofCoeffs_le (cs : List ℚ) : (ofCoeffs cs).natDegree ≤ degreeOf cs := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_ofCoeffs]
  by_contra h
  have hl : n < cs.length := by
    by_contra hl
    apply h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  have := le_foldr_max (P := fun i => cs.getD i 0 != 0) (List.mem_range.2 hl) (by simpa using h)
  exact absurd this (by unfold degreeOf at hn; omega)

/-- The polynomial over ℂ has degree at most the core's degree. -/
theorem natDegree_ofCoeffsC_le (cs : List ℚ) : (ofCoeffsC cs).natDegree ≤ degreeOf cs :=
  (natDegree_map_le).trans (natDegree_ofCoeffs_le cs)

/-- **A root of the stated multiplicity.** A point that passes the core's test of multiplicity `m`
is a root of the polynomial over ℂ of multiplicity exactly `m`. -/
theorem rootMultiplicity_of {cs : List ℚ} {z : GaussQ} {m : ℕ}
    (h : rootOfMultiplicity cs z m = true) : (ofCoeffsC cs).rootMultiplicity (toC z) = m := by
  simp only [rootOfMultiplicity, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hm, hlow⟩, htop⟩ := h
  have root : ∀ j, (derivative^[j] (ofCoeffsC cs)).IsRoot (toC z) ↔
      evalAt (iterDeriv j cs) z = (0, 0) := by
    intro j
    rw [IsRoot, ← ofCoeffsC_iterDeriv, eval_ofCoeffsC, toC_eq_zero]
  have hp : ofCoeffsC cs ≠ 0 := by
    intro h0
    apply htop
    rw [← root, h0, iterate_derivative_zero]
    simp [IsRoot]
  apply le_antisymm
  · by_contra hlt
    exact htop ((root m).1 (isRoot_iterate_derivative_of_lt_rootMultiplicity (by omega)))
  · have := (lt_rootMultiplicity_iff_isRoot_iterate_derivative (n := m - 1) hp).2
      fun j hj => (root j).2 (hlow j (by omega))
    omega

namespace RationalPlot

/-- **Each zero is a root of its multiplicity.** In a verified figure, every supplied zero
`(z, m)` is a root of the numerator over ℂ of multiplicity exactly `m`. -/
theorem zero_rootMultiplicity {R : RationalPlot} (h : R.Verified = true) {z : GaussQ} {m : ℕ}
    (hz : (z, m) ∈ R.zeros) : (ofCoeffsC R.num).rootMultiplicity (toC z) = m := by
  simp only [PILean.Diagram.RationalPlot.Verified, Bool.and_eq_true, List.all_eq_true] at h
  exact rootMultiplicity_of (h.1.1.1.1 _ hz)

/-- **Each pole is a root of the denominator of its multiplicity.** -/
theorem pole_rootMultiplicity {R : RationalPlot} (h : R.Verified = true) {z : GaussQ} {m : ℕ}
    (hz : (z, m) ∈ R.poles) : (ofCoeffsC R.den).rootMultiplicity (toC z) = m := by
  simp only [PILean.Diagram.RationalPlot.Verified, Bool.and_eq_true, List.all_eq_true] at h
  exact rootMultiplicity_of (h.1.1.1.2 _ hz)

/-- Roots supplied with their multiplicities, distinct, whose multiplicities add up to the core's
degree of a nonzero polynomial, are all its roots. -/
theorem roots_complete {cs : List ℚ} {rs : List (GaussQ × ℕ)}
    (hm : ∀ zm ∈ rs, rootOfMultiplicity cs zm.1 zm.2 = true) (hd : (rs.map (·.1)).Nodup)
    (hs : (rs.map (·.2)).sum = degreeOf cs) (hne : ofCoeffsC cs ≠ 0) {w : ℂ}
    (hw : (ofCoeffsC cs).IsRoot w) : ∃ zm ∈ rs, w = toC zm.1 := by
  classical
  set p := ofCoeffsC cs
  by_contra hno
  push Not at hno
  -- the supplied roots as complex numbers, distinct
  have hd' : (rs.map fun zm => toC zm.1).Nodup := by
    rw [show (fun zm : GaussQ × ℕ => toC zm.1) = toC ∘ Prod.fst from rfl, ← List.map_map]
    exact hd.map toC_injective
  set Z := (rs.map fun zm => toC zm.1).toFinset
  have hwZ : w ∉ Z := by
    simp only [Z, List.mem_toFinset, List.mem_map, not_exists, not_and]
    exact fun zm hzm he => hno zm hzm he.symm
  have hZ : ∑ a ∈ Z, p.roots.count a = degreeOf cs := by
    rw [List.sum_toFinset _ hd', List.map_map, ← hs]
    congr 1
    apply List.map_congr_left
    intro zm hzm
    simp only [Function.comp_apply, count_roots]
    exact rootMultiplicity_of (hm zm hzm)
  have hT : ∑ a ∈ insert w Z ∪ p.roots.toFinset, p.roots.count a = Multiset.card p.roots :=
    Multiset.sum_count_eq_card fun a ha => by simp [Multiset.mem_toFinset.2 ha]
  have hle : ∑ a ∈ insert w Z, p.roots.count a ≤
      ∑ a ∈ insert w Z ∪ p.roots.toFinset, p.roots.count a :=
    Finset.sum_le_sum_of_subset Finset.subset_union_left
  rw [Finset.sum_insert hwZ, hZ, hT] at hle
  have hwc : 0 < p.roots.count w := by
    rw [count_roots]; exact (rootMultiplicity_pos hne).2 hw
  have := (card_roots' p).trans (natDegree_ofCoeffsC_le cs)
  omega

/-- **The marks are all the zeros.** In a verified and complete figure, every complex root of the
numerator is one of the supplied zeros. -/
theorem zeros_complete {R : RationalPlot} (hv : R.Verified = true) (hc : R.Complete = true)
    {w : ℂ} (hw : (ofCoeffsC R.num).IsRoot w) : ∃ zm ∈ R.zeros, w = toC zm.1 := by
  simp only [PILean.Diagram.RationalPlot.Verified, Bool.and_eq_true, List.all_eq_true] at hv
  simp only [PILean.Diagram.RationalPlot.Complete, Bool.and_eq_true, beq_iff_eq] at hc
  refine roots_complete (fun zm h => hv.1.1.1.1 zm h) (by simpa using hv.1.1.2) hc.1.1 ?_ hw
  exact nonzero_of hc.1.2
where
  /-- A list with a nonzero coefficient gives a nonzero polynomial over ℂ. -/
  nonzero_of {cs : List ℚ} (h : cs.any (· != 0) = true) : ofCoeffsC cs ≠ 0 := by
    intro h0
    obtain ⟨c, hc, hc0⟩ := List.any_eq_true.1 h
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hc
    have : (ofCoeffs cs).coeff n = 0 := by
      have := congrArg (fun q => q.coeff n) h0
      simp only [ofCoeffsC, coeff_map, coeff_zero, map_eq_zero] at this
      exact this
    rw [coeff_ofCoeffs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn] at this
    simp only [Option.getD_some] at this
    simp [this] at hc0

/-- **The marks are all the poles.** In a verified and complete figure, every complex root of the
denominator is one of the supplied poles. -/
theorem poles_complete {R : RationalPlot} (hv : R.Verified = true) (hc : R.Complete = true)
    {w : ℂ} (hw : (ofCoeffsC R.den).IsRoot w) : ∃ zm ∈ R.poles, w = toC zm.1 := by
  simp only [PILean.Diagram.RationalPlot.Verified, Bool.and_eq_true, List.all_eq_true] at hv
  simp only [PILean.Diagram.RationalPlot.Complete, Bool.and_eq_true, beq_iff_eq] at hc
  exact roots_complete (fun zm h => hv.1.1.1.2 zm h) (by simpa using hv.1.2) hc.2.1
    (zeros_complete.nonzero_of hc.2.2) hw

end RationalPlot

end PILeanMathlib
