/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.PrimeCounting
import PILeanMathlib.NumberTheory
import PILeanMathlib.Examples.NumberTheoryFigures

/-!
# Figures of number theory tied to Mathlib's objects: the theorems

Each figure of `PILeanMathlib.Examples.NumberTheoryFigures` is linked by `figure_proves` to a
theorem that states, with Mathlib's definitions, what it draws. The figures compute with plain
functions; the lemmas `totient'_eq`, `divisorCount_eq`, `isPrime'_iff`, `primeCount_eq`,
`harmonic'_eq`, `legendre'_eq` and `prime_of_gaussianPrime` prove those equal to Mathlib's for
every argument, so no value is computed by the kernel except the Gaussian integers of the window
that are not prime (`unmarked_shown`, by factor witnesses).

## Main results

* `totientFigure_spec`: the points are exactly `(n, Nat.totient n)` for `1 ≤ n ≤ 100`.
* `divisorFigure_spec`: the points are exactly `(n, σ 0 n)` for `1 ≤ n ≤ 100`.
* `primeCountFigure_spec`: the points are exactly `(n, Nat.primeCounting n)` for `2 ≤ n ≤ 100`,
  and the curve is the polyline through `(n, n / (harmonic n - 1))`.
* `ulamFigure_spec`: the cells are `1, …, 441` on a square spiral (each next to the one before,
  no two at one place), and a cell is marked exactly when its number is `Nat.Prime`.
* `residueFigure_spec`: for each `p` of `3, 5, 7, 11, 13` and `a < p`, the cell of `a` in the
  row of `p` is marked exactly when `a` is a nonzero square in `ZMod p` and shows `legendreSym p a`.
* `gaussianFigure_spec`: the dots are exactly the Gaussian integers `a + b i` with
  `|a|, |b| ≤ 7`, in accent 1 when `Prime (⟨a, b⟩ : GaussianInt)` and faint when not.
-/

open PILean PILean.Diagram

namespace PILeanMathlib.Examples

/-! ### The plain functions are Mathlib's -/

/-- The figure's totient is Mathlib's. -/
theorem totient'_eq (n : ℕ) : totient' n = Nat.totient n := by
  unfold totient'
  rw [Nat.totient, card_filter_range (n.Coprime ·)]
  intro a; simp [Nat.Coprime]

/-- The figure's test of primality is `Nat.Prime`. -/
theorem isPrime'_iff (n : ℕ) : isPrime' n = true ↔ n.Prime := by
  rw [Nat.prime_def_lt']
  simp only [isPrime', Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range',
    bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hmn hd => ?_⟩
    exact h m ⟨m - 2, by omega, by omega⟩ (Nat.mod_eq_zero_of_dvd hd)
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m ⟨i, hi, hm⟩ hmod => h m (by omega) (by omega) (Nat.dvd_of_mod_eq_zero hmod)⟩

/-- The figure's count of primes is `Nat.primeCounting`. -/
theorem primeCount_eq (n : ℕ) : primeCount n = Nat.primeCounting n := by
  unfold primeCount
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range,
    card_filter_range Nat.Prime _ isPrime'_iff]

/-- The figure's harmonic numbers are Mathlib's `harmonic`. -/
theorem harmonic'_eq (n : ℕ) : harmonic' n = harmonic n := by
  induction n with
  | zero => simp [harmonic']
  | succ n ih => rw [harmonic', harmonic_succ, ih]; push_cast; ring

/-- The figure's count of divisors is the number of elements of `Nat.divisors n`. -/
theorem divisorCount_eq (n : ℕ) : divisorCount n = (Nat.divisors n).card := by
  unfold divisorCount
  rw [Nat.divisors, Finset.card_def, Finset.filter_val]
  rw [Nat.Ico_eq_range']
  simp only [Nat.add_sub_cancel, Multiset.filter_coe, Multiset.coe_card]
  rw [show (fun b => decide (b ∣ n)) = (fun d => n % d == 0) from
    funext fun d => Bool.eq_iff_iff.2 (by simp [Nat.dvd_iff_mod_eq_zero])]

/-- The search `legendre'` is Mathlib's Legendre symbol. -/
theorem legendre'_eq (p : ℕ) [Fact p.Prime] (a : ℕ) : legendre' p a = legendreSym p a := by
  have hp : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have ha : ((a : ℤ) : ZMod p) = 0 ↔ a % p = 0 := by
    rw [Int.cast_natCast, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
  unfold legendre'
  split_ifs with h0 hs
  · exact ((legendreSym.eq_zero_iff p a).2 (ha.2 h0)).symm
  · rw [eq_comm, legendreSym.eq_one_iff p (mt ha.1 h0), Int.cast_natCast]
    exact (isSquare_iff_any p a).2 hs
  · rw [eq_comm, legendreSym.eq_neg_one_iff p, Int.cast_natCast]
    exact fun h => hs ((isSquare_iff_any p a).1 h)

/-- Every Gaussian integer that `gaussianPrime` marks is prime in `GaussianInt`. -/
theorem prime_of_gaussianPrime {a b : ℤ} (h : gaussianPrime a b = true) :
    Prime (⟨a, b⟩ : GaussianInt) := by
  unfold gaussianPrime at h
  split_ifs at h with hax
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hp, h3⟩ := h
    have hkp : (a + b).natAbs.Prime := (isPrime'_iff _).1 hp
    have := Fact.mk hkp
    have hpk : Prime (((a + b).natAbs : ℕ) : GaussianInt) :=
      GaussianInt.prime_of_nat_prime_of_mod_four_eq_three _ h3
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hax
    rcases hax with rfl | rfl
    · rw [zero_add] at hpk
      rcases Int.natAbs_eq b with hb | hb
      · exact prime_of_unit_mul hpk 0 1 (by norm_num) (by
          rw [Zsqrtd.ext_iff]
          simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast]
          omega)
      · exact prime_of_unit_mul hpk 0 (-1) (by norm_num) (by
          rw [Zsqrtd.ext_iff]
          simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast]
          omega)
    · rw [add_zero] at hpk
      rcases Int.natAbs_eq a with ha | ha
      · exact prime_of_unit_mul hpk 1 0 (by norm_num) (by
          rw [Zsqrtd.ext_iff]
          simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast]
          omega)
      · exact prime_of_unit_mul hpk (-1) 0 (by norm_num) (by
          rw [Zsqrtd.ext_iff]
          simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast]
          omega)
  · apply prime_of_norm_prime
    have : (⟨a, b⟩ : GaussianInt).norm.natAbs = a.natAbs ^ 2 + b.natAbs ^ 2 := by
      rw [Zsqrtd.norm_def]; simp only
      have : a * a - -1 * b * b = ((a.natAbs ^ 2 + b.natAbs ^ 2 : ℕ) : ℤ) := by
        push_cast; rw [sq_abs, sq_abs]; ring
      rw [this, Int.natAbs_natCast]
    rw [this]; exact (isPrime'_iff _).1 h

/-- In the window `|a|, |b| ≤ 7` every Gaussian integer that `gaussianPrime` leaves unmarked is
shown not to be prime (`0`, a unit, or a product of two factors of norm greater than one). -/
theorem unmarked_shown : ∀ a ∈ List.range 15, ∀ b ∈ List.range 15,
    gaussianPrime ((a : ℤ) - 7) ((b : ℤ) - 7) = false →
      notPrimeShown ((a : ℤ) - 7) ((b : ℤ) - 7) = true := by
  decide +kernel

/-! ### The figures -/

/-- **Euler's totient.** The figure plots faithfully one sequence, named `φ(n)`, with no curve,
at positive scales; its points are exactly `(n, Nat.totient n)` for `1 ≤ n ≤ 100`. -/
theorem totientFigure_spec :
    totientPlot.Faithful totientPlot.layout totientFigure ∧
    totientPlot.names = ["φ(n)"] ∧ totientPlot.curves.length = 0 ∧
    0 < totientPlot.layout.sx ∧ 0 < totientPlot.layout.sy ∧
    ∀ k n p, (k, n, p) ∈ totientFigure.data ↔
      k = 0 ∧ 1 ≤ n ∧ n ≤ 100 ∧ p = SeqPlot.point totientPlot.layout n (Nat.totient n) := by
  sorry

figure_proves totientFigure totientFigure_spec

/-- **The number of divisors.** The figure plots faithfully one sequence, named `d(n) = σ₀(n)`,
with no curve, at positive scales; its points are exactly `(n, σ 0 n)` for `1 ≤ n ≤ 100`, where
`σ 0 n` is the number of divisors (`ArithmeticFunction.sigma_zero_apply`). -/
theorem divisorFigure_spec :
    divisorPlot.Faithful divisorPlot.layout divisorFigure ∧
    divisorPlot.names = ["d(n) = σ₀(n)"] ∧ divisorPlot.curves.length = 0 ∧
    0 < divisorPlot.layout.sx ∧ 0 < divisorPlot.layout.sy ∧
    ∀ k n p, (k, n, p) ∈ divisorFigure.data ↔
      k = 0 ∧ 1 ≤ n ∧ n ≤ 100 ∧
        p = SeqPlot.point divisorPlot.layout n (ArithmeticFunction.sigma 0 n) := by
  sorry

figure_proves divisorFigure divisorFigure_spec

/-- **The prime-counting function.** The figure plots faithfully the sequence `π(n)` and the
curve `n / (Hₙ − 1)`, at positive scales; its points are exactly `(n, Nat.primeCounting n)` for
`2 ≤ n ≤ 100`, and its one curve is the polyline through `(n, n / (harmonic n - 1))` for the same
`n`, in the second colour. -/
theorem primeCountFigure_spec :
    primeCountPlot.Faithful primeCountPlot.layout primeCountFigure ∧
    primeCountPlot.names = ["π(n)", "n / (Hₙ − 1)"] ∧
    0 < primeCountPlot.layout.sx ∧ 0 < primeCountPlot.layout.sy ∧
    (∀ k n p, (k, n, p) ∈ primeCountFigure.data ↔
      k = 0 ∧ 2 ≤ n ∧ n ≤ 100 ∧
        p = SeqPlot.point primeCountPlot.layout n (Nat.primeCounting n)) ∧
    primeCountFigure.marksWhere Part.isCurve =
      [{ part := .curve 0, ink := .series 1 false,
         shape := .polyline ((List.range' 2 99).map fun n =>
           SeqPlot.point primeCountPlot.layout n ((n : ℚ) / (harmonic n - 1))) }] := by
  sorry

figure_proves primeCountFigure primeCountFigure_spec

/-- **The primes on the Ulam spiral.** The figure draws the cells faithfully: their numbers are
`1, …, 441`, each cell next to the one before (one unit across or up or down), no two at one
place, `1` at the origin; a cell is marked (filled) exactly when its number is `Nat.Prime`;
only the cell of `1` has a text, `1`; there is no heading. -/
theorem ulamFigure_spec :
    ulamPlot.Faithful ulamFigure ∧ ulamPlot.solid = true ∧ ulamPlot.headings = [] ∧
    ulamPlot.cells.map (·.key) = List.range' 1 441 ∧
    (ulamPlot.cells.map (·.pos)).head? = some (0, 0) ∧
    (ulamPlot.cells.zip ulamPlot.cells.tail).all (fun (c, c') =>
      (c.pos.1 - c'.pos.1).natAbs + (c.pos.2 - c'.pos.2).natAbs == 1) = true ∧
    (ulamPlot.cells.map (·.pos)).Nodup ∧
    (∀ c ∈ ulamPlot.cells, c.text = if c.key = 1 then "1" else "") ∧
    ∀ c ∈ ulamPlot.cells, c.marked = true ↔ c.key.Prime := by
  sorry

figure_proves ulamFigure ulamFigure_spec

/-- **Quadratic residues and Legendre symbols.** The figure draws the table faithfully: its rows
are the primes `3, 5, 7, 11, 13`; it has 39 cells, no two with one key, and for each prime `p` of
row `i` and each `a < p` the cell of key `100 p + a` stands in column `a` of row `i`, is marked
exactly when `a` is a nonzero square in `ZMod p`, and shows the Legendre symbol `legendreSym p a`;
its headings are the primes and the residues (written out). -/
theorem residueFigure_spec :
    residuePlot.Faithful residueFigure ∧ residuePrimes = [3, 5, 7, 11, 13] ∧
    residuePlot.cells.length = 39 ∧ (residuePlot.cells.map (·.key)).Nodup ∧
    (∀ (i p : ℕ) (hp : p.Prime), residuePrimes[i]? = some p → ∀ a < p,
      ∃ c ∈ residuePlot.cells, c.key = 100 * p + a ∧ c.pos = ((a : ℤ), -(i : ℤ)) ∧
        (c.marked = true ↔ (a : ZMod p) ≠ 0 ∧ IsSquare (a : ZMod p)) ∧
        c.text = symbolText (@legendreSym p ⟨hp⟩ a)) ∧
    residuePlot.headings.map (·.1) = ["p = 3", "p = 5", "p = 7", "p = 11", "p = 13", "a", "0", "1",
      "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12"] ∧
    residuePlot.solid = false := by
  sorry

figure_proves residueFigure residueFigure_spec

/-- **The Gaussian primes.** The figure draws the lattice faithfully, with the axes and the unit
square; its dots are exactly the Gaussian integers `a + b i` with `|a|, |b| ≤ 7`, each at
`(a, b)`, drawn in accent 1 when `⟨a, b⟩` is prime in `GaussianInt` and in the faint ink when it
is not. -/
theorem gaussianFigure_spec :
    gaussianLattice.Faithful gaussianFigure ∧
    ∀ (p : QPoint) (col : Ink), (∃ i, (i, p, col) ∈ gaussianFigure.dots) ↔
      ∃ a b : ℤ, |a| ≤ 7 ∧ |b| ≤ 7 ∧ p = ((a : ℚ), (b : ℚ)) ∧
        (col = .accent 1 ∧ Prime (⟨a, b⟩ : GaussianInt) ∨
          col = .faint ∧ ¬ Prime (⟨a, b⟩ : GaussianInt)) := by
  sorry

figure_proves gaussianFigure gaussianFigure_spec

end PILeanMathlib.Examples
