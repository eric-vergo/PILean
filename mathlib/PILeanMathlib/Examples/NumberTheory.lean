/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.PrimeCounting
import PILeanMathlib.Lattice
import PILeanMathlib.NumberTheory
import PILeanMathlib.Examples.NumberTheoryFigures

/-!
# Figures of number theory and Mathlib's objects: the theorems

Each figure of `PILeanMathlib.Examples.NumberTheoryFigures` is linked by `figure_links` to a
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
* `latticeFigure_spec`: the dots are exactly the points of `Submodule.span ℤ {(1, 0), (1/2, 7/8)}`
  in `[-3, 3] × [-2, 2]`, each once, and the parallelogram is `0, ω₁, ω₁ + ω₂, ω₂`.
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

/-- In the window `|a|, |b| ≤ 7`, `gaussianPrime` marks exactly the primes of `GaussianInt`. -/
theorem gaussianPrime_iff {a b : ℤ} (ha : |a| ≤ 7) (hb : |b| ≤ 7) :
    gaussianPrime a b = true ↔ Prime (⟨a, b⟩ : GaussianInt) := by
  refine ⟨prime_of_gaussianPrime, fun hp => ?_⟩
  by_contra hf
  rw [Bool.not_eq_true] at hf
  rw [abs_le] at ha hb
  have h := unmarked_shown (a + 7).toNat (by simp; omega) (b + 7).toNat (by simp; omega)
  rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega), add_sub_cancel_right,
    add_sub_cancel_right] at h
  exact not_prime_of_shown a b (h hf) hp

/-! ### The figures -/

/-- **Euler's totient.** The figure plots faithfully one sequence, named `φ(n)`, with no curve,
at positive scales; its points are exactly `(n, Nat.totient n)` for `1 ≤ n ≤ 100`. -/
theorem totientFigure_spec :
    (totientFigure.title = "Euler's totient φ(n), 1 ≤ n ≤ 100" ∧ totientFigure.style = {}) ∧
    totientPlot.Faithful totientPlot.layout totientFigure ∧
    totientPlot.names = ["φ(n)"] ∧ totientPlot.curves.length = 0 ∧
    0 < totientPlot.layout.sx ∧ 0 < totientPlot.layout.sy ∧
    ∀ k n p, (k, n, p) ∈ totientFigure.data ↔
      k = 0 ∧ 1 ≤ n ∧ n ≤ 100 ∧ p = SeqPlot.point totientPlot.layout n (Nat.totient n) := by
  refine ⟨⟨rfl, by unfold totientFigure SeqPlot.figure Diagram.capped; split <;> rfl⟩, ?_⟩
  have h : totientPlot.Faithful totientPlot.layout totientFigure :=
    SeqPlot.faithful_of_marks (totientPlot.builder_faithful (by decide +kernel)) rfl
  exact ⟨h, rfl, rfl, by decide +kernel, by decide +kernel,
    SeqPlot.data_iff h rfl (fun n => by simp [totient'_eq])⟩

figure_links totientFigure totientFigure_spec

/-- **The number of divisors.** The figure plots faithfully one sequence, named `d(n) = σ₀(n)`,
with no curve, at positive scales; its points are exactly `(n, σ 0 n)` for `1 ≤ n ≤ 100`, where
`σ 0 n` is the number of divisors (`ArithmeticFunction.sigma_zero_apply`). -/
theorem divisorFigure_spec :
    (divisorFigure.title = "The number of divisors d(n), 1 ≤ n ≤ 100" ∧ divisorFigure.style = {}) ∧
    divisorPlot.Faithful divisorPlot.layout divisorFigure ∧
    divisorPlot.names = ["d(n) = σ₀(n)"] ∧ divisorPlot.curves.length = 0 ∧
    0 < divisorPlot.layout.sx ∧ 0 < divisorPlot.layout.sy ∧
    ∀ k n p, (k, n, p) ∈ divisorFigure.data ↔
      k = 0 ∧ 1 ≤ n ∧ n ≤ 100 ∧
        p = SeqPlot.point divisorPlot.layout n (ArithmeticFunction.sigma 0 n) := by
  refine ⟨⟨rfl, by unfold divisorFigure SeqPlot.figure Diagram.capped; split <;> rfl⟩, ?_⟩
  have h : divisorPlot.Faithful divisorPlot.layout divisorFigure :=
    SeqPlot.faithful_of_marks (divisorPlot.builder_faithful (by decide +kernel)) rfl
  exact ⟨h, rfl, rfl, by decide +kernel, by decide +kernel,
    SeqPlot.data_iff h rfl
      (fun n => by simp [divisorCount_eq, ArithmeticFunction.sigma_zero_apply])⟩

figure_links divisorFigure divisorFigure_spec

/-- **The prime-counting function.** The figure plots faithfully the sequence `π(n)` and the
curve `n / (Hₙ − 1)`, at positive scales; its points are exactly `(n, Nat.primeCounting n)` for
`2 ≤ n ≤ 100`, and its one curve is the polyline through `(n, n / (harmonic n - 1))` for the same
`n`, in the second colour. -/
theorem primeCountFigure_spec :
    (primeCountFigure.title = "π(n) and n / (Hₙ − 1), 2 ≤ n ≤ 100" ∧ primeCountFigure.style = {}) ∧
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
  refine ⟨⟨rfl, by unfold primeCountFigure SeqPlot.figure Diagram.capped; split <;> rfl⟩, ?_⟩
  have h : primeCountPlot.Faithful primeCountPlot.layout primeCountFigure :=
    SeqPlot.faithful_of_marks (primeCountPlot.builder_faithful (by decide +kernel)) rfl
  refine ⟨h, rfl, by decide +kernel, by decide +kernel,
    SeqPlot.data_iff h rfl (fun n => by simp [primeCount_eq]), ?_⟩
  rw [h.2.2.1]
  simp [SeqPlot.curveMarks, primeCountPlot, SeqPlot.indices, harmonic'_eq]

figure_links primeCountFigure primeCountFigure_spec

/-- **The primes on the Ulam spiral.** The figure draws the cells faithfully: their numbers are
`1, …, 441`, each cell next to the one before (one unit across or up or down), no two at one
place, `1` at the origin (the centre of the spiral); a cell is marked (filled) exactly when its
number is `Nat.Prime`; no cell has a text and there is no heading. -/
theorem ulamFigure_spec :
    (ulamFigure.title = "The primes up to 441 on the Ulam spiral" ∧ ulamFigure.style = {}) ∧
    ulamPlot.Faithful ulamFigure ∧ ulamPlot.solid = true ∧ ulamPlot.headings = [] ∧
    ulamPlot.cells.map (·.key) = List.range' 1 441 ∧
    ulamPlot.cells.map (·.pos) = ulamWalk 441 ∧
    (ulamPlot.cells.map (·.pos)).head? = some (0, 0) ∧
    (ulamPlot.cells.zip ulamPlot.cells.tail).all (fun (c, c') =>
      (c.pos.1 - c'.pos.1).natAbs + (c.pos.2 - c'.pos.2).natAbs == 1) = true ∧
    (ulamPlot.cells.map (·.pos)).Nodup ∧
    (∀ c ∈ ulamPlot.cells, c.text = "") ∧ ulamPlot.ringed = some 1 ∧ ulamPlot.legend = "" ∧
    ∀ c ∈ ulamPlot.cells, c.marked = true ↔ c.key.Prime := by
  refine ⟨⟨rfl, by unfold ulamFigure CellPlot.figure Diagram.capped; split <;> rfl⟩, ?_⟩
  have h : ulamPlot.Faithful ulamFigure :=
    CellPlot.faithful_of_marks (ulamPlot.builder_faithful (by decide +kernel))
      (by simp only [ulamFigure])
  have hc : ∀ c ∈ ulamPlot.cells, c.marked = isPrime' c.key ∧ c.text = "" := fun c h' => by
    simpa using mem_ulamCells h'
  refine ⟨h, rfl, rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    (nodup_of_distinctInBox 10 _ 0 (by decide +kernel)).2, fun c h' => (hc c h').2, rfl, rfl,
    fun c h' => by rw [(hc c h').1, isPrime'_iff]⟩

figure_links ulamFigure ulamFigure_spec

/-- **Quadratic residues and Legendre symbols.** The figure draws the table faithfully: its rows
are the primes `3, 5, 7, 11, 13`; it has 39 cells, no two with one key, and for each prime `p` of
row `i` and each `a < p` the cell of key `100 p + a` stands in column `a` of row `i`, is marked
exactly when `a` is a nonzero square in `ZMod p`, and shows the Legendre symbol `legendreSym p a`;
its headings are the primes and the residues (written out). -/
theorem residueFigure_spec :
    (residueFigure.title = "Quadratic residues and Legendre symbols \
      modulo 3, 5, 7, 11, 13" ∧ residueFigure.style = {}) ∧
    residuePlot.Faithful residueFigure ∧ residuePrimes = [3, 5, 7, 11, 13] ∧
    residuePlot.cells.length = 39 ∧ (residuePlot.cells.map (·.key)).Nodup ∧
    (∀ (i p : ℕ) (hp : p.Prime), residuePrimes[i]? = some p → ∀ a < p,
      ∃ c ∈ residuePlot.cells, c.key = 100 * p + a ∧ c.pos = ((a : ℤ), -(i : ℤ)) ∧
        (c.marked = true ↔ (a : ZMod p) ≠ 0 ∧ IsSquare (a : ZMod p)) ∧
        c.text = symbolText (@legendreSym p ⟨hp⟩ a)) ∧
    residuePlot.headings = [("p = 3", (-1, 1/2)), ("p = 5", (-1, -1/2)), ("p = 7", (-1, -3/2)),
      ("p = 11", (-1, -5/2)), ("p = 13", (-1, -7/2)), ("a", (-1, 3/2)), ("0", (1/2, 3/2)), ("1",
      (3/2, 3/2)), ("2", (5/2, 3/2)), ("3", (7/2, 3/2)), ("4", (9/2, 3/2)), ("5", (11/2, 3/2)),
      ("6", (13/2, 3/2)), ("7", (15/2, 3/2)), ("8", (17/2, 3/2)), ("9", (19/2, 3/2)), ("10", (21/2,
      3/2)), ("11", (23/2, 3/2)), ("12", (25/2, 3/2))] ∧
    residuePlot.solid = false ∧ residuePlot.legend = "a nonzero square mod p" ∧
    residuePlot.ringed = none := by
  refine ⟨⟨rfl, by unfold residueFigure CellPlot.figure Diagram.capped; split <;> rfl⟩, ?_⟩
  have h : residuePlot.Faithful residueFigure :=
    CellPlot.faithful_of_marks (residuePlot.builder_faithful (by decide +kernel))
      (by simp only [residueFigure])
  refine ⟨h, rfl, by decide +kernel, by decide +kernel, fun i p hp hi a ha => ?_,
    by decide +kernel, rfl, rfl, rfl⟩
  have := Fact.mk hp
  have hne : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨residueCell p i a, ?_, rfl, rfl, ?_, by rw [residueCell, legendre'_eq]⟩
  · simp only [residuePlot, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨(p, i), List.mem_zipIdx_iff_getElem?.2 hi, a, ha, rfl⟩
  · have h0 : (a : ZMod p) ≠ 0 ↔ a % p ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
    simp only [residueCell, legendre', beq_iff_eq]
    rw [h0, isSquare_iff_any]
    split_ifs with h1 h2 <;> simp_all

figure_links residueFigure residueFigure_spec

/-- **The Gaussian primes.** The figure draws the lattice faithfully, with the axes and the unit
square; its dots are exactly the Gaussian integers `a + b i` with `|a|, |b| ≤ 7`, each at
`(a, b)`, drawn in accent 1 when `⟨a, b⟩` is prime in `GaussianInt` and in the faint ink when it
is not. -/
theorem gaussianFigure_spec :
    (gaussianFigure.title = "The Gaussian primes a + bi with \
      |a|, |b| ≤ 7" ∧ gaussianFigure.style = {}) ∧
    gaussianLattice.Faithful gaussianFigure ∧
    ∀ (p : QPoint) (col : Ink), (∃ i, (i, p, col) ∈ gaussianFigure.dots) ↔
      ∃ a b : ℤ, |a| ≤ 7 ∧ |b| ≤ 7 ∧ p = ((a : ℚ), (b : ℚ)) ∧
        (col = .accent 1 ∧ Prime (⟨a, b⟩ : GaussianInt) ∨
          col = .faint ∧ ¬ Prime (⟨a, b⟩ : GaussianInt)) := by
  refine ⟨⟨rfl, by unfold gaussianFigure PlaneLattice.figure Diagram.capped; split <;> rfl⟩, ?_⟩
  have h : gaussianLattice.Faithful gaussianFigure :=
    PlaneLattice.faithful_of_marks (gaussianLattice.builder_faithful (by decide +kernel))
      (by simp only [gaussianFigure])
  refine ⟨h, fun p col => ?_⟩
  have hb : gaussianLattice.bound = 7 := by decide +kernel
  have hw : ∀ m n : ℤ, (m, n) ∈ gaussianLattice.points ↔ |m| ≤ 7 ∧ |n| ≤ 7 := by
    intro m n
    rw [PlaneLattice.mem_points, hb]
    simp only [PlaneLattice.inWindow, PlaneLattice.at_, gaussianLattice, Bool.and_eq_true]
    simp only [decide_eq_true_eq, mul_one, mul_zero, add_zero, zero_add, abs_le]
    constructor
    · rintro ⟨-, -, ⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩, by exact_mod_cast h3,
        by exact_mod_cast h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨by omega, by omega, ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩,
        by exact_mod_cast h3⟩, by exact_mod_cast h4⟩
  have hink : ∀ m n : ℤ, |m| ≤ 7 → |n| ≤ 7 → ∀ col, col = gaussianLattice.pointInk m n ↔
      (col = .accent 1 ∧ Prime (⟨m, n⟩ : GaussianInt) ∨
        col = .faint ∧ ¬ Prime (⟨m, n⟩ : GaussianInt)) := by
    intro m n hm hn col
    rw [← gaussianPrime_iff hm hn]
    simp only [PlaneLattice.pointInk, gaussianLattice]
    by_cases hg : gaussianPrime m n = true <;> simp [hg]
  rw [h.1]
  simp only [List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨i, ⟨⟨m, n⟩, j⟩, hmem, rfl, rfl, rfl⟩
    obtain ⟨hm, hn⟩ := (hw m n).1 (List.fst_mem_of_mem_zipIdx hmem)
    refine ⟨m, n, hm, hn, ?_, (hink m n hm hn _).1 rfl⟩
    simp [PlaneLattice.at_, gaussianLattice]
  · rintro ⟨m, n, hm, hn, rfl, hc⟩
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ((hw m n).2 ⟨hm, hn⟩)
    refine ⟨k, ((m, n), k), List.mk_mem_zipIdx_iff_getElem?.2 hk, rfl, ?_, ?_⟩
    · simp [PlaneLattice.at_, gaussianLattice]
    · exact ((hink m n hm hn col).2 hc).symm

figure_links gaussianFigure gaussianFigure_spec

/-- **A lattice and its fundamental domain.** The figure draws the lattice faithfully; its dots
are exactly the points of `Submodule.span ℤ {(1, 0), (1/2, 7/8)}` in the window
`[-3, 3] × [-2, 2]`, each once, all in the ink; the fundamental parallelogram is the closed
polyline `0, ω₁, ω₁ + ω₂, ω₂` in accent 0. -/
theorem latticeFigure_spec :
    (latticeFigure.title = "The lattice ℤ(1, 0) + ℤ(1/2, 7/8) and \
      its fundamental domain" ∧ latticeFigure.style = {}) ∧
    hexLattice.Faithful latticeFigure ∧
    (∀ p : ℚ × ℚ, (∃ i col, (i, p, col) ∈ latticeFigure.dots) ↔
      p ∈ Submodule.span ℤ {((1 : ℚ), (0 : ℚ)), (1 / 2, 7 / 8)} ∧
        -3 ≤ p.1 ∧ p.1 ≤ 3 ∧ -2 ≤ p.2 ∧ p.2 ≤ 2) ∧
    (latticeFigure.dots.map (·.2.1)).Nodup ∧
    (∀ i p col, (i, p, col) ∈ latticeFigure.dots → col = .ink) ∧
    latticeFigure.marksWhere (· == .note 0) =
      [{ part := .note 0, ink := .accent 0,
         shape := .polyline [(0, 0), (1, 0), (3 / 2, 7 / 8), (1 / 2, 7 / 8), (0, 0)] }] := by
  refine ⟨⟨rfl, by unfold latticeFigure PlaneLattice.figure Diagram.capped; split <;> rfl⟩, ?_⟩
  have h : hexLattice.Faithful latticeFigure :=
    PlaneLattice.faithful_of_marks (hexLattice.builder_faithful (by decide +kernel))
      (by simp only [latticeFigure])
  have hdet : hexLattice.det ≠ 0 := by decide +kernel
  refine ⟨h, fun p => ?_, hexLattice.nodup_dots hdet h, fun i p col hm => ?_, ?_⟩
  · rw [hexLattice.mem_dots_iff hdet h]
    simp only [PlaneLattice.inWindow, hexLattice, Bool.and_eq_true]
    norm_num [and_assoc]
    exact fun _ => ⟨fun ⟨a, b, c, d⟩ => ⟨of_decide_eq_true a, of_decide_eq_true b,
      of_decide_eq_true c, of_decide_eq_true d⟩, fun ⟨a, b, c, d⟩ => ⟨decide_eq_true a,
      decide_eq_true b, decide_eq_true c, decide_eq_true d⟩⟩
  · rw [h.1] at hm
    obtain ⟨⟨⟨m, n⟩, j⟩, -, he⟩ := List.mem_map.1 hm
    simp only [Prod.mk.injEq] at he
    rw [← he.2.2]
    rfl
  · have e : latticeFigure.marksWhere (· == .note 0) =
        (latticeFigure.marksWhere Part.isDecoration).filter (fun m => m.part == .note 0) := by
      simp only [Diagram.marksWhere, List.filter_filter]
      congr 1
      funext m
      cases m.part <;> simp [Part.isDecoration]
    rw [e, h.2.2.1]
    decide +kernel

figure_links latticeFigure latticeFigure_spec

end PILeanMathlib.Examples
