/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic
import PILean.Diagram.Lattice
import PILean.Diagram.Sequence

/-!
# Plots of sequences, grids of numbers and lattices bound to Mathlib

What the theorems about the figures of number theory need to state them in Mathlib's terms:

* `SeqPlot.data_iff`: the points of a faithful plot of one sequence that agrees with a function
  `g : ℕ → ℚ` are exactly the points `(n, g n)` of its range.
* `card_filter_range`: counting with a Boolean filter of `List.range n` is Mathlib's `Finset`
  count, for the plain definitions of the figures (the totient, the prime-counting function).
* `isSquare_iff_any`: being a square in `ZMod p` is a search among `0, …, p - 1`.
* `distinctInBox`, `nodup_of_distinctInBox`: points of a box, no two at one place, checked in
  linear time by a bit mask (the Ulam spiral's 441 cells).
* Gaussian integers: `prime_of_norm_prime` (a prime norm makes a prime), `prime_of_unit_mul`
  (a unit multiple of a prime is prime), `not_prime_of_mul`, and the search `gaussianWitness` of
  a factorisation with `not_prime_of_shown`, which together decide primality in a finite window
  in both directions.
-/

namespace PILeanMathlib

open Finset PILean.Diagram

/-- Faithfulness of a plot depends on the marks only. -/
theorem SeqPlot.faithful_of_marks {P : SeqPlot} {L : SeqLayout} {d d' : Diagram}
    (h : P.Faithful L d) (e : d'.marks = d.marks) : P.Faithful L d' := by
  unfold SeqPlot.Faithful Diagram.data Diagram.marksWhere at *
  rw [e]
  exact h

/-- Faithfulness of a grid depends on the marks only. -/
theorem CellPlot.faithful_of_marks {P : CellPlot} {d d' : Diagram} (h : P.Faithful d)
    (e : d'.marks = d.marks) : P.Faithful d' := by
  unfold CellPlot.Faithful Diagram.marksWhere at *
  rw [e]
  exact h

/-- Faithfulness of a lattice depends on the marks only. -/
theorem PlaneLattice.faithful_of_marks {Λ : PlaneLattice} {d d' : Diagram} (h : Λ.Faithful d)
    (e : d'.marks = d.marks) : Λ.Faithful d' := by
  unfold PlaneLattice.Faithful Diagram.dots Diagram.marksWhere at *
  rw [e]
  exact h

/-- The points of a faithful plot of the single sequence `f`, where `f` agrees with `g`, are
exactly `(0, n, point n (g n))` for the `n` of the range. -/
theorem SeqPlot.data_iff {P : SeqPlot} {L : SeqLayout} {d : Diagram} (h : P.Faithful L d)
    {s : String} {f : ℕ → ℚ} (hs : P.series = [(s, f)]) {g : ℕ → ℚ} (hg : ∀ n, f n = g n)
    (k n : ℕ) (p : QPoint) :
    (k, n, p) ∈ d.data ↔ k = 0 ∧ P.lo ≤ n ∧ n ≤ P.hi ∧ p = SeqPlot.point L n (g n) := by
  rw [h.1, SeqPlot.mem_data, hs]
  constructor
  · rintro ⟨s', f', hk, hlo, hhi, rfl⟩
    match k, hk with
    | 0, hk =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨-, rfl⟩ := hk
      exact ⟨rfl, hlo, hhi, by rw [hg]⟩
  · rintro ⟨rfl, hlo, hhi, rfl⟩
    exact ⟨s, f, rfl, hlo, hhi, by rw [hg]⟩

/-- Every cell of an Ulam spiral is marked by the predicate at its number and has the text of
its number when `numbers`, no text otherwise. -/
theorem mem_ulamCells {count : ℕ} {p : ℕ → Bool} {numbers : Bool} {c : NumberCell}
    (h : c ∈ ulamCells count p numbers) :
    c.marked = p c.key ∧ c.text = if numbers then toString c.key else "" := by
  simp only [ulamCells, List.mem_map] at h
  obtain ⟨i, -, rfl⟩ := h
  exact ⟨rfl, rfl⟩

/-- The number of `a < n` that pass the Boolean test `q`, a test for `p`, is the number of
elements of `range n` that satisfy `p`. -/
theorem card_filter_range (p : ℕ → Prop) [DecidablePred p] (q : ℕ → Bool)
    (hq : ∀ a, q a = true ↔ p a) (n : ℕ) :
    ((List.range n).filter q).length = #{a ∈ range n | p a} := by
  rw [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]
  congr 1
  exact List.filter_congr fun a _ => by rw [Bool.eq_iff_iff, hq, decide_eq_true_iff]

/-- `a` is a square modulo `p` exactly when some `x < p` has `x² ≡ a`. -/
theorem isSquare_iff_any (p : ℕ) [NeZero p] (a : ℕ) :
    IsSquare (a : ZMod p) ↔ (List.range p).any (fun x => x * x % p == a % p) = true := by
  simp only [List.any_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y.val, ZMod.val_lt y, ?_⟩
    have : ((y.val * y.val : ℕ) : ZMod p) = (a : ZMod p) := by simp [hy]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).1 this
  · rintro ⟨x, -, hx⟩
    refine ⟨(x : ZMod p), ?_⟩
    have := (ZMod.natCast_eq_natCast_iff' (x * x) a p).2 hx
    push_cast at this
    exact this.symm

/-- A Gaussian integer whose norm is a prime number is a Gaussian prime. -/
theorem prime_of_norm_prime {x : GaussianInt} (h : x.norm.natAbs.Prime) : Prime x := by
  refine (irreducible_iff_prime).1 ⟨fun hu => ?_, fun y z hyz => ?_⟩
  · rw [← Zsqrtd.norm_eq_one_iff] at hu; rw [hu] at h; exact Nat.not_prime_one h
  · have hn : x.norm.natAbs = y.norm.natAbs * z.norm.natAbs := by
      rw [hyz, Zsqrtd.norm_mul, Int.natAbs_mul]
    rw [hn] at h
    rcases Nat.prime_mul_iff.1 h with ⟨-, hz⟩ | ⟨-, hy⟩
    · exact .inr (Zsqrtd.norm_eq_one_iff.1 hz)
    · exact .inl (Zsqrtd.norm_eq_one_iff.1 hy)

/-- A Gaussian integer that is the product of two of norm greater than one is not prime. -/
theorem not_prime_of_mul {x y z : GaussianInt} (h : x = y * z) (hy : 1 < y.norm.natAbs)
    (hz : 1 < z.norm.natAbs) : ¬ Prime x := fun hx => by
  rcases hx.irreducible.isUnit_or_isUnit h with hu | hu
  · rw [← Zsqrtd.norm_eq_one_iff] at hu; omega
  · rw [← Zsqrtd.norm_eq_one_iff] at hu; omega

/-- A factor of `a + b i` with components in `[-3, 3]` and the cofactor, both of norm greater
than one, if there is one: the first `c + d i` whose norm divides both components of
`(a + b i)(c - d i)`. -/
def gaussianWitness (a b : ℤ) : Option (ℤ × ℤ × ℤ × ℤ) :=
  let box := (List.range 7).map fun (k : ℕ) => (k : ℤ) - 3
  (box.flatMap fun c => box.map fun d => (c, d)).findSome? fun (c, d) =>
    let n := c * c + d * d
    let e := (a * c + b * d) / n
    let f := (b * c - a * d) / n
    if 1 < n && c * e - d * f == a && c * f + d * e == b && 1 < e * e + f * f then
      some (c, d, e, f) else none

/-- Whether `a + b i` is shown not to be prime: it is `0`, a unit, or has a factor witness. -/
def notPrimeShown (a b : ℤ) : Bool :=
  (a == 0 && b == 0) || a * a + b * b == 1 || (gaussianWitness a b).isSome

/-- What `notPrimeShown` shows holds: `a + b i` is not prime. -/
theorem not_prime_of_shown (a b : ℤ) (h : notPrimeShown a b = true) :
    ¬ Prime (⟨a, b⟩ : GaussianInt) := by
  unfold notPrimeShown at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
  rcases h with (⟨rfl, rfl⟩ | h1) | ⟨⟨c0, d0, e0, f0⟩, hw⟩
  · exact fun hp => hp.ne_zero rfl
  · intro hp
    apply hp.not_isUnit
    rw [← Zsqrtd.norm_eq_one_iff, Zsqrtd.norm_def]
    have : a * a - -1 * b * b = 1 := by linarith
    simp only [this]; rfl
  · unfold gaussianWitness at hw
    obtain ⟨⟨c, d⟩, -, hw⟩ := List.exists_of_findSome?_eq_some hw
    simp only at hw
    split_ifs at hw with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨h1, h2, he, hf⟩ := hw
    subst h1 h2
    set e := (a * c + b * d) / (c * c + d * d)
    set f := (b * c - a * d) / (c * c + d * d)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    obtain ⟨⟨⟨hn, h1⟩, h2⟩, h3⟩ := hc
    refine not_prime_of_mul (y := ⟨c, d⟩) (z := ⟨e, f⟩) ?_ ?_ ?_
    · ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> linarith
    · rw [Zsqrtd.norm_def]; simp; omega
    · rw [Zsqrtd.norm_def]; simp; omega

/-- A Gaussian integer associated to a prime is prime: `x` is `k (c + d i)` for a unit
`c + d i`. -/
theorem prime_of_unit_mul {k x : GaussianInt} (hk : Prime k) (c d : ℤ) (hu : c * c + d * d = 1)
    (hx : x = k * ⟨c, d⟩) : Prime x := by
  have hunit : IsUnit (⟨c, d⟩ : GaussianInt) := by
    rw [← Zsqrtd.norm_eq_one_iff, Zsqrtd.norm_def]
    have : c * c - -1 * d * d = 1 := by linarith
    simp only [this]; rfl
  rw [hx]
  exact (associated_mul_unit_right k _ hunit).prime hk

/-- The index of a point of the box `[-r, r]²` in a grid of `(2 r + 1)²` places. -/
def boxIndex (r : ℕ) (p : ℤ × ℤ) : ℕ := (p.1 + r).toNat * (2 * r + 1) + (p.2 + r).toNat

/-- Whether a point lies in the box `[-r, r]²`. -/
def inBox (r : ℕ) (p : ℤ × ℤ) : Bool :=
  decide (-(r : ℤ) ≤ p.1) && decide (p.1 ≤ r) && decide (-(r : ℤ) ≤ p.2) && decide (p.2 ≤ r)

/-- Whether the points lie in the box `[-r, r]²`, no two at one place: each is checked against
the bit mask `m` of the places taken before it, in time linear in the number of points (the
kernel evaluates the bit operations on numbers directly). -/
def distinctInBox (r : ℕ) : List (ℤ × ℤ) → (m : ℕ := 0) → Bool
  | [], _ => true
  | p :: ps, m => inBox r p && !m.testBit (boxIndex r p) &&
      distinctInBox r ps (m ||| 1 <<< boxIndex r p)

/-- What `distinctInBox` checks holds: the points are in the box, none of them takes a place of
the mask, and no two are equal. -/
theorem nodup_of_distinctInBox (r : ℕ) : ∀ (ps : List (ℤ × ℤ)) (m : ℕ),
    distinctInBox r ps m = true →
      (∀ q ∈ ps, inBox r q = true ∧ m.testBit (boxIndex r q) = false) ∧ ps.Nodup
  | [], _, _ => by simp
  | p :: ps, m, h => by
    simp only [distinctInBox, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hp, hm⟩, hrest⟩ := h
    obtain ⟨hq, hnd⟩ := nodup_of_distinctInBox r ps _ hrest
    have hbit : ∀ q ∈ ps, boxIndex r q ≠ boxIndex r p ∧ m.testBit (boxIndex r q) = false := by
      intro q hqm
      have := (hq q hqm).2
      rw [Nat.testBit_or, Bool.or_eq_false_iff, Nat.one_shiftLeft, Nat.testBit_two_pow] at this
      exact ⟨fun e => by simp [e] at this, this.1⟩
    refine ⟨fun q hqm => ?_, List.nodup_cons.2 ⟨fun hpm => ?_, hnd⟩⟩
    · rcases List.mem_cons.1 hqm with rfl | hqm
      · exact ⟨hp, hm⟩
      · exact ⟨(hq q hqm).1, (hbit q hqm).2⟩
    · exact (hbit p hpm).1 rfl

end PILeanMathlib
