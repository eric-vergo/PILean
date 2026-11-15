/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# Exact rationals and sample grids

Everything a plot or an animation says about a *value* can be stated exactly, before any
floating-point number appears. This file is that exact layer: the sample grid of a function, over
the rational numbers `Rat` of Lean's core library.

* `Rat` is a fraction in lowest terms, so two rationals are the same number exactly when they
  are equal (`=`), and every theorem here is an equality.
* `Exact.grid lo hi n` is the list of the `n + 1` points `lo + k (hi - lo) / n`, `k = 0, …, n`
  (the single point `lo` when `n = 0`), and `Exact.samples f lo hi n` pairs each with the value
  of `f`.
* `Exact.toFloat` is where floating point begins: the one place an exact value becomes a `Float`.

The names live in the namespace `PILean.Exact`, not in `Rat`, so that they cannot collide with
the declarations other libraries add to `Rat`.

## Main definitions

* `Exact.toFloat`.
* `Exact.gridStep`, `Exact.gridPoint`, `Exact.grid`, `Exact.samples`.

## Main results

* `Exact.grid_length`, `Exact.grid_getElem`: the grid has `n + 1` points, the `k`-th being
  `gridPoint`.
* `Exact.gridPoint_eq`: for `0 < n` the `k`-th point is `lo + k (hi - lo) / n`.
* `Exact.gridPoint_zero`, `Exact.gridPoint_last`: the grid starts at `lo` and ends at `hi`.
* `Exact.mem_samples`: a pair is a sample exactly when its first part is a grid point and its
  second part the value of `f` there.
-/

namespace PILean

namespace Exact

/-- The quotient of the numerator and the denominator of the rational number (in lowest terms),
each converted to a `Float`. When both have at most 53 significant bits the two conversions are
exact and the result is their quotient as floating-point division rounds it; nothing here proves
that (see `docs/PROOFS.md`). This is where floating point begins. -/
def toFloat (q : Rat) : Float := Float.ofInt q.num / q.den.toFloat

/-! ### Sample grids -/

/-- The step `(hi - lo) / n` of the grid of `n` equal steps from `lo` to `hi` (for `n = 0`, the
step of one piece, `hi - lo`). -/
def gridStep (lo hi : Rat) (n : Nat) : Rat := (hi - lo) / (max n 1 : Nat)

/-- The `k`-th point of the grid of `n` equal steps from `lo` to `hi`: `k` steps after `lo`. -/
def gridPoint (lo hi : Rat) (n k : Nat) : Rat := lo + k * gridStep lo hi n

/-- The grid of `n + 1` points `lo + k (hi - lo) / n`, `k = 0, …, n`, in order (just `[lo]` when
`n = 0`). -/
def grid (lo hi : Rat) (n : Nat) : List Rat := (List.range (n + 1)).map (gridPoint lo hi n)

/-- The exact samples of `f` on the grid: each grid point with the value of `f` there. -/
def samples (f : Rat → Rat) (lo hi : Rat) (n : Nat) : List (Rat × Rat) :=
  (grid lo hi n).map fun x => (x, f x)

/-- The grid has `n + 1` points. -/
theorem grid_length (lo hi : Rat) (n : Nat) : (grid lo hi n).length = n + 1 := by
  simp [grid]

/-- The `k`-th point of the grid (`k ≤ n`) is `gridPoint lo hi n k`. -/
theorem grid_getElem (lo hi : Rat) (n k : Nat) (h : k < (grid lo hi n).length) :
    (grid lo hi n)[k] = gridPoint lo hi n k := by
  simp [grid]

/-- For `0 < n` the step of the grid is `(hi - lo) / n`. -/
theorem gridStep_eq (lo hi : Rat) (n : Nat) (hn : 0 < n) : gridStep lo hi n = (hi - lo) / n := by
  rw [gridStep, Nat.max_eq_left hn]

/-- For `0 < n` the `k`-th grid point is `lo + k · (hi - lo) / n` (for every `k`; the grid
uses `k ≤ n`). -/
theorem gridPoint_eq (lo hi : Rat) (n k : Nat) (hn : 0 < n) :
    gridPoint lo hi n k = lo + k * ((hi - lo) / n) := by
  rw [gridPoint, gridStep_eq lo hi n hn]

/-- The grid starts at `lo`. -/
theorem gridPoint_zero (lo hi : Rat) (n : Nat) : gridPoint lo hi n 0 = lo := by
  simp [gridPoint, Rat.zero_mul, Rat.add_zero]

/-- The grid of at least one step ends at `hi`. -/
theorem gridPoint_last (lo hi : Rat) (n : Nat) (hn : 0 < n) : gridPoint lo hi n n = hi := by
  have h : (n : Rat) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.1 hn
  rw [gridPoint_eq lo hi n n hn]
  grind

/-- Consecutive grid points differ by the step of the grid. -/
theorem gridPoint_succ (lo hi : Rat) (n k : Nat) :
    gridPoint lo hi n (k + 1) - gridPoint lo hi n k = gridStep lo hi n := by
  simp only [gridPoint]
  push_cast
  grind

/-- A pair is an exact sample exactly when its first part is a point of the grid and its second
part is the value of `f` there. -/
theorem mem_samples (f : Rat → Rat) (lo hi : Rat) (n : Nat) (p : Rat × Rat) :
    p ∈ samples f lo hi n ↔ p.1 ∈ grid lo hi n ∧ p.2 = f p.1 := by
  simp only [samples, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨p.1, h1, Prod.ext rfl h2.symm⟩

/-- The first parts of the exact samples are exactly the grid, in order. -/
theorem samples_fst (f : Rat → Rat) (lo hi : Rat) (n : Nat) :
    (samples f lo hi n).map Prod.fst = grid lo hi n := by
  simp [samples, Function.comp_def]

/-- The second parts of the exact samples are the values of `f` on the grid, in order. -/
theorem samples_snd (f : Rat → Rat) (lo hi : Rat) (n : Nat) :
    (samples f lo hi n).map Prod.snd = (grid lo hi n).map f := by
  simp [samples, Function.comp_def]

/-- There are `n + 1` exact samples. -/
theorem samples_length (f : Rat → Rat) (lo hi : Rat) (n : Nat) :
    (samples f lo hi n).length = n + 1 := by
  simp [samples, grid_length]

/-- The hypotheses can be met: the grid of four steps on `[0, 1]` is `0, 1/4, 1/2, 3/4, 1`. -/
example : grid 0 1 4 = [0, 1 / 4, 1 / 2, 3 / 4, 1] := by decide +kernel

end Exact

end PILean
