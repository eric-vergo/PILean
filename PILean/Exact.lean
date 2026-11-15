/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# Exact rationals and sample grids

Everything a plot or an animation says about a *value* can be stated exactly, before any
floating-point number appears. This file is that exact layer: a small rational type `Q` and the
sample grid of a function.

* `Q` is an integer numerator over a positive natural denominator. It is *not* normalised, so
  `2/4` and `1/2` are different values of `Q`; the relations `Q.Equiv` and `Q.lt` compare the
  fractions they stand for (by cross multiplication), and every theorem about arithmetic is
  stated with `Q.Equiv`.
* `Q.grid lo hi n` is the list of the `n + 1` points `lo + k (hi - lo) / n`, `k = 0, …, n`
  (the single point `lo` when `n = 0`), and `Q.samples f lo hi n` pairs each with the value of
  `f`.
* `Q.toFloat` is where floating point begins: the one place an exact value becomes a `Float`.

## Main definitions

* `Q`, `Q.ofInt`, `Q.add`, `Q.sub`, `Q.mul`, `Q.Equiv`, `Q.lt`, `Q.toFloat`.
* `Q.gridPoint`, `Q.grid`, `Q.samples`.

## Main results

* `Q.grid_length`, `Q.grid_getElem`: the grid has `n + 1` points, the `k`-th being `gridPoint`.
* `Q.gridPoint_equiv`: for `k ≤ n` the `k`-th point is `lo + k (hi - lo) / n`.
* `Q.gridPoint_zero`, `Q.gridPoint_last`: the grid starts at `lo` and ends at `hi`.
* `Q.mem_samples`: a pair is a sample exactly when its first part is a grid point and its second
  part the value of `f` there.
-/

namespace PILean

/-- An exact rational number: `num / den` with a positive denominator. Not normalised; compare
with `Q.Equiv`. -/
structure Q where
  /-- The numerator. -/
  num : Int
  /-- The denominator. -/
  den : Nat
  /-- The denominator is positive. -/
  den_pos : 0 < den

namespace Q

/-- The integer `a` as a fraction with denominator one. -/
def ofInt (a : Int) : Q := ⟨a, 1, Nat.one_pos⟩

/-- The natural number `a` as a fraction with denominator one. -/
def ofNat (a : Nat) : Q := ofInt a

/-- The fraction `a / b` of an integer and a positive natural number. -/
def ofFrac (a : Int) (b : Nat) (h : 0 < b := by decide) : Q := ⟨a, b, h⟩

/-- The sum of two fractions (`a/b + c/d = (ad + cb)/(bd)`). -/
def add (a b : Q) : Q :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

/-- The difference of two fractions. -/
def sub (a b : Q) : Q :=
  ⟨a.num * b.den - b.num * a.den, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

/-- The product of two fractions. -/
def mul (a b : Q) : Q := ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

instance : Add Q := ⟨add⟩
instance : Sub Q := ⟨sub⟩
instance : Mul Q := ⟨mul⟩

/-- Two fractions stand for the same rational number (cross multiplication). -/
def Equiv (a b : Q) : Prop := a.num * b.den = b.num * a.den

/-- The fraction `a` is less than the fraction `b` as rational numbers. -/
def lt (a b : Q) : Prop := a.num * b.den < b.num * a.den

instance (a b : Q) : Decidable (Equiv a b) := inferInstanceAs (Decidable (_ = _))
instance (a b : Q) : Decidable (lt a b) := inferInstanceAs (Decidable (_ < _))

/-- The floating-point number nearest to the fraction: the numerator and the denominator are
converted (exactly, when both have at most 53 significant bits) and divided (correctly rounded).
This is where floating point begins. -/
def toFloat (a : Q) : Float := Float.ofInt a.num / a.den.toFloat

/-! ### Sample grids -/

/-- The `k`-th point of the grid of `n` equal steps from `lo` to `hi`:
`(lo (n - k) + hi k) / n`, as a fraction with denominator `lo.den · hi.den · n`; for `n = 0`
it is `lo`. -/
def gridPoint (lo hi : Q) (n k : Nat) : Q :=
  if h : n = 0 then lo
  else ⟨lo.num * hi.den * ((n : Int) - k) + hi.num * lo.den * k, lo.den * hi.den * n,
    Nat.mul_pos (Nat.mul_pos lo.den_pos hi.den_pos) (Nat.pos_of_ne_zero h)⟩

/-- The step `(hi - lo) / n` of the grid (for `n = 0`, the step of one piece, `hi - lo`). -/
def gridStep (lo hi : Q) (n : Nat) : Q :=
  ⟨hi.num * lo.den - lo.num * hi.den, lo.den * hi.den * n.max 1,
    Nat.mul_pos (Nat.mul_pos lo.den_pos hi.den_pos) (Nat.lt_of_lt_of_le Nat.one_pos
      (Nat.le_max_right _ _))⟩

/-- The grid of `n + 1` points `lo + k (hi - lo) / n`, `k = 0, …, n`, in order (just `[lo]` when
`n = 0`). -/
def grid (lo hi : Q) (n : Nat) : List Q := (List.range (n + 1)).map (gridPoint lo hi n)

/-- The exact samples of `f` on the grid: each grid point with the value of `f` there. -/
def samples (f : Q → Q) (lo hi : Q) (n : Nat) : List (Q × Q) :=
  (grid lo hi n).map fun x => (x, f x)

/-- The grid has `n + 1` points. -/
theorem grid_length (lo hi : Q) (n : Nat) : (grid lo hi n).length = n + 1 := by
  simp [grid]

/-- The `k`-th point of the grid (`k ≤ n`) is `gridPoint lo hi n k`. -/
theorem grid_getElem (lo hi : Q) (n k : Nat) (h : k < (grid lo hi n).length) :
    (grid lo hi n)[k] = gridPoint lo hi n k := by
  simp [grid]

/-- For `0 < n` the `k`-th grid point is `lo + k · (hi - lo) / n` (for every `k`; the grid
uses `k ≤ n`). -/
theorem gridPoint_equiv (lo hi : Q) (n k : Nat) (hn : 0 < n) :
    Equiv (gridPoint lo hi n k) (lo + ofNat k * gridStep lo hi n) := by
  have hn' : n ≠ 0 := Nat.pos_iff_ne_zero.1 hn
  have hmax : n.max 1 = n := Nat.max_eq_left hn
  simp only [gridPoint, hn', ↓reduceDIte, Equiv, HAdd.hAdd, Add.add, HMul.hMul, Mul.mul, add, mul,
    ofNat, ofInt, gridStep, hmax]
  push_cast
  grind

/-- The grid starts at `lo`. -/
theorem gridPoint_zero (lo hi : Q) (n : Nat) : Equiv (gridPoint lo hi n 0) lo := by
  by_cases hn : n = 0
  · simp [gridPoint, hn, Equiv]
  · simp only [gridPoint, hn, ↓reduceDIte, Equiv]
    push_cast
    grind

/-- The grid of at least one step ends at `hi`. -/
theorem gridPoint_last (lo hi : Q) (n : Nat) (hn : 0 < n) : Equiv (gridPoint lo hi n n) hi := by
  have hn' : n ≠ 0 := Nat.pos_iff_ne_zero.1 hn
  simp only [gridPoint, hn', ↓reduceDIte, Equiv]
  push_cast
  grind

/-- Consecutive grid points differ by the step `(hi - lo) / n`. -/
theorem gridPoint_succ (lo hi : Q) (n k : Nat) (hn : 0 < n) :
    Equiv (gridPoint lo hi n (k + 1) - gridPoint lo hi n k) (gridStep lo hi n) := by
  have hn' : n ≠ 0 := Nat.pos_iff_ne_zero.1 hn
  have hmax : n.max 1 = n := Nat.max_eq_left hn
  simp only [gridPoint, hn', ↓reduceDIte, Equiv, HSub.hSub, Sub.sub, sub, gridStep, hmax]
  push_cast
  grind

/-- A pair is an exact sample exactly when its first part is a point of the grid and its second
part is the value of `f` there. -/
theorem mem_samples (f : Q → Q) (lo hi : Q) (n : Nat) (p : Q × Q) :
    p ∈ samples f lo hi n ↔ p.1 ∈ grid lo hi n ∧ p.2 = f p.1 := by
  simp only [samples, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨p.1, h1, Prod.ext rfl h2.symm⟩

/-- The first parts of the exact samples are exactly the grid, in order. -/
theorem samples_fst (f : Q → Q) (lo hi : Q) (n : Nat) :
    (samples f lo hi n).map Prod.fst = grid lo hi n := by
  simp [samples, Function.comp_def]

/-- The second parts of the exact samples are the values of `f` on the grid, in order. -/
theorem samples_snd (f : Q → Q) (lo hi : Q) (n : Nat) :
    (samples f lo hi n).map Prod.snd = (grid lo hi n).map f := by
  simp [samples, Function.comp_def]

/-- There are `n + 1` exact samples. -/
theorem samples_length (f : Q → Q) (lo hi : Q) (n : Nat) :
    (samples f lo hi n).length = n + 1 := by
  simp [samples, grid_length]

/-- The hypotheses can be met: the grid of four steps on `[0, 1]` is `0, 1/4, 1/2, 3/4, 1`. -/
example : (grid (ofInt 0) (ofInt 1) 4).map (fun q => (q.num, q.den)) =
    [(0, 4), (1, 4), (2, 4), (3, 4), (4, 4)] := by decide

end Q

end PILean
