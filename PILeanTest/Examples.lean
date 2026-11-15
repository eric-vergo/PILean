/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plot.Figure

/-!
# The example gallery

Figures specified as Lean values, written to `examples/*.svg` by `lake exe pilean-gallery` and
compared with those files by `lake test` (the files are the goldens). The data figures plot
values computed here, from the definitions below.
-/

namespace PILeanTest.Examples

open PILean PILean.Plot

/-- The number of primes up to `n` (trial division; `n` is small here). -/
def primeCount (n : Nat) : Nat :=
  ((List.range (n + 1)).filter fun k =>
    k ≥ 2 && (List.range (k.sqrt + 1)).all fun d => d < 2 || k % d != 0).length

/-- The number of steps of the Collatz map `n ↦ n/2` (even) or `3n + 1` (odd) that bring `n` to
1, with at most `fuel` steps. -/
def collatzSteps (n : Nat) (fuel : Nat := 1000) : Nat := Id.run do
  let mut m := n
  let mut k := 0
  for _ in [0:fuel] do
    if m ≤ 1 then break
    m := if m % 2 == 0 then m / 2 else 3 * m + 1
    k := k + 1
  return k

/-- The constant π. -/
def pi : Float := 3.141592653589793

/-- Two trigonometric functions and the cardinal sine on `[-2π, 2π]`. -/
def functions : Figure where
  title := "Trigonometric functions"
  xLabel := "x"
  yLabel := "y"
  xDomain := some (-2 * pi, 2 * pi)
  yDomain := some (-1.25, 1.25)
  marks := #[.function "sin x" Float.sin (-2 * pi) (2 * pi),
    .function "cos x" Float.cos (-2 * pi) (2 * pi),
    .function "sin x / x" (fun x => if x == 0 then 1 else x.sin / x) (-2 * pi) (2 * pi)]

/-- The prime-counting function against `n / ln n`. -/
def primes : Figure where
  title := "Counting primes"
  xLabel := "n"
  yLabel := "number of primes up to n"
  marks := #[.line "π(n)" ((List.range 101).toArray.map fun i =>
      ⟨(10 * i).toFloat, (primeCount (10 * i)).toFloat⟩),
    .function "n / ln n" (fun x => x / x.log) 3 1000]

/-- Collatz stopping times of 1 to 40, as a data line with markers. -/
def collatz : Figure where
  title := "Collatz stopping times"
  xLabel := "n"
  yLabel := "steps to reach 1"
  marks := #[.line "steps" ((List.range 40).toArray.map fun i =>
    ⟨(i + 1).toFloat, (collatzSteps (i + 1)).toFloat⟩) (markers := true)]

/-- The gallery: file name and figure. -/
def gallery : Array (String × Figure) :=
  #[("function-plot.svg", functions), ("primes-line-plot.svg", primes),
    ("collatz-data-plot.svg", collatz)]

end PILeanTest.Examples
