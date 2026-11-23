/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Diagram.Lattice
import PILean.Diagram.Sequence
import PILean.Trust.Attr

/-!
# Figures of number theory tied to Mathlib's objects: the figures

The figures, built with PILean only from plain functions on the natural numbers and the
integers (this module imports nothing from Mathlib). `PILeanMathlib.Examples.NumberTheory` proves
that each draws Mathlib's object: Euler's totient `Nat.totient` and the number of divisors
`(Nat.divisors n).card` (`σ₀`) on `1, …, 100`, the prime-counting function `Nat.primeCounting`
on `2, …, 100` against the comparison curve `n / (Hₙ - 1)` (`harmonic`), the primes
(`Nat.Prime`) on an Ulam spiral of `1, …, 441`, the quadratic residues modulo the primes
`3, 5, 7, 11, 13` with their Legendre symbols (`IsSquare`, `legendreSym`), and the Gaussian
primes (`Prime` in `GaussianInt`) among the Gaussian integers `a + b i` with `|a|, |b| ≤ 7`.
-/

namespace PILeanMathlib.Examples

open PILean PILean.Diagram

/-- Euler's totient: the number of `a < n` with `gcd n a = 1`. -/
def totient' (n : Nat) : Nat := ((List.range n).filter fun a => Nat.gcd n a == 1).length

/-- The number of divisors of `n`: the `d` from `1` to `n` that divide it. -/
def divisorCount (n : Nat) : Nat := ((List.range' 1 n).filter fun d => n % d == 0).length

/-- Whether `n` is prime: at least 2 and no divisor among `2, …, n - 1`. -/
def isPrime' (n : Nat) : Bool := 2 ≤ n && (List.range' 2 (n - 2)).all fun d => n % d != 0

/-- The number of primes up to `n`. -/
def primeCount (n : Nat) : Nat := ((List.range (n + 1)).filter isPrime').length

/-- The harmonic number `Hₙ = 1 + 1/2 + ⋯ + 1/n`. -/
def harmonic' : Nat → Rat
  | 0 => 0
  | n + 1 => harmonic' n + 1 / (n + 1)

/-- The plot of the totient on `1, …, 100`. -/
def totientPlot : SeqPlot := { lo := 1, hi := 100, series := [("φ(n)", fun n => totient' n)] }

/-- Euler's totient. -/
@[figure]
def totientFigure : Diagram :=
  { totientPlot.figure with title := "Euler's totient φ(n), 1 ≤ n ≤ 100" }

/-- The plot of the number of divisors on `1, …, 100`. -/
def divisorPlot : SeqPlot :=
  { lo := 1, hi := 100, series := [("d(n) = σ₀(n)", fun n => divisorCount n)] }

/-- The number of divisors. -/
@[figure]
def divisorFigure : Diagram :=
  { divisorPlot.figure with title := "The number of divisors d(n), 1 ≤ n ≤ 100" }

/-- The plot of the prime-counting function on `2, …, 100` and the curve `n / (Hₙ - 1)`. -/
def primeCountPlot : SeqPlot :=
  { lo := 2, hi := 100, series := [("π(n)", fun n => primeCount n)],
    curves := [("n / (Hₙ − 1)", fun n => n / (harmonic' n - 1))] }

/-- The prime-counting function against a comparison curve. -/
@[figure]
def primeCountFigure : Diagram :=
  { primeCountPlot.figure with title := "π(n) and n / (Hₙ − 1), 2 ≤ n ≤ 100" }

/-- The Ulam spiral of `1, …, 441`, `1` at the centre, with the primes filled. -/
def ulamPlot : CellPlot := { cells := ulamCells 441 isPrime', solid := true }

/-- The primes on the Ulam spiral. -/
@[figure]
def ulamFigure : Diagram :=
  { ulamPlot.figure with title := "The primes up to 441 on the Ulam spiral", width := 360 }

/-- The primes of the table of residues. -/
def residuePrimes : List Nat := [3, 5, 7, 11, 13]

/-- The Legendre symbol `(a / p)` as a search: `0` when `p ∣ a`, `1` when `a` is a square modulo
`p`, `-1` otherwise. -/
def legendre' (p a : Nat) : Int :=
  if a % p = 0 then 0 else if (List.range p).any (fun x => x * x % p == a % p) then 1 else -1

/-- The text of a Legendre symbol: `0`, `1` or `−1` (with the minus sign `−`). -/
def symbolText (s : Int) : String := if s < 0 then "−" ++ toString s.natAbs else toString s

/-- The cell of `a` in row `i` (the prime `p`) of the table of residues. -/
def residueCell (p i a : Nat) : NumberCell :=
  { key := 100 * p + a, pos := ((a : Int), -(i : Int)), marked := legendre' p a == 1,
    text := symbolText (legendre' p a) }

/-- The table of residues: row `i` for the `i`-th prime `p`, cell `a` for `0 ≤ a < p`, marked when
`a` is a nonzero square modulo `p`, with the Legendre symbol written in it; the primes at the
left and the residues `a` above. -/
def residuePlot : CellPlot where
  cells := residuePrimes.zipIdx.flatMap fun (p, i) => (List.range p).map fun a =>
    residueCell p i a
  headings := residuePrimes.zipIdx.map (fun (p, i) => (s!"p = {p}", (-1, 1 / 2 - (i : Rat)))) ++
    ("a", (-1, 3 / 2)) ::
      (List.range 13).map fun (a : Nat) => (toString a, ((a : Rat) + 1 / 2, 3 / 2))

/-- The quadratic residues. -/
@[figure]
def residueFigure : Diagram :=
  { residuePlot.figure with
    title := "Quadratic residues and Legendre symbols modulo 3, 5, 7, 11, 13", width := 520 }

/-- Whether the Gaussian integer `a + b i` is a Gaussian prime: on an axis, `|a + b|` is a prime
`≡ 3 (mod 4)`; elsewhere `a² + b²` is prime. -/
def gaussianPrime (a b : Int) : Bool :=
  if a = 0 || b = 0 then
    let k := (a + b).natAbs
    isPrime' k && k % 4 == 3
  else isPrime' (a.natAbs ^ 2 + b.natAbs ^ 2)

/-- The Gaussian integers `a + b i` with `|a|, |b| ≤ 7`, the Gaussian primes marked. -/
def gaussianLattice : PlaneLattice :=
  { w1 := (1, 0), w2 := (0, 1), lo := (-7, -7), hi := (7, 7), marked := gaussianPrime,
    plainInk := .faint }

/-- The Gaussian primes. -/
@[figure]
def gaussianFigure : Diagram :=
  { gaussianLattice.figure with title := "The Gaussian primes a + bi with |a|, |b| ≤ 7" }

/-- The figures by file stem. -/
def numberTheoryFigures : Array (String × Diagram) :=
  #[("totient", totientFigure), ("divisor-count", divisorFigure), ("prime-count", primeCountFigure),
    ("ulam", ulamFigure), ("residues", residueFigure), ("gaussian-primes", gaussianFigure)]

end PILeanMathlib.Examples
