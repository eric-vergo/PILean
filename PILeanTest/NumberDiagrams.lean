/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Trust.Attr
import PILeanTest.Diagrams

/-!
# The gallery of plots of sequences, grids of numbers and lattices, their specifications and checks

Figures of the kinds `SeqPlot`, `CellPlot` and `PlaneLattice`, each with the attribute `figure`
and a specification linked by `figure_proves`: the figure is drawn faithfully (every mark
accounted for by the kind's `Faithful`), and what it draws is written out and checked by the
kernel (the values of a sequence on its range, the numbers marked in a grid, the lattice points
drawn and those marked). Changing the data breaks the specification
(`PILeanTest.SpecMutations`). The package `pilean-mathlib` ties figures of these kinds to
Mathlib's functions and predicates.

`checks` holds what the theorems do not: each predicate refuses diagrams with a planted fault in
every class of mark (a point, its colour, a curve, an axis, a tick, a tick's label, a legend's
sample and name, a cell, its colour, its text, a heading, a lattice point, its colour, the
parallelogram), the figures pass the layout checks of plane figures in both themes (a plot's
points may stand closer than markers of a geometric figure, but their discs never overlap), and
hostile data is refused within the caps.
-/

namespace PILeanTest.NumberDiagrams

open PILean PILean.Diagram PILeanTest.Diagrams

/-! ### Euler's totient -/

/-- Euler's totient: the number of `a < n` with `gcd n a = 1`. -/
def phi (n : Nat) : Nat := ((List.range n).filter fun a => Nat.gcd n a == 1).length

/-- Euler's totient on `1, …, 100`. -/
def totientPlot : SeqPlot := { lo := 1, hi := 100, series := [("φ(n)", fun n => phi n)] }

/-- The plot of Euler's totient. -/
@[figure]
def totient : Diagram := { totientPlot.figure with title := "Euler's totient φ(n), 1 ≤ n ≤ 100" }

/-- The figure plots Euler's totient faithfully on `1, …, 100`: its points are exactly
`(n, φ(n))` (`SeqPlot.mem_data`), with the values written out, under the one name `φ(n)`, and it
draws no curve. -/
theorem totient_spec :
    totientPlot.Faithful totientPlot.layout totient ∧
    totientPlot.lo = 1 ∧ totientPlot.hi = 100 ∧ totientPlot.names = ["φ(n)"] ∧
    totientPlot.series.map (fun s => totientPlot.indices.map s.2) =
      [[1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4, 12, 6, 8, 8, 16, 6, 18, 8, 12, 10, 22, 8, 20, 12, 18,
        12, 28, 8, 30, 16, 20, 16, 24, 12, 36, 18, 24, 16, 40, 12, 42, 20, 24, 22, 46, 16, 42, 20,
        32, 24, 52, 18, 40, 24, 36, 28, 58, 16, 60, 30, 36, 32, 48, 20, 66, 32, 44, 24, 70, 24, 72,
        36, 40, 36, 60, 24, 78, 32, 54, 40, 82, 24, 64, 42, 56, 40, 88, 24, 72, 44, 60, 46, 72, 32,
        96, 42, 60, 40]] ∧
    totientPlot.curves.length = 0 := by
  sorry

figure_proves totient totient_spec

/-! ### A sieve of Eratosthenes -/

/-- Whether `n` is prime: at least 2 and no divisor among `2, …, n - 1`. -/
def isPrime (n : Nat) : Bool := 2 ≤ n && (List.range' 2 (n - 2)).all fun d => n % d != 0

/-- The numbers `1, …, 100` in ten rows of ten, `1` at the top left, each written in its cell,
the primes marked. -/
def sievePlot : CellPlot where
  cells := (List.range 100).map fun i =>
    { key := i + 1, pos := ((i % 10 : Nat), -((i / 10 : Nat) : Int)), marked := isPrime (i + 1),
      text := toString (i + 1) }

/-- The sieve. -/
@[figure]
def sieve : Diagram :=
  { sievePlot.figure with title := "The primes up to 100", width := 360 }

/-- The figure draws the hundred cells faithfully: their keys are `1, …, 100`, each written as
itself, in ten rows of ten, and the marked ones are exactly the 25 primes below 100 (written
out); it has no heading. -/
theorem sieve_spec :
    sievePlot.Faithful sieve ∧
    sievePlot.cells.map (·.key) = List.range' 1 100 ∧
    sievePlot.cells.all (fun c => c.text == toString c.key &&
      c.pos == ((((c.key - 1) % 10 : Nat) : Int), -(((c.key - 1) / 10 : Nat) : Int))) = true ∧
    (sievePlot.cells.filter (·.marked)).map (·.key) =
      [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
        97] ∧
    sievePlot.headings = [] ∧ sievePlot.solid = false := by
  sorry

figure_proves sieve sieve_spec

/-! ### The Gaussian primes -/

/-- Whether the Gaussian integer `a + b i` is a Gaussian prime: on an axis, `|a + b|` is a prime
`≡ 3 (mod 4)`; elsewhere `a² + b²` is prime. -/
def gaussianPrime (a b : Int) : Bool :=
  if a = 0 || b = 0 then
    let k := (a + b).natAbs
    isPrime k && k % 4 == 3
  else isPrime (a.natAbs ^ 2 + b.natAbs ^ 2)

/-- The Gaussian integers `a + b i` with `|a|, |b| ≤ 4`, the Gaussian primes marked. -/
def gaussianLattice : PlaneLattice :=
  { w1 := (1, 0), w2 := (0, 1), lo := (-4, -4), hi := (4, 4), marked := gaussianPrime,
    plainInk := .faint }

/-- The Gaussian primes. -/
@[figure]
def gaussian : Diagram :=
  { gaussianLattice.figure with title := "The Gaussian primes a + bi with |a|, |b| ≤ 4" }

/-- The figure draws the lattice `ℤ + ℤ i` faithfully in the window `[-4, 4]²`: its 81 points
are the `a + b i` with `|a|, |b| ≤ 4`, the marked ones (in accent 1, the others faint) exactly
the 32 Gaussian primes among them (written out). -/
theorem gaussian_spec :
    gaussianLattice.Faithful gaussian ∧
    gaussianLattice.w1 = (1, 0) ∧ gaussianLattice.w2 = (0, 1) ∧
    gaussianLattice.lo = (-4, -4) ∧ gaussianLattice.hi = (4, 4) ∧
    gaussianLattice.points = (List.range 9).flatMap (fun (a : Nat) => (List.range 9).map
      fun (b : Nat) => ((a : Int) - 4, (b : Int) - 4)) ∧
    gaussianLattice.plainInk = .faint ∧
    gaussianLattice.points.filter (fun (a, b) => gaussianLattice.marked a b) =
      [(-4, -1), (-4, 1), (-3, -2), (-3, 0), (-3, 2), (-2, -3), (-2, -1), (-2, 1), (-2, 3),
        (-1, -4), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 4), (0, -3), (0, 3), (1, -4),
        (1, -2), (1, -1), (1, 1), (1, 2), (1, 4), (2, -3), (2, -1), (2, 1), (2, 3), (3, -2),
        (3, 0), (3, 2), (4, -1), (4, 1)] := by
  sorry

figure_proves gaussian gaussian_spec

/-! ### A lattice with a skew basis -/

/-- The lattice `ℤ (3/2, 1/2) + ℤ (1/2, 3/2)` in the window `[-3, 3]²`. -/
def skewLattice : PlaneLattice :=
  { w1 := (3 / 2, 1 / 2), w2 := (1 / 2, 3 / 2), lo := (-3, -3), hi := (3, 3) }

/-- The skew lattice. -/
@[figure]
def skew : Diagram :=
  { skewLattice.figure with title := "The lattice ℤ(3/2, 1/2) + ℤ(1/2, 3/2)" }

/-- The figure draws the lattice `ℤ (3/2, 1/2) + ℤ (1/2, 3/2)` faithfully in `[-3, 3]²`: its
points are `m ω₁ + n ω₂` for the coefficients written out, none marked. -/
theorem skew_spec :
    skewLattice.Faithful skew ∧
    skewLattice.w1 = (3 / 2, 1 / 2) ∧ skewLattice.w2 = (1 / 2, 3 / 2) ∧
    skewLattice.lo = (-3, -3) ∧ skewLattice.hi = (3, 3) ∧
    skewLattice.points = [(-3, 3), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2),
      (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 0), (1, 1), (2, -2), (2, -1),
      (2, 0), (3, -3)] ∧
    skewLattice.points.all (fun (m, n) => !skewLattice.marked m n) = true ∧
    skewLattice.plainInk = .ink := by
  sorry

figure_proves skew skew_spec

/-! ### The gallery and the checks -/

/-- The figures by file stem. -/
def figures : Array (String × Diagram) :=
  #[("diagram-totient", totient), ("diagram-sieve", sieve), ("diagram-gaussian-primes", gaussian),
    ("diagram-skew-lattice", skew)]

/-- The gallery: each figure light and dark, as plane figures by file name. -/
def gallery : Array (String × Plane.Figure) :=
  figures.map (fun (n, d) => (n ++ ".svg", d.toPlane)) ++
    figures.map (fun (n, d) => (n ++ "-dark.svg", d.dark.toPlane))

end PILeanTest.NumberDiagrams
