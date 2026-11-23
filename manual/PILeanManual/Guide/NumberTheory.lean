/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILean
import PILean.Trust.Attr
import PILeanVersoManual
import PILeanManual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open PILeanVerso.Manual
open PILeanManual

#doc (Manual) "Analysis and Number Theory" =>
%%%
tag := "number-theory"
%%%

```lean -show
namespace PILeanManual.NumberTheoryGuide
open PILean PILean.Diagram
```

The modules `PILean.Diagram.Sequence` and `PILean.Diagram.Lattice` draw sequences, grids of
numbers and lattices of the plane from the functions and predicates themselves, in the pattern of
{ref "combinatorics"}[Combinatorics and Order]: plain data, a pure layout in exact rational
coordinates, a builder, a decidable `Faithful` predicate that reads the diagram back and accounts
for every mark by class (shape, exact position and colour role; a mark of any other part is
refused), and a theorem that the builder satisfies it. The package `pilean-mathlib` ties the
gallery's figures to Mathlib's functions and predicates.

# Plots of Sequences
%%%
tag := "number-theory-sequences"
%%%

A {name}`PILean.Diagram.SeqPlot` has a range `lo, …, hi`, sequences `ℕ → ℚ` with their names,
and comparison curves. Point `n` of sequence `k` is a dot at `(sx n, sy (f n))` for the exact
scales of {name}`PILean.Diagram.SeqPlot.layout`; a curve is the polyline through its values at
the indices of the range. The index axis starts at a multiple of its tick step (`0` for a range
from `1`) and its ticks stand at round indices; both axes stand a tenth of a unit outside the
points, so that no point lies on an axis; the legend shows a dot for a sequence and a line for a
curve; the points' radius shrinks with their number (`dotRadiusFor`), so that neighbours never
overlap.

* {name}`PILean.Diagram.SeqPlot.draw_faithful`: the points ({name}`PILean.Diagram.Diagram.data`)
  are exactly `(k, n, point n (f n))`, sequence by sequence; the marks of points, curves and
  decorations (axes, ticks, tick labels, the legend's samples and names, the name of the index
  axis) are exactly the builder's, colours included, and nothing else is drawn.
* {name}`PILean.Diagram.SeqPlot.mem_data`: `(k, n, p)` is drawn exactly when sequence `k` is
  `f`, `lo ≤ n ≤ hi` and `p` is the point of `n` and `f n`.

```lean
/-- Euler's totient: the number of `a < n` with `gcd n a = 1`. -/
def phi (n : Nat) : Nat := ((List.range n).filter fun a => Nat.gcd n a == 1).length

/-- The totient on `1, …, 30`. -/
def phiPlot : SeqPlot := { lo := 1, hi := 30, series := [("φ(n)", fun n => phi n)] }

/-- The plot as a plane figure. -/
@[figure]
def phiFigure : Plane.Figure := phiPlot.figure.toPlane

/-- The figure is the plot's diagram, drawn faithfully, and the values are the totient's,
written out. -/
theorem phiFigure_spec :
    phiFigure = phiPlot.figure.toPlane ∧ phiPlot.Faithful phiPlot.layout phiPlot.figure ∧
    phiPlot.series.map (fun s => phiPlot.indices.map s.2) =
      [[1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4, 12, 6, 8, 8, 16, 6, 18, 8, 12, 10, 22, 8, 20, 12, 18,
        12, 28, 8]] :=
  ⟨rfl, phiPlot.builder_faithful (by decide +kernel), by decide +kernel⟩

figure_proves phiFigure phiFigure_spec
```

:::figure PILeanManual.NumberTheoryGuide.phiFigure (alt := "A dot plot of Euler's totient for n from 1 to 30: the index axis from 0 to 30 with ticks every 5, the value axis from 0 to 30; the dots of the primes lie on the line φ(n) = n − 1 and the others below it.")
:::

# Grids of Numbers
%%%
tag := "number-theory-grids"
%%%

A {name}`PILean.Diagram.CellPlot` is a list of unit cells at integer positions, each with a key,
a mark and a text, and headings. A marked cell is tinted in accent 0, or filled opaque in a plot
of `solid` cells (cells without text, drawn a little apart); an unmarked one is outlined in the
faint ink. {name}`PILean.Diagram.ulamCells` lays out `1, …, count` on the square spiral of Ulam.

* {name}`PILean.Diagram.CellPlot.draw_faithful`: the marks of cells and their texts are exactly
  the cells', cell by cell, at their positions, in the colour of their mark; the headings are the
  plot's; nothing else is drawn.
* {name}`PILean.Diagram.CellPlot.mem_marked`: every cell is drawn as its square in the colour of
  its mark.

```lean
/-- Whether `n` is prime: at least 2 and no divisor among `2, …, n - 1`. -/
def isPrime (n : Nat) : Bool := 2 ≤ n && (List.range' 2 (n - 2)).all fun d => n % d != 0

/-- The numbers `1, …, 30` in three rows of ten, the primes marked. -/
def sieve : CellPlot where
  cells := (List.range 30).map fun i =>
    { key := i + 1, pos := ((i % 10 : Nat), -((i / 10 : Nat) : Int)), marked := isPrime (i + 1),
      text := toString (i + 1) }

/-- The sieve as a plane figure. -/
@[figure]
def sieveFigure : Plane.Figure := sieve.figure.toPlane

/-- The figure is drawn faithfully, and the marked numbers are the primes below 30. -/
theorem sieveFigure_spec :
    sieveFigure = sieve.figure.toPlane ∧ sieve.Faithful sieve.figure ∧
    (sieve.cells.filter (·.marked)).map (·.key) = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29] :=
  ⟨rfl, sieve.builder_faithful (by decide +kernel), by decide +kernel⟩

figure_proves sieveFigure sieveFigure_spec
```

:::figure PILeanManual.NumberTheoryGuide.sieveFigure (alt := "The numbers 1 to 30 in three rows of ten cells; the cells of 2, 3, 5, 7, 11, 13, 17, 19, 23 and 29 are tinted.")
:::

# Lattices and Gaussian Integers
%%%
tag := "number-theory-lattices"
%%%

A {name}`PILean.Diagram.PlaneLattice` is the lattice `ℤ ω₁ + ℤ ω₂` of two rational periods with
a window and a marking of its points by their coefficients. It is drawn as a dot at each lattice
point in the window (in accent 1 where marked, otherwise in `plainInk`), the fundamental
parallelogram `0, ω₁, ω₁ + ω₂, ω₂` in accent 0 and the two axes; a point on an axis records that
it is on it. The points considered are the coefficients `|m|, |n| ≤ bound`, a bound computed from
the window and the inverse of the matrix of the periods.

* {name}`PILean.Diagram.PlaneLattice.draw_faithful`: the dots
  ({name}`PILean.Diagram.Diagram.dots`) are exactly the points in the window among the candidates,
  each in the colour of its mark; the parallelogram and the axes are the builder's; nothing else
  is drawn.
* {name}`PILean.Diagram.PlaneLattice.mem_points`: `(m, n)` is drawn exactly when
  `|m|, |n| ≤ bound` and `m ω₁ + n ω₂` is in the window. That `bound` is large enough, so that
  every lattice point of the window is drawn, needs inequalities over ℚ and is proved in
  `pilean-mathlib` (`PlaneLattice.natAbs_le_bound`), where the dots are shown to be exactly the
  points of `Submodule.span ℤ {ω₁, ω₂}` in the window, each once.

```lean
/-- Whether `a + b i` is a Gaussian prime: on an axis, `|a + b|` is a prime `≡ 3 (mod 4)`;
elsewhere `a² + b²` is prime. -/
def gaussianPrime (a b : Int) : Bool :=
  if a = 0 || b = 0 then
    let k := (a + b).natAbs
    isPrime k && k % 4 == 3
  else isPrime (a.natAbs ^ 2 + b.natAbs ^ 2)

/-- The Gaussian integers with `|a|, |b| ≤ 3`, the Gaussian primes marked. -/
def gaussian : PlaneLattice :=
  { w1 := (1, 0), w2 := (0, 1), lo := (-3, -3), hi := (3, 3), marked := gaussianPrime,
    plainInk := .faint }

/-- The lattice as a plane figure. -/
@[figure]
def gaussianFigure : Plane.Figure := gaussian.figure.toPlane

/-- The figure is drawn faithfully, and the marked points are these twenty-four. -/
theorem gaussianFigure_spec :
    gaussianFigure = gaussian.figure.toPlane ∧ gaussian.Faithful gaussian.figure ∧
    gaussian.points.filter (fun (a, b) => gaussian.marked a b) =
      [(-3, -2), (-3, 0), (-3, 2), (-2, -3), (-2, -1), (-2, 1), (-2, 3), (-1, -2), (-1, -1),
        (-1, 1), (-1, 2), (0, -3), (0, 3), (1, -2), (1, -1), (1, 1), (1, 2), (2, -3), (2, -1),
        (2, 1), (2, 3), (3, -2), (3, 0), (3, 2)] :=
  ⟨rfl, gaussian.builder_faithful (by decide +kernel), by decide +kernel⟩

figure_proves gaussianFigure gaussianFigure_spec
```

:::figure PILeanManual.NumberTheoryGuide.gaussianFigure (alt := "The Gaussian integers a + bi with |a| and |b| at most 3 as dots on a square grid with the two axes and the unit square; the Gaussian primes, such as 1 + i, 2 + i, 3 and 3i, are in colour, the others faint.")
:::

# Mathlib's Objects
%%%
tag := "number-theory-mathlib"
%%%

The figures compute with plain functions on the natural numbers and the integers; the package
`pilean-mathlib` proves those functions equal to Mathlib's for every argument and states each
figure's theorem with Mathlib's definitions. Each theorem pins the figure's names, labels and
marks (through the kind's `Faithful`), and `lake test` in `mathlib/` compiles changed copies of
the figures and requires each change to break the figure's theorem.

| Figure | Soundness and completeness (proved) | Range |
|---|---|---|
| Euler's totient | the points are exactly `(n, Nat.totient n)` | `1 ≤ n ≤ 100` |
| The number of divisors | the points are exactly `(n, σ 0 n)` | `1 ≤ n ≤ 100` |
| The prime-counting function | the points are exactly `(n, Nat.primeCounting n)`; the curve is the polyline through `(n, n / (harmonic n - 1))` | `2 ≤ n ≤ 100` |
| The Ulam spiral | the cells are `1, …, 441`, each next to the one before, no two at one place; a cell is filled exactly when its number is `Nat.Prime` | `1, …, 441` |
| Quadratic residues | for `p` in `3, 5, 7, 11, 13` and `a < p`, the cell is marked exactly when `a` is a nonzero square in `ZMod p` and shows `legendreSym p a`; there are no other cells | 39 cells |
| The Gaussian primes | the dots are exactly the `a + b i` with `|a|, |b| ≤ 7`, in colour exactly when `Prime (⟨a, b⟩ : GaussianInt)`, faint exactly when not | 225 points |
| A lattice | the dots are exactly the points of `Submodule.span ℤ {(1, 0), (1/2, 7/8)}` in the window, each once; the parallelogram is `0, ω₁, ω₁ + ω₂, ω₂` | `[-3, 3] × [-2, 2]` |

The Gaussian primes are decided in both directions: a marked point has a prime norm, or is a unit
times a rational prime `≡ 3 (mod 4)`, and is prime by Mathlib's theorems; an unmarked one is `0`,
a unit, or the product of two Gaussian integers of norm greater than one, found by a search and
checked by the kernel. Möbius sums are not drawn: Mathlib's `ArithmeticFunction.moebius` is not
practical to evaluate in the kernel and its equality with a plain function is not proved here.

# Certified Plots of Real Functions
%%%
tag := "number-theory-certified"
%%%

The core has no real numbers; `pilean-mathlib` plots a real function `f` by an exact rational
approximant and proves how near the drawing is. A `CertifiedPlot` holds the function's name, the
approximant, the interval `[lo, hi]`, the number of steps and the bound `delta`, and its figure
writes all four in its title. `CertifiedPlot.Certifies c f` says that the polyline through the
exact samples is *vertically within* `delta` of the graph of `f` over `[lo, hi]`: it lies over
the interval, has a point above every abscissa of it, and every point `(x, y)` of it has
`|y - f x| ≤ delta`. The bound is proved as the approximant's error `ε` at the grid points plus
`M h² / 8`, the error of joining samples `h` apart by segments where `|f''| ≤ M`.

| Function | Interval, steps | Approximant | Bound (pixels at the gallery size) |
|---|---|---|---|
| `exp` | `[−2, 2]`, 128 | Taylor polynomial of degree 15 | `1/1000` (0.036) |
| `cos` | `[−3, 3]`, 96 | Taylor polynomial of degree 16 | `1/2000` (0.072) |
| `log` | `[1/2, 3/2]`, 64 | 20 terms of its series at 1 | `1/8000` (0.026) |
| `arctan` | `[−3/4, 3/4]`, 48 | 20 terms of its series at 0 | `1/5000` (0.029) |
| `√` | `[1/4, 4]`, 120 | square roots to 30 binary digits | `1/4000` (0.048) |
| `sin` | `[−3, 3]`, 96 | Taylor polynomial of degree 15 | `1/2000` (0.072) |

The bound is loose where `|f''|` is smaller than its maximum over the interval. The pixels are
computed in floating point by the package's tests; the theorem is about the exact polyline, and
the step from it to the pixels is tested, not proved.

# What Is Proved and What Is Tested
%%%
tag := "number-theory-proved"
%%%

Proved: which marks are drawn, of which part, at which exact rational positions, with which
colour role; that the points of a plot are the values of its sequences on its range, that a
grid's cells and texts are its data, that a lattice's dots are the lattice points in its window;
in `pilean-mathlib`, the same for Mathlib's totient, divisor function, prime-counting function,
harmonic numbers, primality, Legendre symbol, Gaussian primes and spans. Tested: that the
pictures are good (the axes clear of the points, round ticks, the points of a plot apart; the
layout checks of plane figures in both themes, where two points of a plot may stand closer than
the markers of a geometric figure when their discs do not overlap, and a point may lie near a
comparison curve), the colours' values, floating point and the pixels.

```lean -show
end PILeanManual.NumberTheoryGuide
```
