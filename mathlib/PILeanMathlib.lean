/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanMathlib.Axioms
import PILeanMathlib.Category
import PILeanMathlib.CertifiedPlot
import PILeanMathlib.CertifiedPlotBound
import PILeanMathlib.Examples.Real
import PILeanMathlib.Examples.RealFigures
import PILeanMathlib.Group
import PILeanMathlib.Examples.Algebra
import PILeanMathlib.Examples.AlgebraFigures
import PILeanMathlib.Combinatorics
import PILeanMathlib.Examples.Combinatorics
import PILeanMathlib.Examples.CombinatoricsFigures
import PILeanMathlib.ExactPlot
import PILeanMathlib.Examples.Sine
import PILeanMathlib.Examples.SineFigure
import PILeanMathlib.Interpolation
import PILeanMathlib.Lattice
import PILeanMathlib.NumberTheory
import PILeanMathlib.Examples.NumberTheory
import PILeanMathlib.Examples.NumberTheoryFigures
import PILeanMathlib.Polyline

/-!
# PILean's plots against the real numbers

* `PILeanMathlib.Polyline`: a polyline as a subset of the real plane, and what it means for it to
  be vertically within `δ` of the graph of a function.
* `PILeanMathlib.Interpolation`: the error of linear interpolation.
* `PILeanMathlib.ExactPlot`: the plot of an exact function is near the graph of the real function
  it approximates.
* `PILeanMathlib.Examples.SineFigure`, `PILeanMathlib.Examples.Sine`: a figure of the sine and the
  theorem about it.
* `PILeanMathlib.CertifiedPlot`, `PILeanMathlib.CertifiedPlotBound`: certified plots of real
  functions as a kind (an exact approximant, an interval, a number of steps and a bound) and how
  to prove the bound (Taylor's theorem, the arctangent's series, checked squares).
* `PILeanMathlib.Examples.RealFigures`, `PILeanMathlib.Examples.Real`: the exponential, the cosine,
  the logarithm, the arctangent and the square root, each with its bound proved.
* `PILeanMathlib.Combinatorics`: Mathlib's simple graphs, digraphs, partial orders, Young
  diagrams, semistandard tableaux, permutations, Dyck words and finsets bound to PILean's
  combinatorial diagrams, with theorems that the drawn parts are those objects.
* `PILeanMathlib.Examples.CombinatoricsFigures`, `PILeanMathlib.Examples.Combinatorics`: a figure
  for each and the theorem about it.
* `PILeanMathlib.Category`: commutative diagrams realised in a category: composites of paths,
  commutation, the marks of the arrows' styles (`Mono`, `Epi`, `IsIso`); a `CommSq`, a
  commutative triangle and a short exact sequence drawn.
* `PILeanMathlib.Group`: Cayley tables and graphs of a group, its centre and commutativity, and
  Hasse diagrams of a partial order through an enumeration (lattices of subgroups).
* `PILeanMathlib.Examples.AlgebraFigures`, `PILeanMathlib.Examples.Algebra`: the dihedral group of
  order 8 (table, Cayley graph, subgroups), a commutative square of types and a short exact
  sequence, with their theorems.
* `PILeanMathlib.Lattice`: a figure of a lattice draws exactly the points of
  `Submodule.span ℤ {ω₁, ω₂}` in its window, each once.
* `PILeanMathlib.NumberTheory`: plots of sequences, grids of numbers and lattices bound to
  Mathlib (a plot's points as the values of a function, counting as `Finset` counting, squares
  in `ZMod p`, primes of `GaussianInt` decided in both directions).
* `PILeanMathlib.Examples.NumberTheoryFigures`, `PILeanMathlib.Examples.NumberTheory`: the totient,
  the number of divisors, the prime-counting function, the Ulam spiral, quadratic residues and
  the Gaussian primes, with their theorems.
* `PILeanMathlib.Axioms`: the axioms every theorem depends on, checked by the build.
-/
