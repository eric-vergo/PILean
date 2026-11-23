/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean

/-!
# Certified plots of real functions: the kind

A `CertifiedPlot` plots a real function by an exact rational approximant: the polyline through
the exact samples of `approx` on the grid of `steps` steps from `lo` to `hi`, with a stated bound
`delta`. The figure writes the function's name, the interval, the number of samples and the
bound in its title, and the curve's name in its legend. This module needs PILean only, so that a
figure of the kind is drawn by a program without Mathlib; `PILeanMathlib.CertifiedPlotBound`
says over ℝ what the bound means (`CertifiedPlot.Certifies`: the polyline is vertically within
`delta` of the graph of the function over `[lo, hi]`) and how to prove it.

## Main definitions

* `CertifiedPlot`, `CertifiedPlot.series`, `CertifiedPlot.title`, `CertifiedPlot.figure`,
  `CertifiedPlot.ratText`.
* `polySum`: `∑ k < n, c k * x ^ k` on the rational numbers, the shape of the approximants.
-/

namespace PILeanMathlib

open PILean PILean.Plot

/-- A real function plotted by an exact approximant with a bound on the distance. -/
structure CertifiedPlot where
  /-- The function as the figure names it, `exp x` say. -/
  name : String
  /-- What the curve is, as the legend names it (a Taylor polynomial, say). -/
  curve : String
  /-- The exact function drawn. -/
  approx : Rat → Rat
  /-- The left end of the interval. -/
  lo : Rat
  /-- The right end of the interval. -/
  hi : Rat
  /-- The number of steps of the grid. -/
  steps : Nat
  /-- The bound on the vertical distance from the drawn polyline to the graph. -/
  delta : Rat

namespace CertifiedPlot

/-- The curve: the line through the exact samples of the approximant. -/
def series (c : CertifiedPlot) : Series := .ofExact c.curve c.approx c.lo c.hi c.steps

/-- A rational number as a title writes it: `p/q`, with the minus sign `−`. -/
def ratText (q : Rat) : String := if q < 0 then "−" ++ toString (-q) else toString q

/-- The title: the function, the interval, the number of samples and the bound. -/
def title (c : CertifiedPlot) : String :=
  s!"{c.name} on [{ratText c.lo}, {ratText c.hi}] from {c.steps + 1} exact samples, within \
    {ratText c.delta} of the graph"

/-- The figure: one panel with the curve, the axes named `x` and `y`. -/
def figure (c : CertifiedPlot) : Figure where
  title := c.title
  panels := #[{ x := { label := "x" }, y := { label := "y" }, series := #[c.series] }]

end CertifiedPlot

/-- `∑ k < n, c k * x ^ k`, by recursion on `n`. -/
def polySum (c : Nat → Rat) : Nat → Rat → Rat
  | 0, _ => 0
  | n + 1, x => polySum c n x + c n * x ^ n

/-- `n!` as a rational number. -/
def factQ : Nat → Rat
  | 0 => 1
  | n + 1 => (n + 1) * factQ n

end PILeanMathlib
