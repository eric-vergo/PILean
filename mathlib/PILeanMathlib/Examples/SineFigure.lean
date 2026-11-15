/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Trust.Attr

/-!
# A plot of the sine with a proved error bound: the figure

The figure `sineFigure` plots the Taylor polynomial of the sine at `0` of degree 15, an exact
function on the rational numbers, on the grid of 96 steps from `-3` to `3`. Everything here is
exact and needs PILean only; this module imports nothing from Mathlib, so that the picture can be
drawn by a program that does not contain Mathlib.

The theorem about the figure, `sineFigure_spec` in `PILeanMathlib.Examples.Sine`, says that the
polyline through the exact samples is vertically within `1 / 2000` of the graph of the real sine
over `[-3, 3]`.
-/

namespace PILeanMathlib.Examples

open PILean PILean.Plot

/-- The Taylor polynomial of the sine at `0` of degree 15, on the rational numbers. -/
def sineTaylor (x : Rat) : Rat :=
  x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800
    + x ^ 13 / 6227020800 - x ^ 15 / 1307674368000

/-- The left end of the interval. -/
def lo : Rat := -3

/-- The right end of the interval. -/
def hi : Rat := 3

/-- The number of steps of the grid; the step is `1 / 16`. -/
def steps : Nat := 96

/-- The curve: a line through the 97 exact samples of `sineTaylor`. -/
def sineSeries : Series := .ofExact "Taylor polynomial of degree 15" sineTaylor lo hi steps

/-- The sine on `[-3, 3]`: the polyline through 97 exact samples of its Taylor polynomial of
degree 15, vertically within `1 / 2000` of the graph of the sine (`sineFigure_spec`). -/
@[figure]
def sineFigure : Figure where
  title := "The sine from 97 exact samples"
  panels := #[{
      x := { label := "x" }, y := { label := "y" },
      series := #[sineSeries] }]

end PILeanMathlib.Examples
