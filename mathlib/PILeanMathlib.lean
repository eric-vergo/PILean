/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanMathlib.Axioms
import PILeanMathlib.ExactPlot
import PILeanMathlib.Examples.Sine
import PILeanMathlib.Examples.SineFigure
import PILeanMathlib.Interpolation
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
* `PILeanMathlib.Axioms`: the axioms every theorem depends on, checked by the build.
-/
