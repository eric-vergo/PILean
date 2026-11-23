/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanMathlib.Examples.SineFigure
import PILeanMathlib.Examples.CombinatoricsFigures
import PILeanMathlib.Examples.AlgebraFigures
import PILeanMathlib.Examples.NumberTheoryFigures

/-!
# The files of the gallery

The pictures of `sineFigure`, of the combinatorial figures
(`PILeanMathlib.Examples.CombinatoricsFigures`) and of the figures of algebra
(`PILeanMathlib.Examples.AlgebraFigures`) and of number theory
(`PILeanMathlib.Examples.NumberTheoryFigures`), light and dark, as SVG and PNG. This module and
the programs built from it import nothing from Mathlib.
-/

namespace PILeanMathlibTest

open PILean PILean.Plot PILeanMathlib.Examples

/-- The figures of the gallery: file stem and figure. -/
def figures : Array (String × Figure) :=
  #[("sine-proved", sineFigure), ("sine-proved-dark", { sineFigure with style := Style.dark })]

/-- The diagrams of the gallery: file stem and diagram. -/
def diagrams : Array (String × PILean.Diagram.Diagram) :=
  PILeanMathlib.Examples.figures ++ algebraFigures ++ numberTheoryFigures

/-- Every file of the gallery: name and bytes, in a fixed order. -/
def files : Array (String × Except String ByteArray) := Id.run do
  let mut out := #[]
  for (n, f) in figures do
    out := out.push (n ++ ".svg", .ok f.toSvg.toUTF8)
    out := out.push (n ++ ".png", match f.toPng with
      | some b => .ok b
      | none => .error "no pixels")
  for (n, d) in diagrams do
    for (suffix, fig) in [("", d.toPlane), ("-dark", d.dark.toPlane)] do
      out := out.push (n ++ suffix ++ ".svg", .ok fig.toSvg.toUTF8)
      out := out.push (n ++ suffix ++ ".png", match fig.toPng with
        | some b => .ok b
        | none => .error "no pixels")
  return out

/-- The number of pixels of the first panel of `sineFigure` that one unit of the ordinate
covers. -/
def pixelsPerUnit : Float :=
  match sineFigure.layout[0]? with
  | some l =>
    match l.pos ⟨0, 0⟩, l.pos ⟨0, 1⟩ with
    | some p, some q => (p.y - q.y).abs
    | _, _ => 0
  | none => 0

end PILeanMathlibTest
