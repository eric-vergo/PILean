/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanMathlib.Examples.SineFigure

/-!
# The files of the gallery

The pictures of `sineFigure`, light and dark, as SVG and PNG. This module and the programs built
from it import nothing from Mathlib.
-/

namespace PILeanMathlibTest

open PILean PILean.Plot PILeanMathlib.Examples

/-- The figures of the gallery: file stem and figure. -/
def figures : Array (String × Figure) :=
  #[("sine-proved", sineFigure), ("sine-proved-dark", { sineFigure with style := Style.dark })]

/-- Every file of the gallery: name and bytes, in a fixed order. -/
def files : Array (String × Except String ByteArray) := Id.run do
  let mut out := #[]
  for (n, f) in figures do
    out := out.push (n ++ ".svg", .ok f.toSvg.toUTF8)
    out := out.push (n ++ ".png", match f.toPng with
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
