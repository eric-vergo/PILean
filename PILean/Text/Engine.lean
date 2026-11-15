/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Text.Lettering

/-!
# The text engine interface

What a plot needs of a typesetter: the width of a string, the ascent and descent, and the shape of
a string as filled outlines, as centre lines to stroke, or both. The built-in single-stroke
lettering implements it; a richer typesetting library can implement it later.

## Main definitions

* `TextShape`: the shape of a string: outlines to fill, centre lines to stroke, the stroke width.
* `TextEngine`: the interface.
* `TextEngine.lettering`: the built-in lettering as an engine.
-/

namespace PILean

/-- The shape of a string: filled outlines and/or centre lines to stroke, with the baseline origin
at `(0, 0)` and `y` down. -/
structure TextShape where
  /-- Closed outlines to fill. -/
  fill : Path := {}
  /-- Centre lines to stroke with round caps and joins. -/
  strokes : Path := {}
  /-- The stroke width in pixels. -/
  strokeWidth : Float := 0

/-- A text engine: measures strings and shapes them. -/
structure TextEngine where
  /-- The advance width of a string at a size in pixels. -/
  measure : String → Float → Float
  /-- The ascent as a fraction of the size. -/
  ascent : Float
  /-- The descent as a fraction of the size, positive. -/
  descent : Float
  /-- A string at a size in pixels and a weight (1 is regular), its baseline origin at `(0, 0)`
  and `y` down. -/
  shape : String → Float → Float → TextShape

namespace TextEngine

/-- The built-in single-stroke lettering as an engine. -/
def lettering : TextEngine where
  measure s size := Lettering.measure s size
  ascent := Lettering.ascent
  descent := Lettering.descent
  shape s size weight :=
    let (p, w) := Lettering.shape s size weight
    { strokes := p, strokeWidth := w }

end TextEngine

end PILean
