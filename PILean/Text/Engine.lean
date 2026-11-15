/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Text.Lettering

/-!
# The text engine interface

What a plot needs of a typesetter: the width of a string, the ascent and descent, and the shape of
a string as filled outlines, as centre lines to stroke, or both. The built-in single-stroke
lettering implements it; the package `pilean-leantex` (the folder `leantex/`) implements it with
LeAnTeX, which reads its strings as LaTeX.

An engine also says who it is (`id`, which the fingerprint of a figure drawn with it covers) and
whether its strings are plain text that an SVG document may keep as `text` elements (`native`);
the text of an engine whose strings are markup is always written as shapes.

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
  /-- The engine's identity, covered by the fingerprint of every figure drawn with it (see
  `PILean.Trust.rendererWith`); empty for the built-in lettering, whose code the renderer's
  identity already covers. Another engine names its code, its version and its data (fonts) here,
  so that a change to any of them changes the fingerprint. -/
  id : String := ""
  /-- Whether a string is plain text that SVG may write as a `text` element in a font family;
  `false` for an engine whose strings are markup, whose SVG text is always shapes. -/
  native : Bool := true

namespace TextEngine

/-- The built-in single-stroke lettering as an engine. Small text is shaped a little heavier, so
that a stroke is never thinner than a pixel (an optical size for the single-stroke lettering). -/
def lettering : TextEngine where
  measure s size := Lettering.measure s size
  ascent := Lettering.ascent
  descent := Lettering.descent
  shape s size weight :=
    let (p, w) := Lettering.shape s size
      (max weight (if size > 0 then 1.05 / (0.078 * size) else weight))
    { strokes := p, strokeWidth := w }

end TextEngine

end PILean
