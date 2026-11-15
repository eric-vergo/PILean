/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Path

/-!
# Text engines (placeholder, replaced by the lettering branch)
-/

namespace PILean

/-- A shaped string. -/
structure TextShape where
  /-- Filled outlines. -/
  fill : Path := {}
  /-- Centre lines. -/
  strokes : Path := {}
  /-- Stroke width. -/
  strokeWidth : Float := 0

/-- A text engine. -/
structure TextEngine where
  /-- Advance width. -/
  measure : String → Float → Float
  /-- Ascent. -/
  ascent : Float
  /-- Descent. -/
  descent : Float
  /-- Shape. -/
  shape : String → Float → Float → TextShape

/-- A crude engine. -/
def TextEngine.lettering : TextEngine where
  measure s size := 0.55 * size * s.length.toFloat
  ascent := 0.74
  descent := 0.2
  shape _ _ _ := {}

end PILean
