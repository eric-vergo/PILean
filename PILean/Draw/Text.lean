import PILean.Core.Image
import PILean.Font.Bitmap

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# Text rendering

Bitmap-font text (WP6). Monospace grid; `\n` starts a new line at `pos.x`.
Characters the font doesn't cover render as a hollow fallback box.
TrueType rendering is a later milestone and will slot in as an alternative
font type.
-/

namespace PILean.Draw

open PILean

/-- Draw `s` at `pos` (top-left of the first glyph cell), clipped. -/
def text (img : Image) (pos : Point) (s : String) (color : Color)
    (font : BitmapFont := BitmapFont.default) : Image :=
  panic! "PILean.Draw.text: not implemented yet (WP6)"

/-- The `(width, height)` in pixels that `text` would cover for `s`. -/
def textSize (s : String) (font : BitmapFont := BitmapFont.default) : Nat × Nat :=
  panic! "PILean.Draw.textSize: not implemented yet (WP6)"

end PILean.Draw
