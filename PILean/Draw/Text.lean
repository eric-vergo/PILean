import PILean.Core.Image
import PILean.Font.Bitmap
import PILean.Font.Spleen8x16

/-!
# Text rendering

Bitmap-font text (WP6). Monospace grid; `\n` starts a new line at `pos.x`.
Characters the font doesn't cover render as a hollow fallback box.
TrueType rendering is a later milestone and will slot in as an alternative
font type.
-/

namespace PILean.Draw

open PILean

/-- Blit one glyph's rows (MSB = leftmost pixel) into `img` with top-left
corner `(x, y)`, clipped. -/
private def drawGlyph (img : Image) (x y : Int) (rows : ByteArray)
    (glyphWidth glyphHeight : Nat) (color : Color) : Image := Id.run do
  let mut img := img
  for row in [0:glyphHeight] do
    let byte := (rows.get! row).toNat
    for col in [0:glyphWidth] do
      let bit := (byte >>> (glyphWidth - 1 - col)) &&& 1
      if bit != 0 then
        img := img.putPixel (x + (col : Int)) (y + (row : Int)) color
  return img

/-- Draw a hollow 1-pixel-wide box filling the glyph cell (fallback for
codepoints the font doesn't cover), clipped. -/
private def drawFallbackBox (img : Image) (x y : Int) (glyphWidth glyphHeight : Nat)
    (color : Color) : Image := Id.run do
  let mut img := img
  for row in [0:glyphHeight] do
    for col in [0:glyphWidth] do
      if row == 0 || row + 1 == glyphHeight || col == 0 || col + 1 == glyphWidth then
        img := img.putPixel (x + (col : Int)) (y + (row : Int)) color
  return img

/-- Draw `s` at `pos` (top-left of the first glyph cell), clipped. Advances
one glyph cell per character (`font.glyphWidth`); `'\n'` resets the cursor's
`x` to `pos.x` and advances `y` by `font.glyphHeight`. -/
def text (img : Image) (pos : Point) (s : String) (color : Color)
    (font : BitmapFont := BitmapFont.default) : Image := Id.run do
  let mut img := img
  let mut x := pos.x
  let mut y := pos.y
  for c in s.toList do
    if c == '\n' then
      x := pos.x
      y := y + (font.glyphHeight : Int)
    else
      img := match font.glyph? c with
        | some rows => drawGlyph img x y rows font.glyphWidth font.glyphHeight color
        | none => drawFallbackBox img x y font.glyphWidth font.glyphHeight color
      x := x + (font.glyphWidth : Int)
  return img

/-- The `(width, height)` in pixels that `text` would cover for `s`: the
longest line's character count times `font.glyphWidth`, by the number of
lines times `font.glyphHeight`. The empty string measures `(0, 0)`. -/
def textSize (s : String) (font : BitmapFont := BitmapFont.default) : Nat × Nat :=
  if s.isEmpty then (0, 0)
  else
    let lines := s.splitOn "\n"
    let maxLen := lines.foldl (fun acc l => max acc l.length) 0
    (maxLen * font.glyphWidth, lines.length * font.glyphHeight)

end PILean.Draw
