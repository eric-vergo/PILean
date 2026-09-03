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

/-! ## Integer upscaling

`textScaled` renders exactly what `text` renders and then magnifies it by a
whole number: every glyph pixel becomes a solid `scale × scale` block, with
no smoothing, no partial coverage, and no floating point. Nearest-neighbour
magnification of a bilevel bitmap *is* block replication, so this is the
sharp result, not an approximation to one. -/

/-- Blit one glyph's rows (MSB = leftmost pixel) into `img` with top-left
corner `(x, y)`, magnified by `scale`: the glyph pixel at cell `(col, row)`
becomes the solid `scale × scale` block whose top-left corner is
`(x + col·scale, y + row·scale)`. Clipped. `scale = 1` reduces to
`drawGlyph`. -/
private def drawGlyphScaled (img : Image) (x y : Int) (rows : ByteArray)
    (glyphWidth glyphHeight scale : Nat) (color : Color) : Image := Id.run do
  let mut img := img
  let s : Int := (scale : Int)
  for row in [0:glyphHeight] do
    let byte := (rows.get! row).toNat
    for col in [0:glyphWidth] do
      let bit := (byte >>> (glyphWidth - 1 - col)) &&& 1
      if bit != 0 then
        let gx := x + (col : Int) * s
        let gy := y + (row : Int) * s
        for j in [0:scale] do
          for i in [0:scale] do
            img := img.putPixel (gx + (i : Int)) (gy + (j : Int)) color
  return img

/-- Draw the hollow fallback box of `drawFallbackBox` magnified by `scale`
(so its border is `scale` pixels thick, being the block replication of a
1-pixel border), clipped. `scale = 1` reduces to `drawFallbackBox`. -/
private def drawFallbackBoxScaled (img : Image) (x y : Int)
    (glyphWidth glyphHeight scale : Nat) (color : Color) : Image := Id.run do
  let mut img := img
  let s : Int := (scale : Int)
  for row in [0:glyphHeight] do
    for col in [0:glyphWidth] do
      if row == 0 || row + 1 == glyphHeight || col == 0 || col + 1 == glyphWidth then
        let gx := x + (col : Int) * s
        let gy := y + (row : Int) * s
        for j in [0:scale] do
          for i in [0:scale] do
            img := img.putPixel (gx + (i : Int)) (gy + (j : Int)) color
  return img

/-- Draw `s` at `pos` (top-left of the first glyph cell) with every glyph
pixel magnified into a solid `scale × scale` block, clipped. The cursor
advances `font.glyphWidth * scale` per character and `'\n'` resets `x` to
`pos.x` and advances `y` by `font.glyphHeight * scale`, so the whole layout
scales uniformly and `textScaled img pos s color 1 font = text img pos s
color font`. `scale = 0` draws nothing. -/
def textScaled (img : Image) (pos : Point) (s : String) (color : Color) (scale : Nat)
    (font : BitmapFont := BitmapFont.default) : Image := Id.run do
  if scale == 0 then
    return img
  let mut img := img
  let mut x := pos.x
  let mut y := pos.y
  for c in s.toList do
    if c == '\n' then
      x := pos.x
      y := y + ((font.glyphHeight * scale : Nat) : Int)
    else
      img := match font.glyph? c with
        | some rows => drawGlyphScaled img x y rows font.glyphWidth font.glyphHeight scale color
        | none => drawFallbackBoxScaled img x y font.glyphWidth font.glyphHeight scale color
      x := x + ((font.glyphWidth * scale : Nat) : Int)
  return img

/-- The `(width, height)` in pixels that `textScaled` would cover for `s` at
`scale`: `textSize s font` scaled componentwise, i.e. `(w * scale, h * scale)`.
Agrees with `textSize` at `scale = 1` and measures `(0, 0)` at `scale = 0`,
where nothing is drawn. -/
def textSizeScaled (s : String) (scale : Nat) (font : BitmapFont := BitmapFont.default) :
    Nat × Nat :=
  let (w, h) := textSize s font
  (w * scale, h * scale)

end PILean.Draw
