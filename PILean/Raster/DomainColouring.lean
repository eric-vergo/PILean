/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Geometry
import PILean.Color
import PILean.Image.Basic
import PILean.Png

/-!
# Domain colouring

A `DomainColouring` paints a complex function over a rectangle of the plane: every pixel is
coloured by the argument of `f` at the point it stands for (its hue, OKLCH at a fixed lightness
and chroma, so that equal steps of argument are equal steps of hue) and darkened in bands by the
fractional part of `log₂ |f|`, so that the level curves `|f| = 2ᵏ` show as edges; zeros are where
every hue meets with the bands crowding in, poles where they meet with the bands crowding out.

**Standing: an illustration.** The function is a `Float` function, evaluated at the pixels' centres
in floating point; nothing about the picture is proved (no theorem ties a colour to a value), and
a figure of this kind is marked `@[figure illustration]`, so that its files, the manifest,
`pilean-info` and the Verso pages say so. The proved picture of the same function's zeros and
poles is `Diagram.RationalPlot`. The picture is a raster image only: its outputs are a PNG and a
PDF that embeds it (no SVG, which would have to embed a raster image or a rectangle per pixel).

## Main definitions

* `DomainColouring`, `DomainColouring.colour`, `DomainColouring.toImage`,
  `DomainColouring.maxPixels`.
-/

namespace PILean

/-- A complex function to paint over a window, and the size of the picture. -/
structure DomainColouring where
  /-- The function as the picture's name writes it. -/
  name : String
  /-- The function: the real and imaginary parts of `f (x + i y)` at `(x, y)`. -/
  f : Float → Float → Float × Float
  /-- The lower left corner of the window. -/
  lo : Point := ⟨-2, -2⟩
  /-- The upper right corner of the window. -/
  hi : Point := ⟨2, 2⟩
  /-- The width in pixels. -/
  width : Nat := 480
  /-- The height in pixels. -/
  height : Nat := 360

namespace DomainColouring

/-- The most pixels a picture may have (2048 × 2048). -/
def maxPixels : Nat := 2048 * 2048

/-- The colour of the value `w = (u, v)`: hue from its argument (red for positive reals), the
lightness lowered towards each next power of two of `|w|`; white for a value that is not finite
(a pole hit exactly) and black for `0`. -/
def colour (w : Float × Float) : Rgba :=
  let (u, v) := w
  let m := (u * u + v * v).sqrt
  if m.isNaN || m.isInf then ⟨255, 255, 255, 255⟩
  else if m == 0 then ⟨0, 0, 0, 255⟩
  else
    let hue := (Float.atan2 v u) * 180 / 3.141592653589793
    let hue := if hue < 0 then hue + 360 else hue
    let k := Float.log2 m
    let band := k - k.floor
    Rgba.ofOkLch { l := 0.52 + 0.3 * band, c := 0.13, h := hue }

/-- The picture: an RGB image of `width × height` pixels, pixel `(i, j)` coloured by `f` at the
point of the window its centre stands for (`y` up); `none` for a picture of no pixels or of more
than `maxPixels`. -/
def toImage (d : DomainColouring) : Option Image := Id.run do
  if d.width == 0 || d.height == 0 || d.width * d.height > maxPixels then return none
  let w := d.width.toFloat
  let h := d.height.toFloat
  let mut data := ByteArray.emptyWithCapacity (d.width * d.height * 3)
  for j in [0:d.height] do
    let y := d.hi.y - (j.toFloat + 0.5) / h * (d.hi.y - d.lo.y)
    for i in [0:d.width] do
      let x := d.lo.x + (i.toFloat + 0.5) / w * (d.hi.x - d.lo.x)
      let c := colour (d.f x y)
      data := ((data.push c.r).push c.g).push c.b
  return some { mode := .rgb, width := d.width, height := d.height, data }

end DomainColouring

end PILean
