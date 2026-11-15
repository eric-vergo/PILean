/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Color
import PILean.Png

/-!
# Images

An image in the spirit of Pillow's `Image`: a mode, a size and its pixels, 8 bits per channel,
row by row from the top left. Modes are `L` (grey), `RGB` and `RGBA` (straight, not
premultiplied, alpha, as in Pillow). Images are values: every operation returns a new image.

## Main definitions

* `Image`, `Image.new`, `Image.getpixel`, `Image.putpixel`.
* `Image.ofRaw`, `Image.toRaw`, `Image.writePng`, `Image.readPng`.

## Implementation notes

The samples are a `ByteArray` of `width * height * channels` bytes; `Image.WellFormed` says so,
and every operation keeps it. An operation given a malformed image treats missing samples as 0.
-/

namespace PILean

/-- The pixel layouts: one grey channel, three colour channels, or colour with alpha. -/
abbrev Mode := Png.Mode

/-- An image: its mode, its size in pixels and its samples, row by row, left to right, the
channels of a pixel together. -/
structure Image where
  /-- The mode. -/
  mode : Mode
  /-- Width in pixels. -/
  width : Nat
  /-- Height in pixels. -/
  height : Nat
  /-- The samples. -/
  data : ByteArray

namespace Image

/-- Whether the samples are as many as the size and mode ask for. -/
def WellFormed (im : Image) : Prop := im.data.size = im.width * im.height * im.mode.channels

/-- The samples of one colour in a mode: grey by ITU-R BT.601 luma (Pillow's `L` conversion,
`(299 R + 587 G + 114 B) / 1000`), RGB without alpha, RGBA. -/
def samplesOf (mode : Mode) (c : Rgba) : Array UInt8 :=
  match mode with
  | .l => #[((c.r.toNat * 299 + c.g.toNat * 587 + c.b.toNat * 114 + 500) / 1000).toUInt8]
  | .rgb => #[c.r, c.g, c.b]
  | .rgba => #[c.r, c.g, c.b, c.a]

/-- A new image filled with one colour (Pillow's `Image.new`). -/
def new (mode : Mode) (width height : Nat) (fill : Rgba := ⟨0, 0, 0, 255⟩) : Image := Id.run do
  let px := samplesOf mode fill
  let mut data := ByteArray.emptyWithCapacity (width * height * mode.channels)
  for _ in [0:width * height] do
    for b in px do data := data.push b
  return { mode, width, height, data }

/-- The colour at `(x, y)` (Pillow's `getpixel`), opaque black outside the image; a grey pixel
reads as that grey, an RGB pixel as opaque. -/
def getpixel (im : Image) (x y : Nat) : Rgba :=
  if x < im.width && y < im.height then
    let n := im.mode.channels
    let i := (y * im.width + x) * n
    let at_ := fun (k : Nat) => if h : i + k < im.data.size then im.data[i + k] else 0
    match im.mode with
    | .l => ⟨at_ 0, at_ 0, at_ 0, 255⟩
    | .rgb => ⟨at_ 0, at_ 1, at_ 2, 255⟩
    | .rgba => ⟨at_ 0, at_ 1, at_ 2, at_ 3⟩
  else ⟨0, 0, 0, 255⟩

/-- The image with the colour at `(x, y)` replaced (Pillow's `putpixel`), unchanged outside the
image. -/
def putpixel (im : Image) (x y : Nat) (c : Rgba) : Image := Id.run do
  if !(x < im.width && y < im.height) then return im
  let n := im.mode.channels
  let i := (y * im.width + x) * n
  let px := samplesOf im.mode c
  let mut data := im.data
  for k in [0:n] do
    if i + k < data.size then data := data.set! (i + k) (px[k]?.getD 0)
  return { im with data }

/-- The image as the PNG codec's raw image. -/
def toRaw (im : Image) : Png.RawImage :=
  { width := im.width, height := im.height, mode := im.mode, data := im.data }

/-- An image from the PNG codec's raw image. -/
def ofRaw (r : Png.RawImage) : Image :=
  { mode := r.mode, width := r.width, height := r.height, data := r.data }

/-- The image as PNG bytes (deterministic), with the given metadata. -/
def writePng (im : Image) (md : Png.Metadata := {}) : Except Png.PngError ByteArray :=
  Png.encode im.toRaw md

/-- An image read from PNG bytes, under the reader's caps. -/
def readPng (bytes : ByteArray) (lim : Png.Limits := {}) : Except Png.PngError Image :=
  (fun d => ofRaw d.image) <$> Png.decode bytes lim

end Image

end PILean
