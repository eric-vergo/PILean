import PILean.Core.Image
import PILean.Binary.Writer

/-!
# Basic transforms

Lossless orientation transforms (WP7): flips, quarter-turn rotations, and
transposition. All are pure pixel-shuffles — output size is the input size
with width/height swapped where appropriate.

Every operation is a bpp-aware byte remap into a single freshly-allocated,
correctly-sized output buffer (`ByteArray.replicateByte`), filled with
`ByteArray.copySlice` (whole rows where contiguous, one pixel — `bpp`
bytes — at a time otherwise). `.palette`-mode images keep their palette
unchanged; only the indices are shuffled, exactly like any other
single-byte-per-pixel mode.

`rotate90`/`rotate270`/`transpose` swap `width` and `height`; the direction
conventions (`rotate90` is PIL's `ROTATE_90`, i.e. counter-clockwise) were
verified against Pillow 11.3.0 directly (`img.transpose(Image.ROTATE_90)`
etc.) rather than assumed, since the y-axis-down convention makes
"counter-clockwise" easy to get backwards by construction alone.
-/

namespace PILean.Image

/-- Mirror horizontally (left↔right): `out(x, y) = in(w-1-x, y)`. -/
def flipH (img : Image) : Image :=
  let w := img.width
  let bpp := img.mode.bytesPerPixel
  img.modifyData fun data => Id.run do
    let mut out := ByteArray.replicateByte data.size 0
    for y in [0:img.height] do
      let rowOff := y * w * bpp
      for x in [0:w] do
        let srcOff := rowOff + x * bpp
        let dstOff := rowOff + (w - 1 - x) * bpp
        out := data.copySlice srcOff out dstOff bpp
    return out

/-- Mirror vertically (top↔bottom): `out(x, y) = in(x, h-1-y)`. Whole rows
are contiguous under this remap, so each row is copied with a single
`copySlice`. -/
def flipV (img : Image) : Image :=
  let w := img.width
  let h := img.height
  let bpp := img.mode.bytesPerPixel
  let rowBytes := w * bpp
  img.modifyData fun data => Id.run do
    let mut out := ByteArray.replicateByte data.size 0
    for y in [0:h] do
      let srcOff := y * rowBytes
      let dstOff := (h - 1 - y) * rowBytes
      out := data.copySlice srcOff out dstOff rowBytes
    return out

/-- Rotate 90° counter-clockwise (PIL's `ROTATE_90`): the output is
`height × width`, with `out(y, w-1-x) = in(x, y)`. -/
def rotate90 (img : Image) : Image :=
  let w := img.width
  let h := img.height
  let bpp := img.mode.bytesPerPixel
  let img' := img.modifyData fun data => Id.run do
    let mut out := ByteArray.replicateByte data.size 0
    for y in [0:h] do
      let srcRowOff := y * w * bpp
      for x in [0:w] do
        let srcOff := srcRowOff + x * bpp
        let dstOff := ((w - 1 - x) * h + y) * bpp
        out := data.copySlice srcOff out dstOff bpp
    return out
  { img' with width := h, height := w }

/-- Rotate 180°: `out(x, y) = in(w-1-x, h-1-y)`. -/
def rotate180 (img : Image) : Image :=
  let w := img.width
  let h := img.height
  let bpp := img.mode.bytesPerPixel
  img.modifyData fun data => Id.run do
    let mut out := ByteArray.replicateByte data.size 0
    for y in [0:h] do
      let srcRowOff := y * w * bpp
      let dstRowOff := (h - 1 - y) * w * bpp
      for x in [0:w] do
        let srcOff := srcRowOff + x * bpp
        let dstOff := dstRowOff + (w - 1 - x) * bpp
        out := data.copySlice srcOff out dstOff bpp
    return out

/-- Rotate 270° counter-clockwise (PIL's `ROTATE_270`, i.e. 90° clockwise):
the output is `height × width`, with `out(h-1-x, y) = in(y, x)`. -/
def rotate270 (img : Image) : Image :=
  let w := img.width
  let h := img.height
  let bpp := img.mode.bytesPerPixel
  let img' := img.modifyData fun data => Id.run do
    let mut out := ByteArray.replicateByte data.size 0
    for y in [0:h] do
      let srcRowOff := y * w * bpp
      for x in [0:w] do
        let srcOff := srcRowOff + x * bpp
        let dstOff := (x * h + (h - 1 - y)) * bpp
        out := data.copySlice srcOff out dstOff bpp
    return out
  { img' with width := h, height := w }

/-- Transpose across the main diagonal (swap x and y): the output is
`height × width`, with `out(y, x) = in(x, y)`. -/
def transpose (img : Image) : Image :=
  let w := img.width
  let h := img.height
  let bpp := img.mode.bytesPerPixel
  let img' := img.modifyData fun data => Id.run do
    let mut out := ByteArray.replicateByte data.size 0
    for y in [0:h] do
      let srcRowOff := y * w * bpp
      for x in [0:w] do
        let srcOff := srcRowOff + x * bpp
        let dstOff := (x * h + y) * bpp
        out := data.copySlice srcOff out dstOff bpp
    return out
  { img' with width := h, height := w }

end PILean.Image
