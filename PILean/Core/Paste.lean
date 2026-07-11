import PILean.Core.Image
import PILean.Core.Convert

/-!
# Crop, paste, and compositing

Region extraction and image-onto-image copying. All operations clip
silently; `crop` regions outside the source are filled with zero bytes
(PIL semantics). `paste` and `alphaComposite` clip the source rectangle
against the destination and copy/blend only the overlapping span, row by
row.
-/

namespace PILean.Image

/-- A fresh all-zero buffer of `n` bytes. Local to this file so `crop`
doesn't need to pull in the `Binary` layer for `ByteArray.replicateByte`. -/
private def zeroBytes (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    b := b.push 0
  return b

/-- Extract rectangle `r`. Regions of `r` outside the image are filled with
zero bytes (PIL crop semantics). The result is `r.width × r.height` in the
source's mode (and keeps the source's palette, if any). -/
def crop (img : Image) (r : Rect) : Image :=
  let bpp := img.mode.bytesPerPixel
  let w := r.width
  let h := r.height
  let data := Id.run do
    let mut d := zeroBytes (w * h * bpp)
    let colLo := max r.left 0
    let colHi := min r.right (img.width : Int)
    let rowLo := max r.top 0
    let rowHi := min r.bottom (img.height : Int)
    if colLo < colHi && rowLo < rowHi then
      let colStart := (colLo - r.left).toNat
      let colCount := (colHi - colLo).toNat
      let rowStart := (rowLo - r.top).toNat
      let rowCount := (rowHi - rowLo).toNat
      let srcCol := colLo.toNat
      let srcRow0 := rowLo.toNat
      for i in [0:rowCount] do
        let srcOff := ((srcRow0 + i) * img.width + srcCol) * bpp
        let dstOff := ((rowStart + i) * w + colStart) * bpp
        d := ByteArray.copySlice img.data srcOff d dstOff (colCount * bpp)
    return d
  { img with width := w, height := h, data }

/-- Copy `src` onto `dst` with `src`'s top-left at `pos`, clipped to `dst`.
Plain copy, no blending; `src` is converted to `dst`'s mode first. -/
def paste (dst : Image) (src : Image) (pos : Point) : Image :=
  let src' := src.convert dst.mode
  let bpp := dst.mode.bytesPerPixel
  let dstWidth := dst.width
  let srcWidth := src'.width
  let srcData := src'.data
  let colLo := max pos.x 0
  let colHi := min (pos.x + (srcWidth : Int)) (dst.width : Int)
  let rowLo := max pos.y 0
  let rowHi := min (pos.y + (src'.height : Int)) (dst.height : Int)
  if colLo ≥ colHi || rowLo ≥ rowHi then dst
  else
    let colCount := (colHi - colLo).toNat
    let rowCount := (rowHi - rowLo).toNat
    let srcColStart := (colLo - pos.x).toNat
    let srcRowStart := (rowLo - pos.y).toNat
    let dstColStart := colLo.toNat
    let dstRowStart := rowLo.toNat
    dst.modifyData fun data => Id.run do
      let mut d := data
      for i in [0:rowCount] do
        let srcOff := ((srcRowStart + i) * srcWidth + srcColStart) * bpp
        let dstOff := ((dstRowStart + i) * dstWidth + dstColStart) * bpp
        d := ByteArray.copySlice srcData srcOff d dstOff (colCount * bpp)
      return d

/-- Like `paste` but alpha-composites using `src`'s alpha (`Color.over`),
via a direct two-buffer loop (no intermediate `Color` array, no per-pixel
`getPixel!`/`putPixel`). -/
def alphaComposite (dst : Image) (src : Image) (pos : Point) : Image :=
  let src' := src.convert dst.mode
  let dstMode := dst.mode
  let dstPalette? := dst.palette?
  let bpp := dstMode.bytesPerPixel
  let dstWidth := dst.width
  let srcWidth := src'.width
  let srcData := src'.data
  let srcPalette? := src'.palette?
  let colLo := max pos.x 0
  let colHi := min (pos.x + (srcWidth : Int)) (dst.width : Int)
  let rowLo := max pos.y 0
  let rowHi := min (pos.y + (src'.height : Int)) (dst.height : Int)
  if colLo ≥ colHi || rowLo ≥ rowHi then dst
  else
    let colCount := (colHi - colLo).toNat
    let rowCount := (rowHi - rowLo).toNat
    let srcColStart := (colLo - pos.x).toNat
    let srcRowStart := (rowLo - pos.y).toNat
    let dstColStart := colLo.toNat
    let dstRowStart := rowLo.toNat
    dst.modifyData fun data => Id.run do
      let mut d := data
      for i in [0:rowCount] do
        for j in [0:colCount] do
          let srcOff := ((srcRowStart + i) * srcWidth + (srcColStart + j)) * bpp
          let dstOff := ((dstRowStart + i) * dstWidth + (dstColStart + j)) * bpp
          let sc := rawColorAt dstMode srcPalette? srcData srcOff
          let dc := rawColorAt dstMode dstPalette? d dstOff
          let px := rawPixelBytes dstMode dstPalette? (Color.over sc dc)
          for k in [0:bpp] do
            d := d.set! (dstOff + k) px[k]!
      return d

end PILean.Image
