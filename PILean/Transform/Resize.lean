import PILean.Core.Image
import PILean.Binary.Writer

/-!
# Resizing

`Image.resize` with selectable resampling. WP7 implements `nearest` and
`bilinear`; WP20 adds `bicubic` and `lanczos` (until then they fall back
to `bilinear` — documented, not silent: the docstring states the v1
behavior).
-/

namespace PILean

/-- Resampling filter for `Image.resize`. -/
inductive Resample where
  | nearest
  | bilinear
  | bicubic
  | lanczos
  deriving Repr, DecidableEq, Inhabited

namespace Image

/-- `Nat → Float`, exact for every value that arises from image dimensions
or byte offsets (well within `Float`'s 53-bit exact-integer range). -/
private def n2f (n : Nat) : Float := (UInt64.ofNat n).toFloat

/-- Round `v` to the nearest `UInt8`, clamping to `[0, 255]`. Negatives are
guarded away *before* the `Nat` conversion, per project convention. -/
private def clampByte (v : Float) : UInt8 :=
  let r := v.round
  if r ≤ 0.0 then 0
  else if r ≥ 255.0 then 255
  else UInt8.ofNat r.toUInt64.toNat

/-- Clamp an already-integral `Float` (a `floor` or `floor + 1` result) into
a valid `[0, maxIdx]` index. -/
private def clampIndex (maxIdx : Nat) (f : Float) : Nat :=
  if f ≤ 0.0 then 0
  else if f ≥ n2f maxIdx then maxIdx
  else f.toUInt64.toNat

/-- Nearest-neighbor resample of a `srcW × srcH` buffer (in `mode`, `bpp`
bytes per pixel) to `dstW × dstH`. Pixel centers map via
`src = floor((dst + 0.5) * srcSize / dstSize)`, clamped to the source
extent; this is a pure index remap, so it works unchanged for every mode
including `.palette` (indices are relocated, not reinterpreted).
Precondition: `srcW, srcH, dstW, dstH > 0` (the empty/identity cases are
handled by `resize` itself). -/
private def resizeNearestData (mode : Mode) (srcW srcH dstW dstH : Nat) (src : ByteArray) :
    ByteArray :=
  let bpp := mode.bytesPerPixel
  if srcW == 0 || srcH == 0 then ByteArray.replicateByte (dstW * dstH * bpp) 0
  else
    let scaleX := n2f srcW / n2f dstW
    let scaleY := n2f srcH / n2f dstH
    Id.run do
      let mut out := ByteArray.replicateByte (dstW * dstH * bpp) 0
      for dy in [0:dstH] do
        let sy := clampIndex (srcH - 1) (((n2f dy + 0.5) * scaleY).floor)
        let srcRowOff := sy * srcW * bpp
        let dstRowOff := dy * dstW * bpp
        for dx in [0:dstW] do
          let sx := clampIndex (srcW - 1) (((n2f dx + 0.5) * scaleX).floor)
          out := src.copySlice (srcRowOff + sx * bpp) out (dstRowOff + dx * bpp) bpp
      return out

/-- Bilinear resample of a `srcW × srcH` buffer to `dstW × dstH`, treating
every byte of a pixel as an independent channel — correct for `gray`,
`grayAlpha`, `rgb`, and `rgba` alike (alpha is interpolated exactly like
color channels). Pixel centers map via
`src = (dst + 0.5) * srcSize / dstSize - 0.5`; the sample is a weighted
blend of the 4 surrounding source pixels, with each corner index clamped
independently to the source extent (the blend weight itself is computed
from the *unclamped* coordinate, matching Pillow's edge behavior).
Precondition: `srcW, srcH, dstW, dstH > 0`; not valid for `.palette`
(`resize` routes `.palette` to `resizeNearestData` instead). -/
private def resizeBilinearData (mode : Mode) (srcW srcH dstW dstH : Nat) (src : ByteArray) :
    ByteArray :=
  let bpp := mode.bytesPerPixel
  if srcW == 0 || srcH == 0 then ByteArray.replicateByte (dstW * dstH * bpp) 0
  else
    let scaleX := n2f srcW / n2f dstW
    let scaleY := n2f srcH / n2f dstH
    Id.run do
      let mut out := ByteArray.emptyWithCapacity (dstW * dstH * bpp)
      for dy in [0:dstH] do
        let syF := (n2f dy + 0.5) * scaleY - 0.5
        let fy0 := syF.floor
        let fy := syF - fy0
        let y0 := clampIndex (srcH - 1) fy0
        let y1 := clampIndex (srcH - 1) (fy0 + 1.0)
        for dx in [0:dstW] do
          let sxF := (n2f dx + 0.5) * scaleX - 0.5
          let fx0 := sxF.floor
          let fx := sxF - fx0
          let x0 := clampIndex (srcW - 1) fx0
          let x1 := clampIndex (srcW - 1) (fx0 + 1.0)
          let off00 := (y0 * srcW + x0) * bpp
          let off10 := (y0 * srcW + x1) * bpp
          let off01 := (y1 * srcW + x0) * bpp
          let off11 := (y1 * srcW + x1) * bpp
          for c in [0:bpp] do
            let v00 := (src.get! (off00 + c)).toFloat
            let v10 := (src.get! (off10 + c)).toFloat
            let v01 := (src.get! (off01 + c)).toFloat
            let v11 := (src.get! (off11 + c)).toFloat
            let top := v00 * (1.0 - fx) + v10 * fx
            let bot := v01 * (1.0 - fx) + v11 * fx
            out := out.push (clampByte (top * (1.0 - fy) + bot * fy))
      return out

/-- Resize to `width × height`.

v1 implements `nearest` (index remap, all modes) and `bilinear`
(per-channel float blend of the 4 nearest source pixels, including alpha).
`bicubic`/`lanczos` fall back to `bilinear` until WP20 lands; `bilinear`
(and hence `bicubic`/`lanczos`) on a `.palette` image falls back to
`nearest`, since palette indices cannot be meaningfully interpolated.

Resizing to the current size returns `img` unchanged; resizing to a
`0 × n` or `n × 0` target yields an image with empty `data`. -/
def resize (img : Image) (width height : Nat) (resample : Resample := .bilinear) : Image :=
  if width == img.width && height == img.height then img
  else if width == 0 || height == 0 then
    { img with width, height, data := ByteArray.empty }
  else
    let mode := img.mode
    let srcW := img.width
    let srcH := img.height
    let resized := img.modifyData fun data =>
      match resample with
      | .nearest => resizeNearestData mode srcW srcH width height data
      | .bilinear | .bicubic | .lanczos =>
        if mode == .palette then resizeNearestData mode srcW srcH width height data
        else resizeBilinearData mode srcW srcH width height data
    { resized with width, height }

end Image

end PILean
