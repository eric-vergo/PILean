import PILean.Core.Image
import PILean.Binary.Writer

/-!
# Point operations

Per-pixel adjustments (WP7): invert, brightness, contrast, threshold.
Alpha channels are preserved unchanged. Pillow-parity operations
(autocontrast, equalize, posterize, solarize, channel ops, enhancers)
are added by WP19 as new defs in this namespace.

## `.palette` handling

`invert`, `adjustBrightness`, and `adjustContrast` are point operations on
*colors*; on a `.palette` image the raw bytes are indices, not colors, so
these three transform the palette's ≤ 256 entries in place (leaving the
per-pixel indices untouched) rather than the pixel buffer — cheaper, and
the only interpretation that doesn't corrupt the image. `threshold` is
different: Pillow itself doesn't define these enhancers on `P`-mode images
either (`ImageEnhance`/`ImageOps.invert` raise on them), so this is a
documented v1 design choice, not a Pillow-matched behavior — except for
`threshold`, which resolves indices through the palette and returns a
`.gray` image (documented on `threshold` itself), since "black or white"
doesn't have a sensible palette-preserving representation in general.
-/

namespace PILean.Image

/-- `Nat → Float`, exact for every value that arises from pixel counts. -/
private def n2f (n : Nat) : Float := (UInt64.ofNat n).toFloat

/-- Round `v` to the nearest `UInt8`, clamping to `[0, 255]`. Negatives are
guarded away *before* the `Nat` conversion, per project convention. -/
private def clampByte (v : Float) : UInt8 :=
  let r := v.round
  if r ≤ 0.0 then 0
  else if r ≥ 255.0 then 255
  else UInt8.ofNat r.toUInt64.toNat

/-- Apply `f` to the color channels of every pixel of a non-`.palette`
image (alpha, if any, is the last byte of each pixel and is left alone).
The shared hot loop behind `invert`/`adjustBrightness`/`adjustContrast`. -/
private def mapColorChannels (img : Image) (f : UInt8 → UInt8) : Image :=
  let bpp := img.mode.bytesPerPixel
  let colorBytes := if img.mode.hasAlpha then bpp - 1 else bpp
  let n := img.width * img.height
  img.modifyData fun data => Id.run do
    let mut d := data
    for i in [0:n] do
      let off := i * bpp
      for c in [0:colorBytes] do
        d := d.set! (off + c) (f (d.get! (off + c)))
    return d

/-- Apply `f` to the R/G/B channels of every entry of `p` (alpha untouched).
The shared helper behind the `.palette` case of
`invert`/`adjustBrightness`/`adjustContrast`. -/
private def mapPaletteColors (p : Palette) (f : UInt8 → UInt8) : Palette :=
  { entries := Id.run do
      let mut e := p.entries
      for i in [0:p.size] do
        let base := i * 4
        e := e.set! base (f (e.get! base))
        e := e.set! (base + 1) (f (e.get! (base + 1)))
        e := e.set! (base + 2) (f (e.get! (base + 2)))
      return e }

/-- Invert every channel except alpha (`255 - v`). On `.palette` images the
palette entries are inverted (see the module docstring); pixel indices are
unchanged. -/
def invert (img : Image) : Image :=
  match img.mode, img.palette? with
  | .palette, some p => { img with palette? := some (mapPaletteColors p fun v => 255 - v) }
  | .palette, none => img
  | _, _ => mapColorChannels img fun v => 255 - v

/-- Scale brightness by `factor` (0.0 = black, 1.0 = unchanged, > 1
brighter; clamped): `out = round(v * factor)`. On `.palette` images the
palette entries are scaled (see the module docstring); pixel indices are
unchanged. -/
def adjustBrightness (img : Image) (factor : Float) : Image :=
  let scale (v : UInt8) : UInt8 := clampByte (v.toFloat * factor)
  match img.mode, img.palette? with
  | .palette, some p => { img with palette? := some (mapPaletteColors p scale) }
  | .palette, none => img
  | _, _ => mapColorChannels img scale

/-- Sum of the ITU-R 601-2 luma (`Color.luma`) of every pixel, promoting
`.gray`/`.grayAlpha` (the stored byte *is* the luma), `.rgb`/`.rgba`
(computed from the stored channels), and `.palette` (resolved through the
palette) alike. Used to compute `adjustContrast`'s pivot exactly as Pillow
computes `ImageStat.Stat(image.convert("L")).mean`. -/
private def sumLuma (img : Image) : Nat :=
  let n := img.width * img.height
  let data := img.data
  match img.mode with
  | .gray | .grayAlpha =>
    let bpp := img.mode.bytesPerPixel
    Id.run do
      let mut total := 0
      for i in [0:n] do
        total := total + (data.get! (i * bpp)).toNat
      return total
  | .rgb | .rgba =>
    let bpp := img.mode.bytesPerPixel
    Id.run do
      let mut total := 0
      for i in [0:n] do
        let off := i * bpp
        total := total +
          (Color.luma ⟨data.get! off, data.get! (off + 1), data.get! (off + 2), 255⟩).toNat
      return total
  | .palette =>
    match img.palette? with
    | some p =>
      Id.run do
        let mut total := 0
        for i in [0:n] do
          total := total + (p.get! (data.get! i).toNat).luma.toNat
        return total
    | none => 0

/-- Scale contrast about the mean by `factor` (0.0 = solid gray,
1.0 = unchanged; clamped) — PIL `ImageEnhance.Contrast` semantics: the
pivot is the mean luma of the whole image (`sumLuma` above), rounded to an
integer exactly as Pillow does (`int(mean + 0.5)`, which agrees with
`Float.round` for our non-negative domain), then
`out = round((v - pivot) * factor + pivot)` per color channel. On a
`0 × 0` image (no pixels to average) this is the identity. On `.palette`
images the palette entries are scaled (see the module docstring); pixel
indices are unchanged. -/
def adjustContrast (img : Image) (factor : Float) : Image :=
  let n := img.width * img.height
  if n == 0 then img
  else
    let pivot := (n2f (sumLuma img) / n2f n).round
    let blend (v : UInt8) : UInt8 := clampByte ((v.toFloat - pivot) * factor + pivot)
    match img.mode, img.palette? with
    | .palette, some p => { img with palette? := some (mapPaletteColors p blend) }
    | .palette, none => img
    | _, _ => mapColorChannels img blend

/-- Binarize by luma: pixels with luma ≥ `t` become white, others black.
Alpha is preserved. `.gray`/`.grayAlpha` use the stored byte as the luma
directly; `.rgb`/`.rgba` compute it from the stored channels and write the
result to all three color channels. `.palette` input is resolved through
the palette pixel-by-pixel and the result is returned as `.gray` — v1
behavior, since "black or white" has no general palette-preserving
representation (documented here, not silent). -/
def threshold (img : Image) (t : UInt8) : Image :=
  let n := img.width * img.height
  match img.mode with
  | .palette =>
    match img.palette? with
    | some p =>
      let newData := Id.run do
        let mut out := ByteArray.replicateByte n 0
        for i in [0:n] do
          let c := p.get! (img.data.get! i).toNat
          out := out.set! i (if c.luma ≥ t then 255 else 0)
        return out
      { img with mode := .gray, data := newData, palette? := none }
    | none => img
  | .gray | .grayAlpha =>
    let bpp := img.mode.bytesPerPixel
    img.modifyData fun data => Id.run do
      let mut d := data
      for i in [0:n] do
        let off := i * bpp
        d := d.set! off (if d.get! off ≥ t then 255 else 0)
      return d
  | .rgb | .rgba =>
    let bpp := img.mode.bytesPerPixel
    img.modifyData fun data => Id.run do
      let mut d := data
      for i in [0:n] do
        let off := i * bpp
        let luma := Color.luma ⟨d.get! off, d.get! (off + 1), d.get! (off + 2), 255⟩
        let v : UInt8 := if luma ≥ t then 255 else 0
        d := d.set! off v
        d := d.set! (off + 1) v
        d := d.set! (off + 2) v
      return d

end PILean.Image
