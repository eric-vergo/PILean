import PILean.Core.Error
import PILean.Codec.Png.Filter

/-!
# Raster unpacking and Adam7 deinterlacing

Decode-only for v1 (the encoder never interlaces, matching Pillow's
default). Owned by WP12; the pass structure, per-pass filtering, and the
deinterlace entry point are internal to the PNG decoder and not part of
the frozen interface — WP12 shapes this module freely.

Two independent pieces live here:

* Bit-depth-aware raster unpacking (`channelsOf`, `bppForFilter`,
  `packedBytesPerRow`, `scaleSample`, `unpackRaster`) — turning a PNG
  color type's still bit-packed, already-unfiltered sample bytes into
  PILean's normalized one-byte-per-channel storage layout. This is
  shared by both the flat (non-interlaced) and Adam7 decode paths in
  `Png.Decode`, so it lives here rather than in `Decode.lean` itself
  (`Decode.lean` imports this module, so the dependency has to run this
  way to avoid a cycle).
* Adam7 deinterlacing (`adam7Passes`, `deinterlace`) — each of the seven
  passes is its own independently-filtered scanline group (per-pass
  `bpp`-relative filtering, per the PNG spec), which `deinterlace`
  unfilters, unpacks, and scatters into a full-resolution output buffer.

All arithmetic here is plain `Nat` (`+ - * / %`, never `Nat`-level
`<<< >>> &&&`, which this codebase reserves for fixed-width `UInt8/16/32`
values) — see `pow2` below.
-/

namespace PILean.Png

/-- `2 ^ n` computed by plain `Nat` multiplication (this module never
shifts by more than 8 — PNG bit depths top out at 16). -/
private def pow2 : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * pow2 n

/-- Number of channels (samples per pixel) for a PNG color type
(`0` grayscale, `2` truecolor, `3` palette-index, `4` grayscale+alpha,
`6` truecolor+alpha). `0` for any other value — callers must reject
invalid color types before reaching here (`Png.decode`'s IHDR validation
does this). -/
def channelsOf : Nat → Nat
  | 0 => 1
  | 2 => 3
  | 3 => 1
  | 4 => 2
  | 6 => 4
  | _ => 0

/-- The PILean `Mode` a PNG color type/bit depth combination normalizes
to; `none` for an invalid color type. Color type 4 (grayscale+alpha) is
the one case where bit depth matters: Pillow's PNG decoder promotes the
16-bit variant straight to `RGBA` (replicating the gray sample into R/G/B)
rather than decoding it as `LA` — see `unpackRaster`'s `colorType == 4`
branch, which performs the actual promotion. -/
def modeOf (colorType bitDepth : Nat) : Option Mode :=
  match colorType with
  | 0 => some .gray
  | 2 => some .rgb
  | 3 => some .palette
  | 4 => some (if bitDepth == 16 then .rgba else .grayAlpha)
  | 6 => some .rgba
  | _ => none

/-- Bytes-per-complete-pixel used by the scanline filter algorithms
(PNG spec §6.4, the `bpp` that `Filter.unfilterScanlines` takes):
`⌈bitDepth × channels / 8⌉`, minimum 1 (sub-byte-depth samples still use
`bpp = 1` — the filters key off byte distance, not bit distance). -/
def bppForFilter (colorType bitDepth : Nat) : Nat :=
  max 1 ((channelsOf colorType * bitDepth + 7) / 8)

/-- Bytes in one still bit-packed (pre-unpacking) PNG scanline of `width`
pixels: `⌈width × channels × bitDepth / 8⌉`. -/
def packedBytesPerRow (colorType bitDepth width : Nat) : Nat :=
  (width * channelsOf colorType * bitDepth + 7) / 8

/-- Scale a sub-8-bit grayscale/palette-index sample up to the full 8-bit
range, matching Pillow's load-time bit-replication scaling:
`v * 255 / (2 ^ bitDepth − 1)`, which is exact integer arithmetic for
`bitDepth ∈ {1, 2, 4}` (multipliers `255`, `85`, `17` respectively).
`bitDepth = 8` is the identity (never actually called with 16). -/
def scaleSample (bitDepth : Nat) (v : Nat) : UInt8 :=
  match bitDepth with
  | 1 => UInt8.ofNat (v * 255)
  | 2 => UInt8.ofNat (v * 85)
  | 4 => UInt8.ofNat (v * 17)
  | _ => UInt8.ofNat v

/-- Output channel count after normalization — same as `channelsOf`
except color type 4 (grayscale+alpha) at bit depth 16, which `unpackRaster`
promotes from 2 native samples to 4 (`RGBA`), matching Pillow. -/
def outputChannelsOf (colorType bitDepth : Nat) : Nat :=
  if colorType == 4 && bitDepth == 16 then 4 else channelsOf colorType

/-- Unpack one already-unfiltered raster's worth (`width × height` pixels,
no interlacing involved — used for both the flat decode path and, per
pass, by `deinterlace`) of still bit-packed PNG sample bytes into
PILean's normalized one-byte-per-channel storage layout: gray/palette
samples at bit depth 1/2/4 are widened to one byte per sample (gray is
scaled via `scaleSample`, palette indices are left raw); 16-bit samples
are truncated to their high byte per channel (never rounded — the v1
normalization policy); 8-bit samples are copied through unchanged.
Color type 4 (grayscale+alpha) at bit depth 16 is further promoted from
2 samples/pixel to 4 (`RGBA`: the gray sample's high byte replicated into
R/G/B, the alpha sample's high byte as `A`) — Pillow's PNG decoder does
the same (`LA;16` never round-trips as `LA` in Pillow, only 8-bit does).
The result is exactly `width * height * outputChannelsOf colorType
bitDepth` bytes, already in the layout `Image.data` expects for the
corresponding `Mode`. -/
def unpackRaster (colorType bitDepth width height : Nat) (raw : ByteArray) : ByteArray :=
  Id.run do
    let channels := channelsOf colorType
    let outChannels := outputChannelsOf colorType bitDepth
    let rowBytes := packedBytesPerRow colorType bitDepth width
    let mut out := ByteArray.emptyWithCapacity (width * height * outChannels)
    for y in [0:height] do
      let rowStart := y * rowBytes
      if bitDepth == 8 then
        out := out ++ raw.extract rowStart (rowStart + width * channels)
      else if bitDepth == 16 && colorType == 4 then
        -- LA;16 → RGBA promotion (see the docstring above).
        for x in [0:width] do
          let base := rowStart + x * 4
          let grayHigh := raw.get! base
          let alphaHigh := raw.get! (base + 2)
          out := ((out.push grayHigh).push grayHigh).push grayHigh |>.push alphaHigh
      else if bitDepth == 16 then
        for x in [0:width] do
          for c in [0:channels] do
            out := out.push (raw.get! (rowStart + (x * channels + c) * 2))
      else
        -- bitDepth ∈ {1, 2, 4}; channels == 1 (grayscale or palette only).
        for x in [0:width] do
          let bitOff := x * bitDepth
          let byteIdx := rowStart + bitOff / 8
          let shift := 8 - (bitOff % 8) - bitDepth
          let byteVal := (raw.get! byteIdx).toNat
          let sample := (byteVal / pow2 shift) % pow2 bitDepth
          out := out.push (if colorType == 0 then scaleSample bitDepth sample else UInt8.ofNat sample)
    return out

/-- One Adam7 pass's geometry: the pass covers pixel `(startX, startY)`
and every `(stepX, stepY)` pixel after it. -/
structure Adam7Pass where
  startX : Nat
  startY : Nat
  stepX : Nat
  stepY : Nat
  deriving Repr, Inhabited

/-- The seven Adam7 passes, in encode/decode order (PNG spec §8.2, the
standard `starting_row`/`starting_col`/`row_increment`/`col_increment`
table). -/
def adam7Passes : List Adam7Pass :=
  [ ⟨0, 0, 8, 8⟩, ⟨4, 0, 8, 8⟩, ⟨0, 4, 4, 8⟩
  , ⟨2, 0, 4, 4⟩, ⟨0, 2, 2, 4⟩, ⟨1, 0, 2, 2⟩, ⟨0, 1, 1, 2⟩ ]

/-- Pixel extent of one Adam7 pass along one axis: `⌈(full − start) / step⌉`,
or `0` if the pass starts at or past the edge of a small image (a pass
entirely off the edge contributes no scanlines at all). -/
private def passExtent (full start step : Nat) : Nat :=
  if full > start then (full - start + step - 1) / step else 0

/-- One Adam7 pass's geometry together with its pixel extent over a
particular `width × height` image. -/
private structure PassLayout where
  startX : Nat
  startY : Nat
  stepX : Nat
  stepY : Nat
  passWidth : Nat
  passHeight : Nat

/-- `adam7Passes` resolved against a `width × height` image. -/
private def passLayouts (width height : Nat) : List PassLayout :=
  adam7Passes.map fun g =>
    { startX := g.startX, startY := g.startY, stepX := g.stepX, stepY := g.stepY
      passWidth := passExtent width g.startX g.stepX
      passHeight := passExtent height g.startY g.stepY }

/-- Bytes one pass's filtered scanline group occupies in the
zlib-decompressed stream; `0` for an empty pass (entirely off the edge
of a small image). -/
private def passByteCount (colorType bitDepth : Nat) (l : PassLayout) : Nat :=
  if l.passWidth == 0 || l.passHeight == 0 then 0
  else l.passHeight * (1 + packedBytesPerRow colorType bitDepth l.passWidth)

/-- Deinterlace an Adam7 (`interlace method 1`) PNG raster. `raw` is the
full zlib-decompressed byte stream: the seven passes' filtered scanline
groups back-to-back in pass order, each unfiltered independently (a
pass's Sub/Up/Paeth history never crosses into another pass — every pass
starts fresh, as required by the PNG spec). Empty passes (zero pixel
width or height for a small image) contribute no bytes at all. Returns
the full `width × height` image in PILean's normalized per-channel
storage layout — the same shape `unpackRaster` produces for a
non-interlaced image of the same size.

Validates the total byte count every pass requires against `raw.size`
*before* allocating the full-resolution output buffer, so a tiny
compressed payload paired with an enormous declared `width`/`height`
fails fast (`corrupt`) instead of attempting a huge allocation. -/
def deinterlace (colorType bitDepth width height : Nat) (raw : ByteArray) :
    Except DecodeError ByteArray := do
  -- The *output* channel count (`unpackRaster`'s promoted `LA;16 → RGBA`
  -- included) — never `channelsOf` alone, which would under-allocate `out`
  -- and misalign the scatter below for that one color type/bit-depth combo.
  let channels := outputChannelsOf colorType bitDepth
  let layouts := passLayouts width height
  let totalBytes := layouts.foldl (init := 0) fun acc l => acc + passByteCount colorType bitDepth l
  if raw.size != totalBytes then
    throw (.corrupt raw.size
      (s!"Adam7: decompressed size {raw.size} bytes does not match the {totalBytes} " ++
        s!"bytes the seven passes require for a {width}×{height} image"))
  let bpp := bppForFilter colorType bitDepth
  let mut out : ByteArray := ByteArray.mk (Array.replicate (width * height * channels) 0)
  let mut cursor := 0
  for l in layouts do
    if l.passWidth > 0 && l.passHeight > 0 then
      let rowBytes := packedBytesPerRow colorType bitDepth l.passWidth
      let size := l.passHeight * (1 + rowBytes)
      let filtered := raw.extract cursor (cursor + size)
      cursor := cursor + size
      let passRaw ← unfilterScanlines bpp rowBytes filtered
      let passNorm := unpackRaster colorType bitDepth l.passWidth l.passHeight passRaw
      for py in [0:l.passHeight] do
        for px in [0:l.passWidth] do
          let destOff := ((l.startY + py * l.stepY) * width + (l.startX + px * l.stepX)) * channels
          let srcOff := (py * l.passWidth + px) * channels
          for c in [0:channels] do
            out := out.set! (destOff + c) (passNorm.get! (srcOff + c))
  return out

end PILean.Png
