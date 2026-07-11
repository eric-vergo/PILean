import PILean.Core.Image

/-!
# Mode conversion

`Image.convert` — total conversion between all `Mode`s, with fast
direct-buffer paths for the common `gray↔rgb`, `rgb↔rgba`, and
`gray↔grayAlpha` pairs, and a general RGBA-promotion path (`convertGeneral`)
for every other pair. Grayscale targets use `Color.luma` (Pillow-exact).
Conversion **to** `.palette` uses nearest-match against `Palette.webSafe`;
adaptive quantization is `Image.quantize`. Conversion **from** `.palette`
resolves each index through the source's own palette.

`rawColorAt`/`rawPixelBytes` decode/encode one pixel directly against a
`ByteArray` at a given mode; they are shared with `Image.alphaComposite`
(`PILean/Core/Paste.lean`), which needs the same raw two-buffer access.
-/

namespace PILean.Image

/-- Decode the pixel stored at byte offset `off` in `data` (encoded per
`mode`, resolving `.palette` indices via `palette?`) into an RGBA `Color`.
Panics if `mode = .palette` and `palette?` is `none` — a `.palette` image
without a palette violates `Image`'s invariant and is a PILean bug, not bad
input data. -/
def rawColorAt (mode : Mode) (palette? : Option Palette) (data : ByteArray) (off : Nat) : Color :=
  match mode with
  | .gray => Color.gray (data.get! off)
  | .grayAlpha => ⟨data.get! off, data.get! off, data.get! off, data.get! (off + 1)⟩
  | .rgb => ⟨data.get! off, data.get! (off + 1), data.get! (off + 2), 255⟩
  | .rgba => ⟨data.get! off, data.get! (off + 1), data.get! (off + 2), data.get! (off + 3)⟩
  | .palette =>
    match palette? with
    | some p => p.get! (data.get! off).toNat
    | none => panic! "PILean.Image: palette-mode image without palette"

/-- Encode `c` in the storage format of `mode`, resolving `.palette` via
nearest palette entry (linear scan; see `Palette.nearestIndex`). Panics
under the same invariant-violation condition as `rawColorAt`. -/
def rawPixelBytes (mode : Mode) (palette? : Option Palette) (c : Color) : Array UInt8 :=
  match mode with
  | .gray => #[c.luma]
  | .grayAlpha => #[c.luma, c.a]
  | .rgb => #[c.r, c.g, c.b]
  | .rgba => #[c.r, c.g, c.b, c.a]
  | .palette =>
    match palette? with
    | some p => #[UInt8.ofNat (p.nearestIndex c)]
    | none => panic! "PILean.Image: palette-mode image without palette"

/-- General conversion: promote every source pixel to `Color` (resolving
`.palette` sources through their own palette) and re-encode in `mode`
(building a fresh `Palette.webSafe` when `mode = .palette`). Handles every
mode pair not covered by a fast path in `convert`. -/
private def convertGeneral (img : Image) (mode : Mode) : Image :=
  let n := img.width * img.height
  let srcBpp := img.mode.bytesPerPixel
  let dstBpp := mode.bytesPerPixel
  let palette? := if mode == .palette then some Palette.webSafe else none
  let data := Id.run do
    let mut d := ByteArray.emptyWithCapacity (n * dstBpp)
    for i in [0:n] do
      let c := rawColorAt img.mode img.palette? img.data (i * srcBpp)
      for b in rawPixelBytes mode palette? c do
        d := d.push b
    return d
  { img with mode, data, palette? }

/-- Convert the image to `mode`. Total: every mode converts to every other.
The identity conversion (`img.mode = mode`) returns `img` unchanged.
Converting to `.palette` uses the web-safe palette (see `Image.quantize`
for adaptive palettes). -/
def convert (img : Image) (mode : Mode) : Image :=
  if img.mode == mode then img else
  let n := img.width * img.height
  match img.mode, mode with
  | .gray, .rgb =>
    let data := Id.run do
      let mut d := ByteArray.emptyWithCapacity (n * 3)
      for i in [0:n] do
        let g := img.data.get! i
        d := d.push g |>.push g |>.push g
      return d
    { img with mode := .rgb, data, palette? := none }
  | .rgb, .gray =>
    let data := Id.run do
      let mut d := ByteArray.emptyWithCapacity n
      for i in [0:n] do
        let off := i * 3
        let c : Color := ⟨img.data.get! off, img.data.get! (off + 1), img.data.get! (off + 2), 255⟩
        d := d.push c.luma
      return d
    { img with mode := .gray, data, palette? := none }
  | .rgb, .rgba =>
    let data := Id.run do
      let mut d := ByteArray.emptyWithCapacity (n * 4)
      for i in [0:n] do
        let off := i * 3
        d := d.push (img.data.get! off) |>.push (img.data.get! (off + 1))
              |>.push (img.data.get! (off + 2)) |>.push 255
      return d
    { img with mode := .rgba, data, palette? := none }
  | .rgba, .rgb =>
    let data := Id.run do
      let mut d := ByteArray.emptyWithCapacity (n * 3)
      for i in [0:n] do
        let off := i * 4
        d := d.push (img.data.get! off) |>.push (img.data.get! (off + 1))
              |>.push (img.data.get! (off + 2))
      return d
    { img with mode := .rgb, data, palette? := none }
  | .gray, .grayAlpha =>
    let data := Id.run do
      let mut d := ByteArray.emptyWithCapacity (n * 2)
      for i in [0:n] do
        d := d.push (img.data.get! i) |>.push 255
      return d
    { img with mode := .grayAlpha, data, palette? := none }
  | .grayAlpha, .gray =>
    let data := Id.run do
      let mut d := ByteArray.emptyWithCapacity n
      for i in [0:n] do
        d := d.push (img.data.get! (i * 2))
      return d
    { img with mode := .gray, data, palette? := none }
  | _, _ => convertGeneral img mode

end PILean.Image
