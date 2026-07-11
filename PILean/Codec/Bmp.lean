import PILean.Codec.Types
import PILean.Binary.Reader
import PILean.Binary.Writer

/-!
# BMP

Windows bitmaps (WP4). v1 scope: BI_RGB (uncompressed) 24-bit
and 32-bit, plus 8-bit paletted; BITMAPINFOHEADER; decode both bottom-up
(positive height) and top-down (negative height) row orders; rows are
padded to 4-byte boundaries. Encode: `.rgb` → 24-bit, `.rgba` → 32-bit,
`.palette`/`.gray` → 8-bit paletted, `.grayAlpha` → 32-bit via RGBA.

Byte layout verified against Pillow 11.3.0's own BMP reader/writer: 24-bit
rows are `B, G, R`; 32-bit rows are `B, G, R, A` (Pillow's BMP encoder
*does* write real alpha in the fourth byte, even though its own decoder
discards it — PILean's decoder keeps it, matching the task's `.rgba` spec);
8-bit palette entries are `B, G, R, X` quads; all raster data is stored
bottom-up by default with rows padded to a 4-byte boundary.
-/

namespace PILean.Bmp

open PILean.Binary

/-- Interpret a little-endian `UInt32` as a signed 32-bit two's-complement
integer (BMP's `LONG` header fields). -/
private def toI32 (u : UInt32) : Int :=
  if u.toNat < 0x80000000 then (u.toNat : Int) else (u.toNat : Int) - 0x100000000

/-- Round `n` up to the next multiple of 4 (BMP row padding). -/
@[inline] private def alignUp4 (n : Nat) : Nat := (n + 3) / 4 * 4

/-- Read `n` palette entries as BGRX quads, converting to RGBA (alpha
always opaque — BMP palettes carry no usable alpha). -/
private def readPaletteEntries (n : Nat) : ParseM Palette := do
  let mut p : Palette := { entries := ByteArray.emptyWithCapacity (4 * n) }
  for _ in [0:n] do
    let b ← ParseM.u8
    let g ← ParseM.u8
    let r ← ParseM.u8
    let _reserved ← ParseM.u8
    p := p.push ⟨r, g, b, 255⟩
  return p

/-- Skip from the current position to the absolute pixel-data offset
recorded in the file header. -/
private def seekTo (offset : Nat) : ParseM Unit := do
  let cur ← ParseM.pos
  if offset < cur then
    throw (.corrupt cur "pixel data offset precedes end of headers")
  ParseM.skip (offset - cur)

/-- Unpack 8-bit palette-index rows (row order per `topDown`, padding
stripped) into a flat row-major index buffer. -/
private def unpack8 (width height rowBytes : Nat) (topDown : Bool) (raw : ByteArray) :
    ByteArray := Id.run do
  let mut d := ByteArray.emptyWithCapacity (width * height)
  for y in [0:height] do
    let srcY := if topDown then y else height - 1 - y
    let rowOff := srcY * rowBytes
    for x in [0:width] do
      d := d.push (raw.get! (rowOff + x))
  return d

/-- Unpack 24-bit BGR rows into a flat row-major RGB buffer. -/
private def unpack24 (width height rowBytes : Nat) (topDown : Bool) (raw : ByteArray) :
    ByteArray := Id.run do
  let mut d := ByteArray.emptyWithCapacity (width * height * 3)
  for y in [0:height] do
    let srcY := if topDown then y else height - 1 - y
    let rowOff := srcY * rowBytes
    for x in [0:width] do
      let o := rowOff + x * 3
      let b := raw.get! o
      let g := raw.get! (o + 1)
      let r := raw.get! (o + 2)
      d := d.push r
      d := d.push g
      d := d.push b
  return d

/-- Unpack 32-bit BGRA rows into a flat row-major RGBA buffer. -/
private def unpack32 (width height rowBytes : Nat) (topDown : Bool) (raw : ByteArray) :
    ByteArray := Id.run do
  let mut d := ByteArray.emptyWithCapacity (width * height * 4)
  for y in [0:height] do
    let srcY := if topDown then y else height - 1 - y
    let rowOff := srcY * rowBytes
    for x in [0:width] do
      let o := rowOff + x * 4
      let b := raw.get! o
      let g := raw.get! (o + 1)
      let r := raw.get! (o + 2)
      let a := raw.get! (o + 3)
      d := d.push r
      d := d.push g
      d := d.push b
      d := d.push a
  return d

/-- Decode a BMP (BI_RGB 8/24/32-bit, 40-byte BITMAPINFOHEADER only). -/
def decode (bytes : ByteArray) : Except DecodeError Image :=
  Binary.ParseM.run (data := bytes) do
    ParseM.expectBytes "BM".toUTF8 "bmp"
    let _bfSize ← ParseM.u32le
    let _reserved1 ← ParseM.u16le
    let _reserved2 ← ParseM.u16le
    let bfOffBits ← ParseM.u32le
    let biSize ← ParseM.u32le
    unless biSize == 40 do
      throw (.unsupported "bmp" s!"{biSize}-byte info header (only BITMAPINFOHEADER=40)")
    let rawWidth ← ParseM.u32le
    let rawHeight ← ParseM.u32le
    let widthI := toI32 rawWidth
    if widthI < 0 then throw (.unsupported "bmp" "negative width")
    let width := widthI.toNat
    let heightI := toI32 rawHeight
    let topDown := heightI < 0
    let height := heightI.natAbs
    if width == 0 || height == 0 then
      throw (.corrupt (← ParseM.pos) "zero image dimension")
    let _planes ← ParseM.u16le
    let bpp ← ParseM.u16le
    let compression ← ParseM.u32le
    unless compression == 0 do
      throw (.unsupported "bmp" s!"compression {compression} (only BI_RGB)")
    let _imageSize ← ParseM.u32le
    let _xPixelsPerM ← ParseM.u32le
    let _yPixelsPerM ← ParseM.u32le
    let colorsUsed ← ParseM.u32le
    let _colorsImportant ← ParseM.u32le
    match bpp with
    | 8 =>
      let n := if colorsUsed == 0 then 256 else min colorsUsed.toNat 256
      let palette ← readPaletteEntries n
      seekTo bfOffBits.toNat
      let rowBytes := alignUp4 width
      let raw ← ParseM.take (rowBytes * height)
      pure { width, height, mode := .palette,
             data := unpack8 width height rowBytes topDown raw, palette? := some palette }
    | 24 =>
      seekTo bfOffBits.toNat
      let rowBytes := alignUp4 (width * 3)
      let raw ← ParseM.take (rowBytes * height)
      pure { width, height, mode := .rgb, data := unpack24 width height rowBytes topDown raw }
    | 32 =>
      seekTo bfOffBits.toNat
      let rowBytes := width * 4  -- always a multiple of 4 already
      let raw ← ParseM.take (rowBytes * height)
      pure { width, height, mode := .rgba, data := unpack32 width height rowBytes topDown raw }
    | _ => throw (.unsupported "bmp" s!"{bpp}-bit depth")

/-- The 14-byte BITMAPFILEHEADER followed by the 40-byte BITMAPINFOHEADER. -/
private def headers (width height dataOffset bpp paletteEntries imageSize : Nat) : ByteArray :=
  let fileSize := dataOffset + imageSize
  ByteArray.empty
    |>.pushAscii "BM"
    |>.pushU32le (UInt32.ofNat fileSize)
    |>.pushU16le 0
    |>.pushU16le 0
    |>.pushU32le (UInt32.ofNat dataOffset)
    |>.pushU32le 40
    |>.pushU32le (UInt32.ofNat width)
    |>.pushU32le (UInt32.ofNat height)  -- positive: bottom-up
    |>.pushU16le 1
    |>.pushU16le (UInt16.ofNat bpp)
    |>.pushU32le 0  -- BI_RGB
    |>.pushU32le (UInt32.ofNat imageSize)
    |>.pushU32le 0
    |>.pushU32le 0
    |>.pushU32le (UInt32.ofNat paletteEntries)
    |>.pushU32le 0

/-- Encode `.rgb` pixel data (row-major, top-down) as bottom-up padded
24-bit BGR rows. -/
private def packRows24 (img : Image) (rowBytes : Nat) : ByteArray := Id.run do
  let width := img.width
  let height := img.height
  let mut d := ByteArray.emptyWithCapacity (rowBytes * height)
  for y in [0:height] do
    let srcY := height - 1 - y
    let rowOff := srcY * width * 3
    for x in [0:width] do
      let o := rowOff + x * 3
      d := d.push (img.data.get! (o + 2))
      d := d.push (img.data.get! (o + 1))
      d := d.push (img.data.get! o)
    for _ in [0:rowBytes - width * 3] do
      d := d.push 0
  return d

/-- Encode `.rgba` pixel data as bottom-up 32-bit BGRA rows (already a
multiple of 4 bytes wide, so no padding is needed). -/
private def packRows32 (img : Image) : ByteArray := Id.run do
  let width := img.width
  let height := img.height
  let mut d := ByteArray.emptyWithCapacity (width * height * 4)
  for y in [0:height] do
    let srcY := height - 1 - y
    let rowOff := srcY * width * 4
    for x in [0:width] do
      let o := rowOff + x * 4
      d := d.push (img.data.get! (o + 2))
      d := d.push (img.data.get! (o + 1))
      d := d.push (img.data.get! o)
      d := d.push (img.data.get! (o + 3))
  return d

/-- Encode `.grayAlpha` pixel data (gray, alpha) as bottom-up 32-bit BGRA
rows (gray expands to equal B, G, R). -/
private def packRows32GrayAlpha (img : Image) : ByteArray := Id.run do
  let width := img.width
  let height := img.height
  let mut d := ByteArray.emptyWithCapacity (width * height * 4)
  for y in [0:height] do
    let srcY := height - 1 - y
    let rowOff := srcY * width * 2
    for x in [0:width] do
      let o := rowOff + x * 2
      let gray := img.data.get! o
      let alpha := img.data.get! (o + 1)
      d := d.push gray
      d := d.push gray
      d := d.push gray
      d := d.push alpha
  return d

/-- Encode single-byte-per-pixel index data (`.gray` luma values, or
`.palette` indices) as bottom-up padded 8-bit rows. -/
private def packRows8 (img : Image) (rowBytes : Nat) : ByteArray := Id.run do
  let width := img.width
  let height := img.height
  let mut d := ByteArray.emptyWithCapacity (rowBytes * height)
  for y in [0:height] do
    let srcY := height - 1 - y
    let rowOff := srcY * width
    for x in [0:width] do
      d := d.push (img.data.get! (rowOff + x))
    for _ in [0:rowBytes - width] do
      d := d.push 0
  return d

/-- A 256-entry linear grayscale palette, `BGRX` quads (`i, i, i, 0`). -/
private def grayPaletteBytes : ByteArray := Id.run do
  let mut p := ByteArray.emptyWithCapacity 1024
  for i in [0:256] do
    let v := UInt8.ofNat i
    p := p.push v |>.push v |>.push v |>.push 0
  return p

/-- `p`'s entries (≤ 256) as `BGRX` quads. -/
private def paletteAsBgrx (p : Palette) : ByteArray := Id.run do
  let n := min p.size 256
  let mut d := ByteArray.emptyWithCapacity (4 * n)
  for i in [0:n] do
    let c := p.get! i
    d := d.push c.b |>.push c.g |>.push c.r |>.push 0
  return d

/-- Encode as an uncompressed BI_RGB BMP: `.rgb` → 24-bit, `.rgba` → 32-bit,
`.grayAlpha` → 32-bit (RGB expanded from gray), `.gray` → 8-bit with a
256-entry grayscale palette, `.palette` → 8-bit with its own palette.
Always bottom-up with rows padded to a 4-byte boundary. -/
def encode (img : Image) : Except EncodeError ByteArray :=
  match img.mode with
  | .rgb =>
    let rowBytes := alignUp4 (img.width * 3)
    let pixels := packRows24 img rowBytes
    let hdr := headers img.width img.height 54 24 0 pixels.size
    .ok (hdr ++ pixels)
  | .rgba =>
    let pixels := packRows32 img
    let hdr := headers img.width img.height 54 32 0 pixels.size
    .ok (hdr ++ pixels)
  | .grayAlpha =>
    let pixels := packRows32GrayAlpha img
    let hdr := headers img.width img.height 54 32 0 pixels.size
    .ok (hdr ++ pixels)
  | .gray =>
    let rowBytes := alignUp4 img.width
    let pixels := packRows8 img rowBytes
    let pal := grayPaletteBytes
    let hdr := headers img.width img.height (54 + pal.size) 8 256 pixels.size
    .ok (hdr ++ pal ++ pixels)
  | .palette =>
    match img.palette? with
    | none => .error (.invalidArg "cannot encode a .palette image without a palette")
    | some p =>
      let rowBytes := alignUp4 img.width
      let pixels := packRows8 img rowBytes
      let pal := paletteAsBgrx p
      let hdr := headers img.width img.height (54 + pal.size) 8 (min p.size 256) pixels.size
      .ok (hdr ++ pal ++ pixels)

/-- BMP codec (registered in `PILean.codecs`). -/
def codec : Codec where
  name := "bmp"
  extensions := [".bmp", ".dib"]
  sniff := fun b => b.size ≥ 2 && b.get! 0 == 66 && b.get! 1 == 77  -- "BM"
  decode := decode
  encode := encode

end PILean.Bmp
