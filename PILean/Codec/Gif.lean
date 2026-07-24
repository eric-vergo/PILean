import PILean.Codec.Types
import PILean.Binary.Reader
import PILean.Binary.Writer
import PILean.Compress.Lzw
import PILean.Core.Paste
import PILean.Color.Quantize

/-!
# GIF

GIF87a/89a decode (WP15) and encode including animation (WP16), on top of
`PILean.Compress.Lzw` (WP14). The `Codec` surface is single-frame; the
frame-level API (`decode`, `encodeFrames`, `saveGif`) is the real
interface. WP15 may add a lossless lower-level `GifFile` view as new defs.

Decode composites frames to RGBA honoring disposal methods 0/1/2/3
(disposal 2 restores to *transparent*, the modern interpretation, matching
Pillow). Encode v1 builds one global color table by quantizing across
frames; per-frame local tables and frame-diff optimization come later.

## Encoder v1 palette policy (documented, per the work package)

* **Lossless fast path**: if every frame is already `.palette`-mode with
  the *identical* palette (byte-for-byte, `≤ 256` entries), that palette is
  used as the GIF's one global color table directly — no quantization, no
  remapping, exact round trip.
* **Otherwise**: every frame is pasted (via `Image.new` + `Image.paste`,
  both real operations, no special-casing) into one tall temporary `.rgb`
  image and `Image.quantize`d once (256 colors, or 255 if
  `SaveOptions.transparentIndex` is set, to leave that index free — see
  below), then every frame is independently remapped against that shared
  palette (`Palette.nearestIndex`). Deterministic, no dithering.
* `transparentIndex` reservation on the quantize path: if the requested
  index falls within the quantized palette's real range, colors are
  shifted to open up exactly that slot (filled with black, a placeholder
  that is not treated specially by `nearestIndex` — a real black pixel in
  the source can legitimately land there too; this is a known v1
  limitation of the auto-palette path, not present on the lossless path
  where the caller controls the palette directly). If the index falls
  beyond the quantized palette's range, nothing needs to move: the global
  color table is padded with black out to the next power of two anyway.
-/

namespace PILean.Gif

open PILean.Compress.Lzw (compress)

/-- GIF frame disposal method (GCE "disposal" field). -/
inductive Disposal where
  | unspecified
  | keep
  | restoreBackground
  | restorePrevious
  deriving Repr, DecidableEq, Inhabited

/-- One frame to encode: an image plus its display duration. -/
structure Frame where
  image : Image
  durationMs : Nat := 100
  deriving Inhabited

/-- Options for writing (animated) GIFs. -/
structure SaveOptions where
  /-- Number of animation loops; 0 = forever (NETSCAPE2.0 extension). -/
  loopCount : Nat := 0
  /-- Palette index rendered as transparent, if any. -/
  transparentIndex : Option UInt8 := none
  deriving Repr, Inhabited

set_option linter.unusedVariables false in
/-- Decode all frames, composited to `.rgba`, each with its display
duration in milliseconds. -/
def decode (bytes : ByteArray) : Except DecodeError (Array (Image × Nat)) :=
  .error (.unsupported "gif" "decoder not implemented yet (WP15)")

/-! ## Encoding internals -/

/-- The smallest `b` with `n ≤ 2 ^ b` (`0` for `n ≤ 1`). Used both for the
LZW `minCodeSize` (bits actually needed by the palette) and, separately,
for the global color table's power-of-two size field. -/
private def bitsNeeded (n : Nat) : Nat := Id.run do
  let mut b := 0
  while (1 <<< b) < n do
    b := b + 1
  return b

/-- Are every frame's images `.palette`-mode with byte-identical palettes
(`≤ 256` entries)? The precondition for the lossless encode path. -/
private def palettesIdentical (frames : Array Frame) : Bool := Id.run do
  match frames[0]!.image.mode, frames[0]!.image.palette? with
  | .palette, some p0 =>
    if p0.size > 256 then
      return false
    for f in frames do
      match f.image.mode, f.image.palette? with
      | .palette, some p =>
        if p.entries != p0.entries then
          return false
      | _, _ => return false
    return true
  | _, _ => return false

/-- Convert `img` to `.palette` mode against a *given* palette (nearest
RGBA match per pixel), unlike `Image.quantize` which also builds the
palette. Mirrors `Image.quantize`'s own remap step. -/
private def remapToPalette (img : Image) (palette : Palette) : Image :=
  let width := img.width
  let height := img.height
  let data : ByteArray := Id.run do
    let mut d := ByteArray.emptyWithCapacity (width * height)
    for y in [0:height] do
      for x in [0:width] do
        d := d.push (UInt8.ofNat (palette.nearestIndex (img.getPixel! x y)))
    return d
  { width, height, mode := .palette, data, palette? := some palette }

/-- Open up palette slot `reservedIndex` for `SaveOptions.transparentIndex`
by shifting later colors down one and filling the freed slot with black.
A no-op when `reservedIndex` already falls past `p`'s real colors (the
global color table's own black-padding covers it there). -/
private def insertReservedSlot (p : Palette) (reservedIndex : UInt8) : Palette :=
  let ri := reservedIndex.toNat
  if ri ≥ p.size then p
  else Id.run do
    let mut colors : Array Color := Array.emptyWithCapacity (p.size + 1)
    for i in [0:p.size + 1] do
      if i == ri then
        colors := colors.push Color.black
      else
        colors := colors.push (p.get! (if i < ri then i else i - 1))
    return Palette.ofColors colors

/-- Build the one global palette and the per-frame `.palette`-mode images
to encode from, per the module docstring's policy. -/
private def buildGlobalPalette (frames : Array Frame) (opts : SaveOptions) :
    Palette × Array Image :=
  if palettesIdentical frames then
    (frames[0]!.image.palette?.getD Palette.webSafe, frames.map (·.image))
  else
    let canvasWidth := frames[0]!.image.width
    let canvasHeight := frames[0]!.image.height
    let stacked : Image := Id.run do
      let mut s := Image.new canvasWidth (canvasHeight * frames.size) .rgb
      for i in [0:frames.size] do
        s := s.paste frames[i]!.image ⟨0, (i * canvasHeight : Int)⟩
      return s
    let targetColors := if opts.transparentIndex.isSome then 255 else 256
    let qPalette := (stacked.quantize targetColors).palette?.getD Palette.webSafe
    let finalPalette := match opts.transparentIndex with
      | none => qPalette
      | some ti => insertReservedSlot qPalette ti
    (finalPalette, frames.map fun f => remapToPalette f.image finalPalette)

/-- The 7-byte Logical Screen Descriptor: canvas size, a global color
table flagged with size field `gctSizeField` (table size `2 ^ (field + 1)`
colors), background index 0, square pixels. -/
private def logicalScreenDescriptor (width height gctSizeField : Nat) : ByteArray :=
  ByteArray.empty
    |>.pushU16le (UInt16.ofNat width)
    |>.pushU16le (UInt16.ofNat height)
    |>.push (UInt8.ofNat (0x80 ||| gctSizeField))
    |>.push 0
    |>.push 0

/-- `palette`'s entries as `gctSize * 3` bytes of packed RGB, padded with
black out to `gctSize` (which is always a power of two, ≥ `palette.size`). -/
private def colorTableBytes (palette : Palette) (gctSize : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (3 * gctSize)
  for i in [0:gctSize] do
    if i < palette.size then
      let c := palette.get! i
      b := b.push c.r |>.push c.g |>.push c.b
    else
      b := b.push 0 |>.push 0 |>.push 0
  return b

/-- The 8-byte Graphic Control Extension: display duration (converted from
milliseconds to centiseconds, rounded, clamped to `UInt16`), disposal
method 1 ("keep" — v1's only supported method, full-frame replacement),
and an optional transparent color index. -/
private def graphicControlExtension (durationMs : Nat) (transparentIndex? : Option UInt8) :
    ByteArray :=
  let centiseconds := min 65535 ((durationMs + 5) / 10)
  let disposal : UInt8 := 1
  let transparentFlag : UInt8 := if transparentIndex?.isSome then 1 else 0
  let packed : UInt8 := (disposal <<< 2) ||| transparentFlag
  ByteArray.empty
    |>.push 0x21 |>.push 0xF9 |>.push 0x04
    |>.push packed
    |>.pushU16le (UInt16.ofNat centiseconds)
    |>.push (transparentIndex?.getD 0)
    |>.push 0x00

/-- The 10-byte Image Descriptor for a full-canvas frame at `(0, 0)`: no
local color table, no interlacing. -/
private def imageDescriptor (width height : Nat) : ByteArray :=
  ByteArray.empty
    |>.push 0x2C
    |>.pushU16le 0 |>.pushU16le 0
    |>.pushU16le (UInt16.ofNat width) |>.pushU16le (UInt16.ofNat height)
    |>.push 0x00

/-- Pack `data` into `≤ 255`-byte sub-blocks (each preceded by its length
byte), terminated by a zero-length block. -/
private def subBlocks (data : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (data.size + data.size / 255 + 2)
  let mut i := 0
  while i < data.size do
    let n := min 255 (data.size - i)
    out := out.push (UInt8.ofNat n)
    out := out ++ data.extract i (i + n)
    i := i + n
  out := out.push 0x00
  return out

/-- The NETSCAPE2.0 application extension requesting `loopCount` animation
loops (`0` = forever), written once when there is more than one frame. -/
private def netscapeLoopExtension (loopCount : Nat) : ByteArray :=
  ByteArray.empty
    |>.push 0x21 |>.push 0xFF |>.push 0x0B
    |>.pushAscii "NETSCAPE2.0"
    |>.push 0x03 |>.push 0x01
    |>.pushU16le (UInt16.ofNat (min 65535 loopCount))
    |>.push 0x00

/-- Encode frames as an (animated, if more than one frame) GIF. Every
frame must share the first frame's size (`EncodeError.invalidArg`
otherwise); an empty `frames` array is also `EncodeError.invalidArg`. See
the module docstring for the palette policy. -/
def encodeFrames (frames : Array Frame) (opts : SaveOptions := {}) :
    Except EncodeError ByteArray := do
  if frames.isEmpty then
    throw (.invalidArg "cannot encode a GIF with zero frames")
  let canvasWidth := frames[0]!.image.width
  let canvasHeight := frames[0]!.image.height
  if canvasWidth == 0 || canvasHeight == 0 then
    throw (.invalidArg "cannot encode a zero-dimension GIF")
  for f in frames do
    if f.image.width != canvasWidth || f.image.height != canvasHeight then
      throw (.invalidArg
        s!"all GIF frames must share the first frame's {canvasWidth}x{canvasHeight} size, \
           got {f.image.width}x{f.image.height}")
  let (globalPalette, indexImages) := buildGlobalPalette frames opts
  let paletteSize := max 1 globalPalette.size
  let minCodeSize := max 2 (bitsNeeded paletteSize)
  let gctSizeField := Id.run do
    let mut n := 0
    while (2 <<< n) < paletteSize do
      n := n + 1
    return n
  let gctSize := 2 <<< gctSizeField
  let mut out := "GIF89a".toUTF8
  out := out ++ logicalScreenDescriptor canvasWidth canvasHeight gctSizeField
  out := out ++ colorTableBytes globalPalette gctSize
  if frames.size > 1 then
    out := out ++ netscapeLoopExtension opts.loopCount
  for i in [0:frames.size] do
    let frame := frames[i]!
    let idxImg := indexImages[i]!
    out := out ++ graphicControlExtension frame.durationMs opts.transparentIndex
    out := out ++ imageDescriptor canvasWidth canvasHeight
    out := out.push (UInt8.ofNat minCodeSize)
    out := out ++ subBlocks (compress minCodeSize idxImg.data)
  out := out.push 0x3B
  return out

/-- Write an animated GIF to a file. -/
def saveGif (path : System.FilePath) (frames : Array Frame)
    (opts : SaveOptions := {}) : IO Unit := do
  match encodeFrames frames opts with
  | .ok bytes => IO.FS.writeBinFile path bytes
  | .error e => throw (IO.userError (toString e))

/-- GIF codec (single-frame view; registered in `PILean.codecs`). -/
def codec : Codec where
  name := "gif"
  extensions := [".gif"]
  sniff := fun b =>
    b.size ≥ 6 && b.get! 0 == 71 && b.get! 1 == 73 && b.get! 2 == 70 &&
    b.get! 3 == 56 && (b.get! 4 == 55 || b.get! 4 == 57) && b.get! 5 == 97  -- GIF87a/89a
  decode := fun b => do
    let frames ← decode b
    match frames[0]? with
    | some (img, _) => return img
    | none => throw (.corrupt 0 "GIF contains no frames")
  encode := fun img => encodeFrames #[{ image := img }]

end PILean.Gif
