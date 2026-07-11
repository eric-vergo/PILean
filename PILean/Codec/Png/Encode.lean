import PILean.Codec.Types
import PILean.Codec.Png.Chunk
import PILean.Codec.Png.Filter
import PILean.Compress.Zlib

/-!
# PNG encoding

WP11. v1 writes bit depth 8 only: `.gray` → color type 0, `.grayAlpha` → 4,
`.rgb` → 2, `.rgba` → 6, `.palette` → 3 (8-bit PLTE even for small
palettes — valid, just not minimal). Works the moment stored-block DEFLATE
exists; compression quality improves transparently as WP10 lands.
-/

namespace PILean.Png

open PILean.Compress.Zlib (compress)

/-- PNG encode options. -/
structure Options where
  /-- DEFLATE compression level, 0 (stored) – 9. -/
  level : Nat := 6
  /-- Scanline filter heuristic. -/
  heuristic : FilterHeuristic := .msad
  deriving Repr, Inhabited

/-- The 13-byte IHDR payload: width, height, bit depth 8, `colorType`,
compression/filter/interlace methods 0 (PILean never writes interlaced
PNGs). -/
private def ihdrPayload (width height : Nat) (colorType : UInt8) : ByteArray :=
  (ByteArray.empty.pushU32be (UInt32.ofNat width)).pushU32be (UInt32.ofNat height)
    |>.push 8
    |>.push colorType
    |>.push 0
    |>.push 0
    |>.push 0

/-- A palette's entries as `width * 3` bytes of packed RGB (the PLTE
payload). -/
private def paletteRgbBytes (p : Palette) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (3 * p.size)
  for i in [0:p.size] do
    let c := p.get! i
    b := b.push c.r |>.push c.g |>.push c.b
  return b

/-- A palette's entries as one alpha byte each (the tRNS payload). -/
private def paletteAlphaBytes (p : Palette) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity p.size
  for i in [0:p.size] do
    b := b.push (p.get! i).a
  return b

/-- Does any entry of `p` have alpha `< 255`? Determines whether a tRNS
chunk is needed. -/
private def paletteHasAlpha (p : Palette) : Bool := Id.run do
  for i in [0:p.size] do
    if (p.get! i).a != 255 then return true
  return false

/-- PNG color type for each `Mode` (bit depth 8 always, v1). -/
private def colorTypeOf : Mode → UInt8
  | .gray => 0
  | .rgb => 2
  | .palette => 3
  | .grayAlpha => 4
  | .rgba => 6

/-- Encode as PNG with explicit options. Requires `width ≥ 1` and
`height ≥ 1` (`EncodeError.invalidArg` otherwise); every mode encodes
successfully given nonzero dimensions (`.palette` requires `img.palette?`
to be set, which every well-formed `.palette` image satisfies). Writes
IHDR, `PLTE`/`tRNS` for `.palette` (tRNS only when some palette entry has
alpha `< 255`), one `IDAT`, then `IEND`. Bit depth 8, no interlacing. -/
def encodeWith (opts : Options) (img : Image) : Except EncodeError ByteArray := do
  if img.width == 0 || img.height == 0 then
    throw (.invalidArg "cannot encode a zero-dimension image as PNG")
  if img.mode == .palette && img.palette?.isNone then
    throw (.invalidArg "cannot encode a .palette image without a palette")
  let bpp := img.mode.bytesPerPixel
  let bytesPerRow := img.width * bpp
  let filtered := filterScanlines bpp bytesPerRow img.data opts.heuristic
  let idat := compress filtered opts.level
  let mut out := signature
  out := appendChunk out "IHDR" (ihdrPayload img.width img.height (colorTypeOf img.mode))
  -- The `.palette, none` case was already rejected above, so `getD` here is
  -- unreachable dead weight, never an actual fallback.
  if img.mode == .palette then
    let p := img.palette?.getD { entries := ByteArray.empty }
    out := appendChunk out "PLTE" (paletteRgbBytes p)
    if paletteHasAlpha p then
      out := appendChunk out "tRNS" (paletteAlphaBytes p)
  out := appendChunk out "IDAT" idat
  out := appendChunk out "IEND" ByteArray.empty
  return out

/-- Encode as PNG with default options. -/
def encode (img : Image) : Except EncodeError ByteArray :=
  encodeWith {} img

end PILean.Png
