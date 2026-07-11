import PILean.Codec.Types
import PILean.Binary.Reader
import PILean.Binary.Writer

/-!
# Netpbm (PPM/PGM/PBM)

The simplest viewable formats — both ASCII (P1–P3) and binary (P4–P6)
variants, encode and decode (WP4). Header comments (`#` to end of line)
must be skipped; they may appear anywhere whitespace is allowed, including
inside the run of header fields. Encode: gray → P5, everything else → P6 via
RGB conversion (binary variants; maxval 255). Decode maps P1/P4 (bitmap) and
P2/P5 (graymap) to `.gray`, P3/P6 (pixmap) to `.rgb`.

## Bitmap convention

In P1/P4, a `1` bit means BLACK and a `0` bit means WHITE (the opposite of
numeric magnitude); decoded to gray `0`/`255` respectively.

## Grayscale/pixmap sample scaling

P2/P3/P5/P6 carry a `maxval`; samples are linearly rescaled to 0–255 via
`v * 255 / maxval` (integer division, i.e. floor — not rounded). Only
`maxval ≤ 255` is supported; larger maxvals (which use two bytes per sample
in the binary variants) are `DecodeError.unsupported`.
-/

namespace PILean.Netpbm

open PILean.Binary

/-- Is `b` the ASCII `'#'` comment-start byte? -/
@[inline] private def isHash (b : UInt8) : Bool := b == 35

/-- Skip ASCII whitespace and `#`-to-end-of-line comments, in any
combination — Netpbm allows comments anywhere whitespace is allowed. -/
private def skipWsAndComments : ParseM Unit := do
  repeat
    match ← ParseM.peek? with
    | some b =>
      if ParseM.isAsciiWhitespace b then
        let _ ← ParseM.u8
      else if isHash b then
        repeat
          match ← ParseM.peek? with
          | some c =>
            let _ ← ParseM.u8
            if c == 10 then break  -- '\n' ends the comment
          | none => break
      else break
    | none => break

/-- Skip comment-aware whitespace, then read a decimal natural number.
Fails if no digit follows. -/
private def headerNat : ParseM Nat := do
  skipWsAndComments
  let mut n := 0
  let mut seen := false
  repeat
    match ← ParseM.peek? with
    | some b =>
      if 48 ≤ b && b ≤ 57 then
        let _ ← ParseM.u8
        n := n * 10 + (b.toNat - 48)
        seen := true
      else break
    | none => break
  unless seen do
    throw (.corrupt (← ParseM.pos) "expected a decimal integer")
  return n

/-- Consume exactly one raw whitespace byte (the mandatory separator between
a binary variant's header and its raw pixel data — no comments allowed
here, the following bytes are opaque binary data). -/
private def consumeSingleWs : ParseM Unit := do
  let b ← ParseM.u8
  unless ParseM.isAsciiWhitespace b do
    throw (.corrupt (← ParseM.pos) "expected a single whitespace byte after the header")

/-- `maxval` must be positive and ≤ 255 (larger maxvals use two-byte samples
in the binary formats, which PILean does not support). -/
private def validateMaxval (m : Nat) : ParseM Unit := do
  if m == 0 then
    throw (.corrupt (← ParseM.pos) "maxval must be positive")
  else if m > 255 then
    throw (.unsupported "netpbm" s!"maxval {m} > 255 (16-bit samples unsupported)")

/-- Rescale a sample in `[0, maxval]` to `[0, 255]` via floor division,
clamping to 255 in case the input exceeds its declared `maxval`. -/
@[inline] private def scaleSample (v maxval : Nat) : UInt8 :=
  UInt8.ofNat (min (v * 255 / maxval) 255)

/-- Rescale every byte of `raw` by `maxval` (identity when `maxval = 255`,
the common case, taken as a direct-copy fast path). -/
private def scaleBytes (raw : ByteArray) (maxval : Nat) : ByteArray :=
  if maxval == 255 then raw
  else Id.run do
    let mut d := ByteArray.emptyWithCapacity raw.size
    for i in [0:raw.size] do
      d := d.push (scaleSample (raw.get! i).toNat maxval)
    return d

/-- Decode `width * height` ASCII `0`/`1` tokens (P1) into gray bytes,
`1 → 0` (black), `0 → 255` (white). -/
private def decodeP1 (width height : Nat) : ParseM ByteArray := do
  let mut d := ByteArray.emptyWithCapacity (width * height)
  for _ in [0:width * height] do
    let v ← headerNat
    if v > 1 then throw (.corrupt (← ParseM.pos) "P1 sample must be 0 or 1")
    d := d.push (if v == 1 then 0 else 255)
  return d

/-- Decode `width * height` ASCII gray samples (P2), rescaled by `maxval`. -/
private def decodeP2 (width height maxval : Nat) : ParseM ByteArray := do
  let mut d := ByteArray.emptyWithCapacity (width * height)
  for _ in [0:width * height] do
    let v ← headerNat
    d := d.push (scaleSample v maxval)
  return d

/-- Decode `width * height` ASCII RGB triples (P3), rescaled by `maxval`. -/
private def decodeP3 (width height maxval : Nat) : ParseM ByteArray := do
  let mut d := ByteArray.emptyWithCapacity (width * height * 3)
  for _ in [0:width * height] do
    let r ← headerNat
    let g ← headerNat
    let b ← headerNat
    d := d.push (scaleSample r maxval)
    d := d.push (scaleSample g maxval)
    d := d.push (scaleSample b maxval)
  return d

/-- Unpack MSB-first bit-packed rows (P4), each row padded to a byte
boundary, into gray bytes (`1 → 0` black, `0 → 255` white). -/
private def unpackP4 (width height rowBytes : Nat) (raw : ByteArray) : ByteArray := Id.run do
  let mut d := ByteArray.emptyWithCapacity (width * height)
  for y in [0:height] do
    let rowOff := y * rowBytes
    for x in [0:width] do
      let byte := raw.get! (rowOff + x / 8)
      let bit := (byte >>> (UInt8.ofNat (7 - x % 8))) &&& 1
      d := d.push (if bit == 1 then 0 else 255)
  return d

/-- Decode any of P1–P6 into an `Image` (`.gray` for bitmaps/graymaps,
`.rgb` for pixmaps). -/
def decode (bytes : ByteArray) : Except DecodeError Image :=
  Binary.ParseM.run (data := bytes) do
    let p ← ParseM.u8
    let t ← ParseM.u8
    unless p == 80 && 49 ≤ t && t ≤ 54 do
      throw (.badMagic "netpbm")
    let width ← headerNat
    let height ← headerNat
    if width == 0 || height == 0 then
      throw (.corrupt (← ParseM.pos) "zero image dimension")
    match t with
    | 49 =>  -- P1
      let data ← decodeP1 width height
      pure { width, height, mode := .gray, data }
    | 50 =>  -- P2
      let maxval ← headerNat
      validateMaxval maxval
      let data ← decodeP2 width height maxval
      pure { width, height, mode := .gray, data }
    | 51 =>  -- P3
      let maxval ← headerNat
      validateMaxval maxval
      let data ← decodeP3 width height maxval
      pure { width, height, mode := .rgb, data }
    | 52 =>  -- P4
      consumeSingleWs
      let rowBytes := (width + 7) / 8
      let raw ← ParseM.take (rowBytes * height)
      pure { width, height, mode := .gray, data := unpackP4 width height rowBytes raw }
    | 53 =>  -- P5
      let maxval ← headerNat
      validateMaxval maxval
      consumeSingleWs
      let raw ← ParseM.take (width * height)
      pure { width, height, mode := .gray, data := scaleBytes raw maxval }
    | _ =>  -- P6 ('6' == 54; unreachable otherwise by the magic-byte guard)
      let maxval ← headerNat
      validateMaxval maxval
      consumeSingleWs
      let raw ← ParseM.take (width * height * 3)
      pure { width, height, mode := .rgb, data := scaleBytes raw maxval }

/-- Promote every pixel of a non-gray/rgb image to `Color` and pack its RGB
bytes (used for `.rgba`, `.grayAlpha`, `.palette` — modes with no direct
byte-layout match for a PPM raster). -/
private def packRgbSlow (img : Image) : ByteArray := Id.run do
  let mut d := ByteArray.emptyWithCapacity (img.width * img.height * 3)
  for y in [0:img.height] do
    for x in [0:img.width] do
      let c := img.getPixel! x y
      d := d.push c.r
      d := d.push c.g
      d := d.push c.b
  return d

/-- Encode as binary PGM (P5) for `.gray`; every other mode as binary PPM
(P6), maxval 255. `.gray`/`.rgb` take a direct-buffer fast path since their
storage layout already matches the raster exactly. -/
def encode (img : Image) : Except EncodeError ByteArray :=
  match img.mode with
  | .gray =>
    let header := ByteArray.empty.pushAscii s!"P5\n{img.width} {img.height}\n255\n"
    .ok (header ++ img.data)
  | .rgb =>
    let header := ByteArray.empty.pushAscii s!"P6\n{img.width} {img.height}\n255\n"
    .ok (header ++ img.data)
  | _ =>
    let header := ByteArray.empty.pushAscii s!"P6\n{img.width} {img.height}\n255\n"
    .ok (header ++ packRgbSlow img)

/-- Netpbm codec (registered in `PILean.codecs`). -/
def codec : Codec where
  name := "netpbm"
  extensions := [".ppm", ".pgm", ".pbm", ".pnm"]
  sniff := fun b =>
    b.size ≥ 2 && b.get! 0 == 80 &&  -- 'P'
    49 ≤ b.get! 1 && b.get! 1 ≤ 54   -- '1'–'6'
  decode := decode
  encode := encode

end PILean.Netpbm
