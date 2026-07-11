import PILean.Codec.Types
import PILean.Binary.Reader
import PILean.Binary.Writer
import PILean.Core.Convert

/-!
# QOI — the Quite OK Image format

A tiny lossless format (spec: qoiformat.org): a 14-byte header followed by a
stream of variable-length chunks, one 8-byte end marker, no other framing.

Header: magic `"qoif"`, `width`/`height` as big-endian `u32`, `channels`
(3 = RGB, 4 = RGBA), `colorspace` (0 = sRGB with linear alpha, 1 = all
channels linear — opaque to PILean, round-tripped via `Image.info`'s
`"colorspace"` key).

Chunk stream: each pixel is encoded relative to the previous pixel and a
64-entry table of recently seen pixels (`index_position = (r*3 + g*5 + b*7 +
a*11) mod 64`, computed here via `&&& 63` since 64 is a power of two):

* `QOI_OP_RGB` (`0xfe`) / `QOI_OP_RGBA` (`0xff`) — literal bytes.
* `QOI_OP_INDEX` (`00xxxxxx`) — repeat table entry `xxxxxx`.
* `QOI_OP_DIFF` (`01xxxxxx`) — per-channel delta in `[-2, 1]`, alpha
  unchanged.
* `QOI_OP_LUMA` (`10xxxxxx` + one byte) — green delta in `[-32, 31]`, red/blue
  deltas (relative to the green delta) in `[-8, 7]`, alpha unchanged.
* `QOI_OP_RUN` (`11xxxxxx`) — repeat the previous pixel `xxxxxx + 1` times
  (`1..62`; `62`/`63` are reserved for the two literal ops above).

All delta arithmetic is done directly in wraparound `UInt8` (Lean's `UInt8`
subtraction/addition is mod-256, exactly QOI's intended per-channel
arithmetic), avoiding any signed-integer conversion.

Decode produces `.rgb` (3-channel) or `.rgba` (4-channel) images. Encode:
`.rgb` images stay `.rgb` (`channels = 3`); every other mode is converted to
`.rgba` first via `Image.convert` (`channels = 4`) — QOI has no encoding for
any other pixel layout.
-/

namespace PILean.Qoi

open PILean.Binary

/-- The QOI magic bytes, ASCII `"qoif"`. -/
private def magic : ByteArray := ByteArray.mk #[0x71, 0x6f, 0x69, 0x66]

/-- `QOI_OP_RGB`: a literal RGB triple, alpha unchanged. -/
private def opRgb : UInt8 := 0xfe

/-- `QOI_OP_RGBA`: a literal RGBA quadruple. -/
private def opRgba : UInt8 := 0xff

/-- The fixed 8-byte end-of-stream marker. -/
private def endMarker : ByteArray := ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 1]

/-- The 64-slot running-array hash: `(r*3 + g*5 + b*7 + a*11) mod 64`
(`mod 64` as `&&& 63`, since 64 is a power of two). -/
@[inline] private def qoiHash (c : Color) : UInt32 :=
  (c.r.toUInt32 * 3 + c.g.toUInt32 * 5 + c.b.toUInt32 * 7 + c.a.toUInt32 * 11) &&& 63

/-- Decode `n` pixels of QOI chunk data into a tightly packed pixel buffer
(`channels` bytes per pixel: 3 = rgb, 4 = rgba). Implements every op
(`QOI_OP_RGB`/`RGBA`/`INDEX`/`DIFF`/`LUMA`/`RUN`) and the 64-entry seen-pixel
table. Every byte read goes through `ParseM.u8`, so running out of input
surfaces as `DecodeError.truncated` — never a panic. -/
private def decodePixels (n channels : Nat) : ParseM ByteArray := do
  let mut data := ByteArray.emptyWithCapacity (n * channels)
  let mut index : Array Color := Array.replicate 64 ⟨0, 0, 0, 0⟩
  let mut px : Color := ⟨0, 0, 0, 255⟩
  let mut run : Nat := 0
  for _ in [0:n] do
    if run > 0 then
      run := run - 1
    else
      let b1 ← ParseM.u8
      if b1 == opRgb then
        let r ← ParseM.u8
        let g ← ParseM.u8
        let b ← ParseM.u8
        px := ⟨r, g, b, px.a⟩
      else if b1 == opRgba then
        let r ← ParseM.u8
        let g ← ParseM.u8
        let b ← ParseM.u8
        let a ← ParseM.u8
        px := ⟨r, g, b, a⟩
      else
        match b1 >>> 6 with
        | 0 =>  -- QOI_OP_INDEX: top two bits are 0, so b1 IS the index.
          px := index[b1.toNat]!
        | 1 =>  -- QOI_OP_DIFF
          let dr := (b1 >>> 4) &&& 3
          let dg := (b1 >>> 2) &&& 3
          let db := b1 &&& 3
          px := ⟨px.r + dr - 2, px.g + dg - 2, px.b + db - 2, px.a⟩
        | 2 =>  -- QOI_OP_LUMA
          let b2 ← ParseM.u8
          let vg := (b1 &&& 0x3f) - 32
          let drh := (b2 >>> 4) &&& 0xf
          let dbh := b2 &&& 0xf
          px := ⟨px.r + vg + drh - 8, px.g + vg, px.b + vg + dbh - 8, px.a⟩
        | _ =>  -- QOI_OP_RUN (tag == 3; 0xfe/0xff already handled above)
          run := (b1 &&& 0x3f).toNat
      index := index.set! (qoiHash px).toNat px
    if channels == 3 then
      data := data.push px.r |>.push px.g |>.push px.b
    else
      data := data.push px.r |>.push px.g |>.push px.b |>.push px.a
  return data

/-- Decode a QOI image (to `.rgb` for a 3-channel file or `.rgba` for
4-channel). The colorspace byte (0 = sRGB with linear alpha, 1 = all
channels linear) is preserved verbatim in `Image.info["colorspace"]`.
Malformed or truncated input always yields `DecodeError`, never a panic. -/
def decode (bytes : ByteArray) : Except DecodeError Image :=
  Binary.ParseM.run (data := bytes) do
    ParseM.expectBytes magic "qoi"
    let width ← ParseM.u32be
    let height ← ParseM.u32be
    let channels ← ParseM.u8
    let colorspace ← ParseM.u8
    unless channels == 3 || channels == 4 do
      throw (.unsupported "qoi" s!"{channels}-channel image (only 3 or 4 are valid)")
    unless colorspace == 0 || colorspace == 1 do
      throw (.corrupt (← ParseM.pos) s!"invalid colorspace byte {colorspace}")
    let n := width.toNat * height.toNat
    -- Every op encodes at least one pixel per byte read (QOI_OP_RUN, the
    -- densest, encodes up to 62 pixels per byte); bound the declared pixel
    -- count against the bytes actually on hand so a bogus huge width/height
    -- can't force a large allocation before truncation would otherwise be
    -- caught pixel-by-pixel.
    let remaining ← ParseM.remaining
    let minNeeded := (n + 61) / 62
    if remaining < minNeeded then
      throw (.truncated (← ParseM.pos)
        s!"{n} pixels need at least {minNeeded} bytes of chunk data, only {remaining} remain")
    let data ← decodePixels n channels.toNat
    ParseM.expectBytes endMarker "qoi"
    let mode : Mode := if channels == 3 then .rgb else .rgba
    pure { width := width.toNat, height := height.toNat, mode, data,
           info := [("colorspace", toString colorspace.toNat)] }

/-- Encode `img`'s pixel buffer (already `.rgb` or `.rgba`, `channels` bytes
per pixel) as the QOI chunk stream — the exact inverse of `decodePixels`,
maintaining the same 64-entry seen-pixel table and preferring, in order,
`QOI_OP_RUN`, `QOI_OP_INDEX`, `QOI_OP_DIFF`, `QOI_OP_LUMA`, falling back to
`QOI_OP_RGB`/`QOI_OP_RGBA`. -/
private def encodePixels (img : Image) (channels : Nat) : ByteArray := Id.run do
  let n := img.width * img.height
  let mut out := ByteArray.emptyWithCapacity (n * (channels + 1))
  let mut index : Array Color := Array.replicate 64 ⟨0, 0, 0, 0⟩
  let mut prev : Color := ⟨0, 0, 0, 255⟩
  let mut run : Nat := 0
  for i in [0:n] do
    let off := i * channels
    let c : Color :=
      if channels == 3 then
        ⟨img.data.get! off, img.data.get! (off + 1), img.data.get! (off + 2), 255⟩
      else
        ⟨img.data.get! off, img.data.get! (off + 1), img.data.get! (off + 2),
         img.data.get! (off + 3)⟩
    if c == prev then
      run := run + 1
      if run == 62 || i == n - 1 then
        out := out.push ((0xc0 : UInt8) ||| UInt8.ofNat (run - 1))
        run := 0
    else
      if run > 0 then
        out := out.push ((0xc0 : UInt8) ||| UInt8.ofNat (run - 1))
        run := 0
      let h := (qoiHash c).toNat
      if index[h]! == c then
        out := out.push (UInt8.ofNat h)  -- QOI_OP_INDEX: tag bits are 00.
      else
        index := index.set! h c
        if c.a == prev.a then
          let dr := c.r - prev.r
          let dg := c.g - prev.g
          let db := c.b - prev.b
          let drB := dr + 2
          let dgB := dg + 2
          let dbB := db + 2
          if drB.toNat < 4 && dgB.toNat < 4 && dbB.toNat < 4 then
            out := out.push ((0x40 : UInt8) ||| (drB <<< 4) ||| (dgB <<< 2) ||| dbB)
          else
            let vrg := dr - dg
            let vbg := db - dg
            let vgB := dg + 32
            let vrgB := vrg + 8
            let vbgB := vbg + 8
            if vgB.toNat < 64 && vrgB.toNat < 16 && vbgB.toNat < 16 then
              out := out.push ((0x80 : UInt8) ||| vgB)
              out := out.push ((vrgB <<< 4) ||| vbgB)
            else
              out := out.push opRgb |>.push c.r |>.push c.g |>.push c.b
        else
          out := out.push opRgba |>.push c.r |>.push c.g |>.push c.b |>.push c.a
    prev := c
  return out

/-- Encode as QOI. `.rgb` images encode directly with `channels = 3`; every
other mode is converted to `.rgba` first (`channels = 4`) via `Image.convert`
— QOI has no direct encoding for gray/grayAlpha/palette. The colorspace byte
comes from `Image.info`'s `"colorspace"` key (`"1"` = all-linear; absent or
anything else = `0`, sRGB with linear alpha). Always succeeds. -/
def encode (img : Image) : Except EncodeError ByteArray :=
  let isRgb := img.mode == .rgb
  let channels : UInt8 := if isRgb then 3 else 4
  let img' := if isRgb then img else img.convert .rgba
  let colorspace : UInt8 :=
    if img.info.any (fun kv => kv.1 == "colorspace" && kv.2 == "1") then 1 else 0
  let hdr := ByteArray.empty
    |>.pushAscii "qoif"
    |>.pushU32be (UInt32.ofNat img'.width)
    |>.pushU32be (UInt32.ofNat img'.height)
    |>.push channels
    |>.push colorspace
  .ok (hdr ++ encodePixels img' channels.toNat ++ endMarker)

/-- QOI codec (registered in `PILean.codecs`). -/
def codec : Codec where
  name := "qoi"
  extensions := [".qoi"]
  sniff := fun b =>
    b.size ≥ 4 && b.get! 0 == 113 && b.get! 1 == 111 &&
    b.get! 2 == 105 && b.get! 3 == 102  -- "qoif"
  decode := decode
  encode := encode

end PILean.Qoi
