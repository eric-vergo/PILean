/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Png.Types
import PILean.Png.Write

/-!
# The PNG reader

`decode` reads the bytes of a PNG file, which it treats as untrusted, into a `RawImage` plus the
text and colour-space chunks it found.

## Main definitions

* `Decoded`: the result of `decode`.
* `decode`: the reader.
* `Header`: the validated `IHDR` fields.

## Implementation notes

* Structure. The signature is checked; every chunk's length must be at most `2 ^ 31 - 1` and
  lie within the file, and its CRC is checked (including unknown chunks). The first chunk must
  be `IHDR`, occurring once. A critical chunk (upper-case first letter) other than `IHDR`,
  `PLTE`, `IDAT` and `IEND` is an error; unknown ancillary chunks are skipped. `IDAT` chunks
  must be consecutive, `PLTE` must precede `IDAT`, at most one of each of `PLTE` and `tRNS`,
  `PLTE` is required for colour type 3 and forbidden for types 0 and 4. `IEND` must be empty;
  bytes after it are ignored. Ancillary chunks `sRGB`, `gAMA` and the text chunks are read
  when they precede the image data; a malformed one is ignored. A `tRNS` chunk of the wrong
  length, or a `tRNS` after `IDAT`, is ignored for colour types 4 and 6 and an error otherwise.
* Caps. Before any image buffer is allocated, `width * height` is checked against
  `Limits.maxPixels` and the sizes of the decompressed data and of the output against
  `Limits.maxBytes`. The decompressor is given the exact expected size as its output cap.
  Compressed text (`zTXt`, compressed `iTXt`) is inflated under a shared budget of
  `Limits.maxTextBytes`; an entry over budget is dropped.
* Formats. All five colour types; bit depths 1, 2, 4, 8 and 16 as the specification allows
  for each; Adam7 interlacing. The result is `l` for colour type 0, `rgb` for 2 and 3, and
  `rgba` for 4 and 6; a `tRNS` chunk turns types 0, 2 and 3 into `rgba` (grey and
  colour-key transparency compare the sample at its own depth). Samples of depth 1, 2 and 4 are
  scaled to 8 bits by `v * 255 / (2 ^ depth - 1)`; 16-bit samples keep their high byte.
* The compressed data must decompress to exactly the size the header implies, and the zlib
  stream must end with nothing after its checksum.

## References

* PNG Specification, Third Edition (W3C), also ISO/IEC 15948. Written from the specification.
-/

namespace PILean.Png

/-- The result of reading a PNG: the image in 8-bit samples, the text entries found, and the
`sRGB` rendering intent and `gAMA` value if present. -/
structure Decoded where
  /-- The image. -/
  image : RawImage
  /-- The text entries, in file order. -/
  text : Array TextEntry
  /-- The `sRGB` rendering intent. -/
  srgbIntent : Option UInt8
  /-- The `gAMA` value (gamma times 100000). -/
  gamma : Option UInt32

/-- The fields of a validated `IHDR`. -/
structure Header where
  /-- Width in pixels. -/
  width : Nat
  /-- Height in pixels. -/
  height : Nat
  /-- Bits per sample: 1, 2, 4, 8 or 16. -/
  depth : Nat
  /-- The colour type: 0, 2, 3, 4 or 6. -/
  colorType : Nat
  /-- Whether the image is Adam7 interlaced. -/
  interlaced : Bool

/-- The number of samples per pixel of a colour type. -/
def Header.channels (h : Header) : Nat :=
  match h.colorType with | 2 => 3 | 4 => 2 | 6 => 4 | _ => 1

/-- Bits per pixel. -/
def Header.bitsPerPixel (h : Header) : Nat := h.channels * h.depth

/-- Bytes per pixel as the filters see them (at least 1). -/
def Header.filterBpp (h : Header) : Nat := max 1 ((h.bitsPerPixel + 7) / 8)

/-- Bytes in a row of `w` pixels. -/
def Header.rowBytes (h : Header) (w : Nat) : Nat := (w * h.bitsPerPixel + 7) / 8

/-- The Adam7 passes as (x start, y start, x step, y step). -/
def adam7 : Array (Nat × Nat × Nat × Nat) :=
  #[(0, 0, 8, 8), (4, 0, 8, 8), (0, 4, 4, 8), (2, 0, 4, 4), (0, 2, 2, 4), (1, 0, 2, 2),
    (0, 1, 1, 2)]

/-- The passes of an image: the single full pass, or the seven Adam7 passes. -/
def Header.passes (h : Header) : Array (Nat × Nat × Nat × Nat) :=
  if h.interlaced then adam7 else #[(0, 0, 1, 1)]

/-- The width and height of a pass. -/
def Header.passDims (h : Header) (p : Nat × Nat × Nat × Nat) : Nat × Nat :=
  let (x0, y0, dx, dy) := p
  ((if h.width > x0 then (h.width - x0 + dx - 1) / dx else 0),
    (if h.height > y0 then (h.height - y0 + dy - 1) / dy else 0))

/-- The size of the unfiltered image data including the filter-type bytes. -/
def Header.rawSize (h : Header) : Nat :=
  h.passes.foldl (fun s p =>
    let (pw, ph) := h.passDims p
    if pw == 0 || ph == 0 then s else s + ph * (1 + h.rowBytes pw)) 0

/-- The sample layout of the output. -/
def outMode (colorType : Nat) (hasTrns : Bool) : Mode :=
  match colorType with
  | 0 => if hasTrns then .rgba else .l
  | 2 | 3 => if hasTrns then .rgba else .rgb
  | _ => .rgba

/-- A big-endian 32-bit number at `i` (zeros beyond the end). -/
def getBe32 (d : ByteArray) (i : Nat) : Nat :=
  ((byteAt d i).toNat <<< 24) ||| ((byteAt d (i + 1)).toNat <<< 16) |||
    ((byteAt d (i + 2)).toNat <<< 8) ||| (byteAt d (i + 3)).toNat

/-- Validates the 13 bytes of an `IHDR` against the caps. -/
def parseHeader (d : ByteArray) (lim : Limits) : Except PngError Header := do
  if d.size != 13 then throw (.badHeader "length is not 13")
  let w := getBe32 d 0
  let ht := getBe32 d 4
  let depth := (byteAt d 8).toNat
  let ct := (byteAt d 9).toNat
  if w == 0 || ht == 0 then throw (.badHeader "zero width or height")
  if w > 0x7FFFFFFF || ht > 0x7FFFFFFF then throw (.badHeader "dimension above 2^31-1")
  let okDepth := match ct with
    | 0 => depth == 1 || depth == 2 || depth == 4 || depth == 8 || depth == 16
    | 2 | 4 | 6 => depth == 8 || depth == 16
    | 3 => depth == 1 || depth == 2 || depth == 4 || depth == 8
    | _ => false
  if !okDepth then throw (.badHeader s!"colour type {ct} with bit depth {depth}")
  if (byteAt d 10) != 0 then throw (.badHeader "unknown compression method")
  if (byteAt d 11) != 0 then throw (.badHeader "unknown filter method")
  let il := (byteAt d 12).toNat
  if il > 1 then throw (.badHeader "unknown interlace method")
  let h : Header := { width := w, height := ht, depth, colorType := ct, interlaced := il == 1 }
  if w * ht > lim.maxPixels then throw (.tooLarge s!"{w} x {ht} pixels")
  if h.rawSize > lim.maxBytes then throw (.tooLarge "decompressed data")
  if w * ht * (outMode ct true).channels > lim.maxBytes then throw (.tooLarge "decoded samples")
  return h

/-- Reverses the filters of one pass: `raw` holds `ph` rows of a filter-type byte and `rb` bytes
from `off`; the result has `ph * rb` bytes. -/
def unfilterPass (raw : ByteArray) (off rb ph bpp : Nat) : Except PngError ByteArray := do
  let mut rows := ByteArray.empty
  let mut prev := ByteArray.empty
  for r in [0:ph] do
    let base := off + r * (rb + 1)
    let ty := (byteAt raw base).toNat
    if ty > 4 then throw (.badImageData s!"filter type {ty}")
    let mut cur := ByteArray.empty
    if ty == 0 then cur := raw.extract (base + 1) (base + 1 + rb)
    else
      for i in [0:rb] do
        let x := byteAt raw (base + 1 + i)
        let a := if i ≥ bpp then (byteAt cur (i - bpp)).toNat else 0
        let b := (byteAt prev i).toNat
        let c := if i ≥ bpp then (byteAt prev (i - bpp)).toNat else 0
        let p := match ty with
          | 1 => a
          | 2 => b
          | 3 => (a + b) / 2
          | _ => paeth a b c
        cur := cur.push (x + p.toUInt8)
    rows := rows ++ cur
    prev := cur
  return rows

/-- The sample `ch` of pixel `px` in a row starting at byte `ro` of `rows`, at its own depth. -/
@[inline] def sampleAt (h : Header) (rows : ByteArray) (ro px ch : Nat) : Nat :=
  match h.depth with
  | 8 => (byteAt rows (ro + px * h.channels + ch)).toNat
  | 16 =>
    let i := ro + (px * h.channels + ch) * 2
    ((byteAt rows i).toNat <<< 8) ||| (byteAt rows (i + 1)).toNat
  | d =>
    let bit := px * d
    let sh := 8 - d - bit % 8
    ((byteAt rows (ro + bit / 8)).toNat >>> sh) &&& ((1 <<< d) - 1)

/-- A sample scaled to 8 bits. -/
@[inline] def to8 (depth v : Nat) : UInt8 :=
  match depth with
  | 8 => v.toUInt8
  | 16 => (v >>> 8).toUInt8
  | d => (v * 255 / ((1 <<< d) - 1)).toUInt8

/-- Stores a byte at an index of the output, ignoring indices out of range. -/
@[inline] def setByte (a : ByteArray) (i : Nat) (v : UInt8) : ByteArray :=
  if h : i < a.size then a.set i v h else a

/-- Writes the pixels of one unfiltered pass into the output image. -/
def emitPass (h : Header) (palette trns rows : ByteArray) (p : Nat × Nat × Nat × Nat)
    (out : ByteArray) : Except PngError ByteArray := do
  let (x0, y0, dx, dy) := p
  let (pw, ph) := h.passDims p
  let hasTrns := !trns.isEmpty
  let oc := (outMode h.colorType hasTrns).channels
  let rb := h.rowBytes pw
  let mask := (1 <<< h.depth) - 1
  let key (k : Nat) := ((byteAt trns (2 * k)).toNat <<< 8 ||| (byteAt trns (2 * k + 1)).toNat) &&&
    mask
  let mut out := out
  for py in [0:ph] do
    let ro := py * rb
    for px in [0:pw] do
      let o := ((y0 + py * dy) * h.width + x0 + px * dx) * oc
      match h.colorType with
      | 0 =>
        let v := sampleAt h rows ro px 0
        let g := to8 h.depth v
        if hasTrns then
          out := setByte (setByte (setByte out o g) (o + 1) g) (o + 2) g
          out := setByte out (o + 3) (if v == key 0 then 0 else 255)
        else out := setByte out o g
      | 2 =>
        let r := sampleAt h rows ro px 0
        let g := sampleAt h rows ro px 1
        let b := sampleAt h rows ro px 2
        out := setByte (setByte (setByte out o (to8 h.depth r)) (o + 1) (to8 h.depth g))
          (o + 2) (to8 h.depth b)
        if hasTrns then
          out := setByte out (o + 3) (if r == key 0 && g == key 1 && b == key 2 then 0 else 255)
      | 3 =>
        let i := sampleAt h rows ro px 0
        if i * 3 + 2 ≥ palette.size then throw (.badImageData "palette index out of range")
        out := setByte (setByte (setByte out o (byteAt palette (i * 3)))
          (o + 1) (byteAt palette (i * 3 + 1))) (o + 2) (byteAt palette (i * 3 + 2))
        if hasTrns then
          out := setByte out (o + 3) (if i < trns.size then byteAt trns i else 255)
      | 4 =>
        let g := to8 h.depth (sampleAt h rows ro px 0)
        out := setByte (setByte (setByte out o g) (o + 1) g) (o + 2) g
        out := setByte out (o + 3) (to8 h.depth (sampleAt h rows ro px 1))
      | _ =>
        for c in [0:4] do
          out := setByte out (o + c) (to8 h.depth (sampleAt h rows ro px c))
  return out

/-- Decodes the unfiltered-and-filtered image data `raw` of the header into the output image. -/
def buildImage (h : Header) (palette trns raw : ByteArray) : Except PngError RawImage := do
  let mode := outMode h.colorType !trns.isEmpty
  let mut off := 0
  let mut out : ByteArray := ByteArray.empty
  let mut allocated := false
  for p in h.passes do
    let (pw, ph) := h.passDims p
    if pw == 0 || ph == 0 then continue
    let rb := h.rowBytes pw
    let rows ← unfilterPass raw off rb ph h.filterBpp
    off := off + ph * (1 + rb)
    -- colour types and depths whose rows already are the output
    if !h.interlaced && h.depth == 8 && trns.isEmpty &&
        (h.colorType == 0 || h.colorType == 2 || h.colorType == 6) then
      return { width := h.width, height := h.height, mode, data := rows }
    if !allocated then
      out := ByteArray.mk (Array.replicate (h.width * h.height * mode.channels) 0)
      allocated := true
    out ← emitPass h palette trns rows p out
  return { width := h.width, height := h.height, mode, data := out }

/-- The text of a Latin-1 byte string. -/
def latin1String (b : ByteArray) : String := String.ofList (b.toList.map fun x => Char.ofNat x.toNat)

/-- The index of the first zero byte at or after `i`, if any. -/
def findNul (d : ByteArray) (i : Nat) : Option Nat := Id.run do
  for j in [i:d.size] do
    if byteAt d j == 0 then return some j
  return none

/-- Reads a `tEXt`, `zTXt` or `iTXt` chunk; `none` for a malformed one or one over the text
budget. Returns the entry and the size it used from the budget. -/
def parseText (ty : String) (d : ByteArray) (budget : Nat) : Option (TextEntry × Nat) := do
  let k ← findNul d 0
  let kw := latin1String (d.extract 0 k)
  guard (validKeyword kw)
  let cap := min (1 <<< 20) budget
  let inflateText (z : ByteArray) : Option ByteArray :=
    match zlibDecompress z cap (allowTrailing := true) with
    | .ok o => some o
    | .error _ => none
  match ty with
  | "tEXt" =>
    let t := d.extract (k + 1) d.size
    guard (t.size ≤ budget)
    return ({ keyword := kw, text := latin1String t }, t.size)
  | "zTXt" =>
    guard (byteAt d (k + 1) == 0)
    let t ← inflateText (d.extract (k + 2) d.size)
    return ({ keyword := kw, text := latin1String t }, t.size)
  | _ =>
    let flag := byteAt d (k + 1)
    guard (k + 2 < d.size && byteAt d (k + 2) == 0 && flag ≤ 1)
    let l ← findNul d (k + 3)
    let tk ← findNul d (l + 1)
    let lang := latin1String (d.extract (k + 3) l)
    let tkw ← String.fromUTF8? (d.extract (l + 1) tk)
    let body := d.extract (tk + 1) d.size
    let raw ← if flag == 1 then inflateText body else if body.size ≤ budget then some body else none
    let t ← String.fromUTF8? raw
    return ({ keyword := kw, text := t, international := true, language := lang,
              translatedKeyword := tkw }, raw.size)

/-- Reads the PNG file `bytes`. Fails with a `PngError` if the file is malformed, uses an
unsupported feature, or is larger than `lim` allows; see the module documentation for the exact
rules. -/
def decode (bytes : ByteArray) (lim : Limits := {}) : Except PngError Decoded := do
  if bytes.size < 8 || bytes.extract 0 8 != pngSignature then throw .badSignature
  let mut pos := 8
  let mut hdr : Option Header := none
  let mut plte : ByteArray := ByteArray.empty
  let mut hasPlte := false
  let mut trns : ByteArray := ByteArray.empty
  let mut idat := ByteArray.empty
  let mut idatState := 0
  let mut sawEnd := false
  let mut text : Array TextEntry := #[]
  let mut budget := lim.maxTextBytes
  let mut srgb : Option UInt8 := none
  let mut gamma : Option UInt32 := none
  for _ in [0:bytes.size / 12 + 1] do
    if pos + 12 > bytes.size then throw .truncated
    let len := getBe32 bytes pos
    if len > 0x7FFFFFFF then throw .badChunkLength
    if pos + 12 + len > bytes.size then throw .truncated
    let tyBytes := bytes.extract (pos + 4) (pos + 8)
    let data := bytes.extract (pos + 8) (pos + 8 + len)
    if !(tyBytes.data.all fun b => (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122)) then
      throw (.badChunkOrder "chunk type is not four letters")
    let ty := latin1String tyBytes
    let crc := crcUpdate (crcUpdate 0xFFFFFFFF tyBytes) data ^^^ 0xFFFFFFFF
    if crc.toNat != getBe32 bytes (pos + 8 + len) then throw (.badCrc ty)
    pos := pos + 12 + len
    if hdr.isNone && ty != "IHDR" then throw (.badChunkOrder "IHDR is not the first chunk")
    if ty != "IDAT" && idatState == 1 then idatState := 2
    let some h := hdr | do hdr := some (← parseHeader data lim); continue
    match ty with
    | "IHDR" => throw (.badChunkOrder "repeated IHDR")
    | "PLTE" =>
      if idatState != 0 || hasPlte then throw (.badChunkOrder "PLTE after IDAT or repeated")
      if h.colorType == 0 || h.colorType == 4 then
        throw (.badChunkOrder "PLTE in a grey image")
      if len == 0 || len % 3 != 0 || len / 3 > 256 ||
          (h.colorType == 3 && len / 3 > (1 <<< h.depth)) then
        throw (.badChunkOrder "invalid PLTE length")
      plte := data
      hasPlte := true
    | "IDAT" =>
      if idatState == 2 then throw (.badChunkOrder "IDAT chunks are not consecutive")
      idatState := 1
      idat := idat ++ data
    | "IEND" =>
      if len != 0 then throw (.badChunkOrder "IEND is not empty")
      if idatState == 0 then throw (.badChunkOrder "no IDAT")
      sawEnd := true
      break
    | "tRNS" =>
      if h.colorType == 4 || h.colorType == 6 || idatState != 0 then pure ()
      else
        if !trns.isEmpty then throw (.badChunkOrder "repeated tRNS")
        let okLen := match h.colorType with
          | 0 => len == 2
          | 2 => len == 6
          | _ => hasPlte && len > 0 && len ≤ plte.size / 3
        if !okLen then throw (.badChunkOrder "invalid tRNS length")
        trns := data
    | "sRGB" =>
      if idatState == 0 && len == 1 && (byteAt data 0) ≤ 3 then srgb := some (byteAt data 0)
    | "gAMA" =>
      if idatState == 0 && len == 4 then gamma := some (getBe32 data 0).toUInt32
    | "tEXt" | "zTXt" | "iTXt" =>
      if let some (e, used) := parseText ty data budget then
        text := text.push e
        budget := budget - min used budget
    | _ =>
      if (byteAt tyBytes 0) &&& 32 == 0 then throw (.unknownCriticalChunk ty)
  let some h := hdr | throw .truncated
  if !sawEnd then throw .truncated
  if h.colorType == 3 && !hasPlte then throw (.badChunkOrder "missing PLTE")
  let raw ← match zlibDecompress idat h.rawSize with
    | .ok o => pure o
    | .error e => throw (.inflate e)
  if raw.size != h.rawSize then throw (.badImageData "too little image data")
  let image ← buildImage h plte trns raw
  return { image, text, srgbIntent := srgb, gamma }

end PILean.Png
