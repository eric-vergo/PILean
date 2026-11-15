/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Png.Types
import PILean.Png.Deflate

/-!
# The PNG writer

`encode` turns a `RawImage` (8-bit grey, RGB or RGBA) and `Metadata` into the bytes of a PNG
file.

## Main definitions

* `encode`: the PNG file for an image, a metadata record, a compression level and a filter
  policy.
* `pngSignature`, `chunk`: the file signature and one chunk with its CRC.
* `validKeyword`: the keyword rule of the specification.
* `paeth`, `filterRow`: the filters of the specification.

## Implementation notes

* Chunks, in order: `IHDR`, `sRGB`, `gAMA`, the text chunks, `IDAT` (the zlib stream split into
  pieces of `idatChunkSize` bytes), `IEND`. Colour types are 0, 2 and 6 at bit depth 8; there
  is no interlacing.
* Filters: every row is filtered with the filter (types 0 to 4) that gives the smallest sum of
  absolute values of the filtered bytes taken as signed 8-bit numbers, the heuristic the
  specification recommends; ties go to the lower filter type. A fixed filter type can be chosen
  instead. The first row's "previous row" is all zeros.
* The output is a function of the arguments alone, so the same image always gives the same
  bytes.
* Text keywords are checked as the specification demands (1 to 79 printable Latin-1 characters,
  no leading, trailing or repeated spaces); `tEXt` text must be Latin-1 and free of NUL;
  `iTXt` entries are written uncompressed.

## References

* PNG Specification, Third Edition (W3C), sections "Chunk specifications", "Filtering" and
  "Textual information". Written from the specification.
-/

namespace PILean.Png

/-- The eight bytes that start every PNG file. -/
def pngSignature : ByteArray := ⟨#[137, 80, 78, 71, 13, 10, 26, 10]⟩

/-- A 32-bit number in big-endian byte order. -/
def be32 (v : UInt32) : ByteArray :=
  ⟨#[(v >>> 24).toUInt8, (v >>> 16).toUInt8, (v >>> 8).toUInt8, v.toUInt8]⟩

/-- The bytes of a chunk: length, four-character type, data and the CRC of type and data. -/
def chunk (ty : String) (data : ByteArray) : ByteArray :=
  let t := ty.toUTF8
  let crc := crcUpdate (crcUpdate 0xFFFFFFFF t) data ^^^ 0xFFFFFFFF
  be32 data.size.toUInt32 ++ t ++ data ++ be32 crc

/-- The size of the data of each `IDAT` chunk the writer produces (the last may be shorter). -/
def idatChunkSize : Nat := 65536

/-- Whether `k` is a valid keyword of a text chunk: 1 to 79 characters in the printable Latin-1
ranges `U+0020 … U+007E` and `U+00A1 … U+00FF`, no leading, trailing or consecutive spaces. -/
def validKeyword (k : String) : Bool :=
  let cs := k.toList
  decide (1 ≤ cs.length) && decide (cs.length ≤ 79) &&
    cs.all (fun c => (32 ≤ c.toNat && c.toNat ≤ 126) || (161 ≤ c.toNat && c.toNat ≤ 255)) &&
    cs.head? != some ' ' && cs.getLast? != some ' ' &&
    (cs.zip (cs.drop 1)).all fun (a, b) => !(a == ' ' && b == ' ')

/-- The Latin-1 bytes of a string, or none if a character is above `U+00FF`. -/
def latin1? (s : String) : Option ByteArray :=
  if s.toList.all (·.toNat < 256) then some ⟨(s.toList.map fun c => c.toNat.toUInt8).toArray⟩
  else none

/-- The paeth predictor of the specification, for the left, above and upper-left samples. -/
def paeth (a b c : Nat) : Nat :=
  let pa := ((b : Int) - c).natAbs
  let pb := ((a : Int) - c).natAbs
  let pc := ((a : Int) + b - 2 * c).natAbs
  if pa ≤ pb && pa ≤ pc then a else if pb ≤ pc then b else c

/-- The byte `i` of `cur` after filter `ty` (0 none, 1 sub, 2 up, 3 average, 4 paeth) with
`prev` the previous unfiltered row (empty for none) and `bpp` bytes per pixel. -/
@[inline] def filterByte (ty : Nat) (cur prev : ByteArray) (bpp i : Nat) : UInt8 :=
  let x := byteAt cur i
  let a := if i ≥ bpp then (byteAt cur (i - bpp)).toNat else 0
  let b := (byteAt prev i).toNat
  let c := if i ≥ bpp then (byteAt prev (i - bpp)).toNat else 0
  match ty with
  | 0 => x
  | 1 => x - a.toUInt8
  | 2 => x - b.toUInt8
  | 3 => x - ((a + b) / 2).toUInt8
  | _ => x - (paeth a b c).toUInt8

/-- The filtered row (without the type byte). -/
def filterRow (ty : Nat) (cur prev : ByteArray) (bpp : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:cur.size] do
    out := out.push (filterByte ty cur prev bpp i)
  return out

/-- The sum of the filtered bytes read as signed numbers, in absolute value. -/
def filterCost (ty : Nat) (cur prev : ByteArray) (bpp : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:cur.size] do
    let v := (filterByte ty cur prev bpp i).toNat
    s := s + (if v < 128 then v else 256 - v)
  return s

/-- The filter type with the smallest cost (the lowest on ties). -/
def bestFilter (cur prev : ByteArray) (bpp : Nat) : Nat := Id.run do
  let mut best := 0
  let mut bestCost := filterCost 0 cur prev bpp
  for t in [1:5] do
    let c := filterCost t cur prev bpp
    if c < bestCost then
      best := t
      bestCost := c
  return best

/-- The image data with a filter-type byte before every row. -/
def filterImage (img : RawImage) (filter : Option Nat) : ByteArray := Id.run do
  let bpp := img.mode.channels
  let rb := img.width * bpp
  let mut out := ByteArray.empty
  let mut prev := ByteArray.empty
  for y in [0:img.height] do
    let cur := img.data.extract (y * rb) ((y + 1) * rb)
    let ty := match filter with
      | some t => t
      | none => bestFilter cur prev bpp
    out := out.push ty.toUInt8
    out := out ++ filterRow ty cur prev bpp
    prev := cur
  return out

/-- The bytes of the text chunk of an entry, or an error naming the problem. -/
def textChunk (e : TextEntry) : Except PngError ByteArray := do
  let some kw := latin1? e.keyword | throw (.invalidInput "text keyword is not Latin-1")
  if !validKeyword e.keyword then throw (.invalidInput s!"invalid text keyword {e.keyword.quote}")
  if !e.international then
    let some t := latin1? e.text | throw (.invalidInput "tEXt text is not Latin-1")
    if t.data.contains 0 then throw (.invalidInput "tEXt text contains NUL")
    return chunk "tEXt" (kw.push 0 ++ t)
  else
    if !(e.language.toList.all fun c => c.isAlphanum || c == '-') || e.language.length > 79 then
      throw (.invalidInput "invalid language tag")
    if e.translatedKeyword.toList.contains (Char.ofNat 0) then
      throw (.invalidInput "translated keyword contains NUL")
    let body := ((((kw.push 0).push 0).push 0) ++ e.language.toUTF8).push 0 ++
      e.translatedKeyword.toUTF8 |>.push 0 |> (· ++ e.text.toUTF8)
    return chunk "iTXt" body

/-- The PNG file for `img`. `level` is the compression level of `zlibCompress` (0 stored, 1 to 9
LZ77 and Huffman coding), `filter` fixes one filter type (0 to 4) for all rows instead of the
per-row choice. Fails with `PngError.invalidInput` if the size or the sample count is wrong,
the dimensions are 0 or exceed `2 ^ 31 - 1`, the sRGB intent is above 3, or a text entry is
invalid. -/
def encode (img : RawImage) (md : Metadata := {}) (level : Nat := 6)
    (filter : Option Nat := none) : Except PngError ByteArray := do
  if img.width == 0 || img.height == 0 then throw (.invalidInput "empty image")
  if img.width > 0x7FFFFFFF || img.height > 0x7FFFFFFF then
    throw (.invalidInput "dimensions exceed 2^31-1")
  if img.data.size != img.width * img.height * img.mode.channels then
    throw (.invalidInput "sample count does not match width, height and mode")
  if let some t := filter then
    if t > 4 then throw (.invalidInput "filter type above 4")
  if let some i := md.srgbIntent then
    if i > 3 then throw (.invalidInput "sRGB intent above 3")
  let colorType : UInt8 := match img.mode with | .l => 0 | .rgb => 2 | .rgba => 6
  let ihdr := be32 img.width.toUInt32 ++ be32 img.height.toUInt32 ++
    ⟨#[8, colorType, 0, 0, 0]⟩
  let mut out := pngSignature ++ chunk "IHDR" ihdr
  if let some i := md.srgbIntent then out := out ++ chunk "sRGB" ⟨#[i]⟩
  if let some g := md.gamma then out := out ++ chunk "gAMA" (be32 g)
  for e in md.text do
    out := out ++ (← textChunk e)
  let z := zlibCompress (filterImage img filter) level
  let mut pos := 0
  for _ in [0:z.size / idatChunkSize + 1] do
    if pos ≥ z.size then break
    let e := min z.size (pos + idatChunkSize)
    out := out ++ chunk "IDAT" (z.extract pos e)
    pos := e
  return out ++ chunk "IEND" ByteArray.empty

end PILean.Png
