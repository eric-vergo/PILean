/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Png.Inflate

/-!
# PNG data types

The raw image, metadata and error types shared by the PNG writer (`PILean.Png.encode`) and the
PNG reader (`PILean.Png.decode`).

## Main definitions

* `Mode`: the sample layout of a raw image: grey (`l`), `rgb` or `rgba`, 8 bits per sample.
* `RawImage`: width, height, mode and the row-major samples.
* `TextEntry`: a `tEXt`, `zTXt` or `iTXt` entry (keyword and text).
* `Metadata`: what the writer records besides the pixels (sRGB intent, gamma, text).
* `Limits`: the caps the reader enforces before it allocates.
* `PngError`: why writing or reading failed.

## References

* PNG Specification, Third Edition (W3C), also ISO/IEC 15948. Written from the specification.
-/

namespace PILean.Png

/-- The sample layout of a raw image, 8 bits per sample. -/
inductive Mode where
  /-- One grey sample per pixel (PNG colour type 0). -/
  | l
  /-- Red, green, blue (colour type 2). -/
  | rgb
  /-- Red, green, blue, alpha (colour type 6). -/
  | rgba
deriving BEq, Repr, Inhabited, DecidableEq

/-- The number of samples per pixel. -/
def Mode.channels : Mode → Nat
  | .l => 1
  | .rgb => 3
  | .rgba => 4

/-- A raw image: `data` holds `width * height * mode.channels` samples, row by row, left to
right, the channels of a pixel next to each other. -/
structure RawImage where
  /-- Width in pixels. -/
  width : Nat
  /-- Height in pixels. -/
  height : Nat
  /-- The sample layout. -/
  mode : Mode
  /-- The samples. -/
  data : ByteArray

/-- A textual metadata entry. For `tEXt` and `zTXt` (`international = false`) the keyword and
text are Latin-1; for `iTXt` they are Unicode (UTF-8 in the file) and `language` is an RFC 5646
language tag (possibly empty) and `translatedKeyword` an optional translation of the keyword. -/
structure TextEntry where
  /-- The keyword: 1 to 79 printable Latin-1 characters, no leading, trailing or repeated
  spaces. -/
  keyword : String
  /-- The text. -/
  text : String
  /-- Whether the entry is an `iTXt` entry. -/
  international : Bool := false
  /-- The language tag of an `iTXt` entry. -/
  language : String := ""
  /-- The translated keyword of an `iTXt` entry. -/
  translatedKeyword : String := ""
deriving BEq, Repr, Inhabited

/-- What the writer records besides the pixels. -/
structure Metadata where
  /-- The `sRGB` rendering intent (0 perceptual, 1 relative colorimetric, 2 saturation,
  3 absolute colorimetric), or none to omit the chunk. -/
  srgbIntent : Option UInt8 := some 0
  /-- The `gAMA` value (gamma times 100000), or none to omit the chunk; 45455 is the value the
  specification recommends alongside `sRGB`. -/
  gamma : Option UInt32 := some 45455
  /-- Text entries, written as `tEXt` chunks (or `iTXt` when `international`), before the
  image data. -/
  text : Array TextEntry := #[]
deriving Repr, Inhabited

/-- The caps the reader applies to untrusted input before it allocates. -/
structure Limits where
  /-- The largest accepted `width * height`. -/
  maxPixels : Nat := 1 <<< 26
  /-- The largest accepted size of the decompressed image data (with filter bytes) and of the
  decoded samples. -/
  maxBytes : Nat := 1 <<< 29
  /-- The total size of decompressed text the reader accepts. -/
  maxTextBytes : Nat := 1 <<< 22
deriving Repr, Inhabited

/-- Why writing or reading a PNG failed. -/
inductive PngError where
  /-- The input does not start with the PNG signature. -/
  | badSignature
  /-- The input ends inside a chunk, or a required chunk is missing. -/
  | truncated
  /-- A chunk length exceeds `2 ^ 31 - 1`. -/
  | badChunkLength
  /-- The CRC of the named chunk is wrong. -/
  | badCrc (chunk : String)
  /-- The `IHDR` chunk is invalid. -/
  | badHeader (msg : String)
  /-- Chunks are in an invalid order, repeated, or have an invalid layout. -/
  | badChunkOrder (msg : String)
  /-- An unknown chunk whose type marks it as critical. -/
  | unknownCriticalChunk (chunk : String)
  /-- The image is larger than the caller's `Limits`. -/
  | tooLarge (msg : String)
  /-- The decompressed image data is invalid (size, filter type, palette index). -/
  | badImageData (msg : String)
  /-- The zlib stream of the image data is invalid. -/
  | inflate (e : InflateError)
  /-- A feature the reader does not provide. -/
  | unsupported (msg : String)
  /-- The writer was given an invalid image or metadata. -/
  | invalidInput (msg : String)
deriving Repr, BEq, Inhabited

/-- A short description of the error. -/
def PngError.toString : PngError → String
  | .badSignature => "not a PNG file (bad signature)"
  | .truncated => "PNG data is truncated"
  | .badChunkLength => "PNG chunk length exceeds 2^31-1"
  | .badCrc c => s!"CRC mismatch in chunk {c}"
  | .badHeader m => s!"invalid IHDR: {m}"
  | .badChunkOrder m => s!"invalid chunk structure: {m}"
  | .unknownCriticalChunk c => s!"unknown critical chunk {c}"
  | .tooLarge m => s!"image too large: {m}"
  | .badImageData m => s!"invalid image data: {m}"
  | .inflate e => s!"invalid compressed image data: {e}"
  | .unsupported m => s!"unsupported: {m}"
  | .invalidInput m => s!"invalid input: {m}"

instance : ToString PngError := ⟨PngError.toString⟩

end PILean.Png
