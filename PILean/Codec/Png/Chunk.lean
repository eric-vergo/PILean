import PILean.Core.Error
import PILean.Binary.Reader
import PILean.Binary.Writer
import PILean.Compress.Checksum

/-!
# PNG chunk layer

Signature check, chunk framing, and per-chunk CRC-32 (WP11). Multiple IDAT
chunks are the norm — the decoder concatenates their payloads before
inflating.
-/

namespace PILean.Png

open PILean.Binary
open PILean.Compress (crc32)

/-- The 8-byte PNG file signature. -/
def signature : ByteArray := ⟨#[137, 80, 78, 71, 13, 10, 26, 10]⟩

/-- One PNG chunk: 4-character type + payload. -/
structure Chunk where
  typ : String
  data : ByteArray
  deriving Inhabited

/-- Decode 4 raw bytes as an ASCII chunk-type string. Chunk types are
always 4 ASCII letters in valid PNG; on malformed input this may produce
non-letter codepoints, which is harmless — the result is only ever
compared against fixed ASCII literals like `"IHDR"`/`"IEND"`. Codepoints
0–255 are always valid `Char`s, so this never panics. -/
private def asciiOfBytes (b : ByteArray) : String := Id.run do
  let mut s := ""
  for i in [0:b.size] do
    s := s.push (Char.ofNat (b.get! i).toNat)
  return s

/-- Parse one length-prefixed, CRC-checked chunk at the current cursor. -/
private def readOneChunk : ParseM Chunk := do
  let len ← ParseM.u32be
  let typBytes ← ParseM.take 4
  let payload ← ParseM.take len.toNat
  let crc ← ParseM.u32be
  let body := typBytes ++ payload
  let computed := crc32 body
  unless computed == crc do
    throw (.corrupt (← ParseM.pos) s!"chunk CRC mismatch (type {asciiOfBytes typBytes})")
  return { typ := asciiOfBytes typBytes, data := payload }

/-- Parse all chunks, verifying the signature and each chunk's CRC-32.
Stops right after `IEND`; any bytes following it are rejected as trailing
garbage. Running out of input before `IEND` is `truncated`; a bad signature
or a chunk CRC mismatch is `badMagic`/`corrupt` respectively. -/
def readChunks (bytes : ByteArray) : Except DecodeError (Array Chunk) :=
  ParseM.run (data := bytes) do
    ParseM.expectBytes signature "png"
    let mut chunks : Array Chunk := #[]
    repeat
      if (← ParseM.isEof) then
        throw (.truncated (← ParseM.pos) "missing IEND chunk")
      let c ← readOneChunk
      chunks := chunks.push c
      if c.typ == "IEND" then break
    unless (← ParseM.isEof) do
      throw (.corrupt (← ParseM.pos) "trailing garbage after IEND")
    return chunks

/-- Append one chunk (length + type + payload + CRC-32) to `out`. `typ`
must be exactly 4 ASCII characters (PNG chunk types always are). -/
def appendChunk (out : ByteArray) (typ : String) (payload : ByteArray) : ByteArray :=
  let body := typ.toUTF8 ++ payload
  (out.pushU32be (UInt32.ofNat payload.size) ++ body).pushU32be (crc32 body)

end PILean.Png
