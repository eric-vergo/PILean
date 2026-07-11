import PILean.Core.Error
import PILean.Binary.Reader
import PILean.Binary.Writer
import PILean.Compress.Checksum

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# PNG chunk layer

Signature check, chunk framing, and per-chunk CRC-32 (WP11). Multiple IDAT
chunks are the norm — the decoder concatenates their payloads before
inflating.
-/

namespace PILean.Png

/-- The 8-byte PNG file signature. -/
def signature : ByteArray := ⟨#[137, 80, 78, 71, 13, 10, 26, 10]⟩

/-- One PNG chunk: 4-character type + payload. -/
structure Chunk where
  typ : String
  data : ByteArray

/-- Parse all chunks, verifying the signature and each chunk's CRC-32. -/
def readChunks (bytes : ByteArray) : Except DecodeError (Array Chunk) :=
  .error (.unsupported "png" "chunk reader not implemented yet (WP11)")

/-- Append one chunk (length + type + payload + CRC-32) to `out`. -/
def appendChunk (out : ByteArray) (typ : String) (payload : ByteArray) : ByteArray :=
  panic! "PILean.Png.appendChunk: not implemented yet (WP11)"

end PILean.Png
