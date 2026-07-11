import PILean.Binary.Writer
import PILean.Compress.Checksum
import PILean.Compress.Inflate
import PILean.Compress.Deflate

/-!
# zlib framing (RFC 1950)

CMF/FLG header + raw DEFLATE + Adler-32 trailer. `compress` writes the
conventional `0x78 0x9C` header. `decompress` (WP9) verifies the header
checksum, rejects FDICT, and verifies the Adler-32 trailer.
-/

namespace PILean.Compress.Zlib

set_option linter.unusedVariables false in
/-- Decompress a zlib (RFC 1950) stream, verifying the Adler-32 trailer. -/
def decompress (data : ByteArray) : Except DecodeError ByteArray :=
  .error (.unsupported "zlib" "decompress not implemented yet (WP9)")

/-- Compress into a zlib (RFC 1950) stream (header `0x78 0x9C`, raw
DEFLATE body, big-endian Adler-32 trailer). -/
def compress (data : ByteArray) (level : Nat := 6) : ByteArray :=
  let out := ((ByteArray.emptyWithCapacity (data.size + 16)).push 0x78).push 0x9C
  (out ++ deflate data level).pushU32be (adler32 data)

end PILean.Compress.Zlib
