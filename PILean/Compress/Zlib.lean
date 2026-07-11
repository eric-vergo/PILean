import PILean.Compress.Checksum
import PILean.Compress.Inflate
import PILean.Compress.Deflate

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# zlib framing (RFC 1950)

CMF/FLG header + raw DEFLATE + Adler-32 trailer. `compress` writes header
`0x78 0x9C`. `decompress` verifies the header checksum, rejects FDICT, and
verifies the Adler-32 trailer.
-/

namespace PILean.Compress.Zlib

/-- Decompress a zlib (RFC 1950) stream, verifying the Adler-32 trailer. -/
def decompress (data : ByteArray) : Except DecodeError ByteArray :=
  .error (.unsupported "zlib" "decompress not implemented yet (WP10)")

/-- Compress into a zlib (RFC 1950) stream. -/
def compress (data : ByteArray) (level : Nat := 6) : ByteArray :=
  panic! "PILean.Compress.Zlib.compress: not implemented yet (WP10)"

end PILean.Compress.Zlib
