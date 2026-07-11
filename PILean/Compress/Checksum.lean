import PILean.Core.Error

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# Checksums

CRC-32 (PNG, GIF) and Adler-32 (zlib). Both take a running value so
checksums chain across buffers: `crc32 b (crc32 a) = crc32 (a ++ b)`.

Implementation notes for WP2: CRC-32 uses polynomial `0xEDB88320`,
table-driven — compute the 256-entry table in a plain top-level `def` (do
not embed it as a literal). Adler-32 is mod 65521 with the standard
NMAX = 5552 batching before reduction.
-/

namespace PILean.Compress

/-- CRC-32 (polynomial `0xEDB88320`, as used by PNG and zlib's gzip). Pass
the previous return value as `crc` to continue across buffers; the default
starts a fresh checksum. -/
def crc32 (data : ByteArray) (crc : UInt32 := 0) : UInt32 :=
  panic! "PILean.Compress.crc32: not implemented yet (WP2)"

/-- Adler-32 (RFC 1950). Pass the previous return value as `adler` to
continue across buffers; the default starts a fresh checksum. -/
def adler32 (data : ByteArray) (adler : UInt32 := 1) : UInt32 :=
  panic! "PILean.Compress.adler32: not implemented yet (WP2)"

end PILean.Compress
