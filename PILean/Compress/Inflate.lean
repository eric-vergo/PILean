import PILean.Compress.BitStream
import PILean.Compress.Huffman

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# INFLATE — raw DEFLATE decoding (RFC 1951)

Implementation notes for WP9: stored (LEN/NLEN check), fixed (hardcoded
tables: litlen 0–143→8, 144–255→9, 256–279→7, 280–287→8; dist all 5), and
dynamic blocks (HLIT/HDIST/HCLEN; code-length alphabet in permuted order
16 17 18 0 8 7 9 6 10 5 11 4 12 3 13 2 14 1 15; repeat codes 16/17/18,
where repeat-16 may not appear before any length). Back-references copy
from the output buffer itself; overlapping copies (dist < len) must go
byte-by-byte. Reject litlen symbols 286/287 and distances 30/31. Must
return `Error` — never panic or hang — on any malformed or truncated
input (fuzzed in tests).
-/

namespace PILean.Compress

/-- Decode a raw DEFLATE (RFC 1951) stream. `sizeHint` preallocates the
output buffer when the caller knows the decompressed size (e.g. PNG). -/
def inflate (compressed : ByteArray) (sizeHint : Nat := 0) : Except DecodeError ByteArray :=
  .error (.unsupported "deflate" "inflate not implemented yet (WP9)")

end PILean.Compress
