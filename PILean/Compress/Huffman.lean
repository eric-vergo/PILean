import PILean.Compress.BitStream

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# Canonical Huffman coding

Shared by DEFLATE (encode + decode). Codes are canonical per RFC 1951
§3.2.2: shorter codes first, ties broken by symbol order.

Implementation notes for WP3: the v1 decoder is the puff.c-style
count/offset arithmetic decode implemented from the RFC text (simple,
obviously correct); a table-driven fast path can replace it behind the same
interface later. `buildDecoder` must reject over-subscribed code sets
(Kraft sum > 1). The encoder length-limiter uses package-merge, which
guarantees valid ≤ maxLen codes with no overflow fixup.
-/

namespace PILean.Compress.Huffman

/-- Canonical code values for the given code lengths (RFC 1951 §3.2.2).
`lengths[sym] = 0` means the symbol is unused. Fails on over-subscribed
lengths. -/
def canonicalCodes (lengths : Array UInt8) : Except DecodeError (Array UInt16) :=
  .error (.unsupported "huffman" "canonicalCodes not implemented yet (WP3)")

/-- A prepared Huffman decoder. Internals are owned by WP3 and may change;
only `buildDecoder`/`decodeSym` are frozen. -/
structure Decoder where
  counts : Array UInt16 := #[]
  symbols : Array UInt16 := #[]
  deriving Inhabited

/-- Build a decoder from code lengths. Rejects over-subscribed code sets;
incomplete sets are allowed (needed by DEFLATE's single-distance-code
edge case). -/
def buildDecoder (lengths : Array UInt8) : Except DecodeError Decoder :=
  .error (.unsupported "huffman" "buildDecoder not implemented yet (WP3)")

/-- Decode one symbol from the bit stream. -/
def Decoder.decodeSym (d : Decoder) (r : BitReader) : Except DecodeError (UInt16 × BitReader) :=
  .error (.unsupported "huffman" "decodeSym not implemented yet (WP3)")

/-- Length-limited code lengths for the given symbol frequencies
(package-merge). Symbols with zero frequency get length 0. Total: always
returns a valid ≤ `maxLen` code set for the nonzero symbols. -/
def lengthLimitedLengths (freqs : Array Nat) (maxLen : Nat) : Array UInt8 :=
  panic! "PILean.Compress.Huffman.lengthLimitedLengths: not implemented yet (WP3)"

end PILean.Compress.Huffman
