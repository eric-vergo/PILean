set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# LZ77 matching

Greedy hash-chain matcher for DEFLATE. Independent of the bit/Huffman
layers so it is testable in isolation: `detokenize (tokenize d) = d`, and
every emitted match must actually match the source.

Token packing (frozen): a literal byte `b` is the `UInt32` value `b`;
a match of length `len` (3–258) at distance `dist` (1–32768) is
`0x80000000 ||| (len <<< 16) ||| dist`.

Implementation notes for WP3: 3-byte hash into `head : Array Int32`
(2^15 buckets) + `prev : Array Int32` ring; chain-probe cap scales with
`level` (1 → ~8 probes, 6 → ~128, 9 → ~1024).
-/

namespace PILean.Compress.LZ77

/-- Tokenize `data` into literals and back-references (see module docstring
for the packed `UInt32` token format). Higher `level` = more probes =
better matches, slower. -/
def tokenize (data : ByteArray) (level : Nat := 6) : Array UInt32 :=
  panic! "PILean.Compress.LZ77.tokenize: not implemented yet (WP3)"

/-- Reconstruct the original bytes from tokens. For testing `tokenize`
(round-trip and match-validity checks); not used by the encoder proper. -/
def detokenize (tokens : Array UInt32) : ByteArray :=
  panic! "PILean.Compress.LZ77.detokenize: not implemented yet (WP3)"

end PILean.Compress.LZ77
