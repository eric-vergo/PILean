import Tests.Framework
import Tests.Prng

/-!
# huffman tests

Canonical Huffman codes, decoder, package-merge, LZ77 round trip. Owned by WP3 — that work package fills in `cases`.
-/

namespace Tests.HuffmanTests

open PILean

/-- The `huffman` suite (WP3). -/
def suite : Tests.Suite := { name := "huffman" }

end Tests.HuffmanTests
