import Tests.Framework
import Tests.Prng

/-!
# lzw tests

LZW quirk vectors: KwKwK, deferred clear, width growth, earlyChange. Owned by WP14 — that work package fills in `cases`.
-/

namespace Tests.LzwTests

open PILean

/-- The `lzw` suite (WP14). -/
def suite : Tests.Suite := { name := "lzw" }

end Tests.LzwTests
