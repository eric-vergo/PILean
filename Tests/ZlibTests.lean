import Tests.Framework
import Tests.Prng

/-!
# zlib tests

zlib framing, Adler verification. Owned by WP10 — that work package fills in `cases`.
-/

namespace Tests.ZlibTests

open PILean

/-- The `zlib` suite (WP10). -/
def suite : Tests.Suite := { name := "zlib" }

end Tests.ZlibTests
