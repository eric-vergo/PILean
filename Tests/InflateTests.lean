import Tests.Framework
import Tests.Prng

/-!
# inflate tests

INFLATE vs Python-zlib corpus, hostile vectors, truncation fuzz. Owned by WP9 — that work package fills in `cases`.
-/

namespace Tests.InflateTests

open PILean

/-- The `inflate` suite (WP9). -/
def suite : Tests.Suite := { name := "inflate" }

end Tests.InflateTests
