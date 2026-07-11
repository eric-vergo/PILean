import Tests.Framework
import Tests.Prng

/-!
# deflate tests

DEFLATE staged output, in-Lean inflate round trip. Owned by WP10 — that work package fills in `cases`.
-/

namespace Tests.DeflateTests

open PILean

/-- The `deflate` suite (WP10). -/
def suite : Tests.Suite := { name := "deflate" }

end Tests.DeflateTests
