import Tests.Framework
import Tests.Prng

/-!
# filter tests

Point operations: invert, brightness, contrast, threshold. Owned by WP7 — that work package fills in `cases`.
-/

namespace Tests.FilterTests

open PILean

/-- The `filter` suite (WP7). -/
def suite : Tests.Suite := { name := "filter" }

end Tests.FilterTests
