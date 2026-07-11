import Tests.Framework
import Tests.Prng

/-!
# io tests

Sniffing dispatch, extension fallback, load/save. Owned by WP13 — that work package fills in `cases`.
-/

namespace Tests.IOTests

open PILean

/-- The `io` suite (WP13). -/
def suite : Tests.Suite := { name := "io" }

end Tests.IOTests
