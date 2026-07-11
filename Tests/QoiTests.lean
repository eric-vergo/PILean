import Tests.Framework
import Tests.Prng

/-!
# qoi tests

QOI encode/decode round trip and goldens. Owned by WP13 — that work package fills in `cases`.
-/

namespace Tests.QoiTests

open PILean

/-- The `qoi` suite (WP13). -/
def suite : Tests.Suite := { name := "qoi" }

end Tests.QoiTests
