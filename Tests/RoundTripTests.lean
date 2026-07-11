import Tests.Framework
import Tests.Prng

/-!
# roundtrip tests

Cross-format decode-encode-decode properties. Owned by integrator — that work package fills in `cases`.
-/

namespace Tests.RoundTripTests

open PILean

/-- The `roundtrip` suite (integrator). -/
def suite : Tests.Suite := { name := "roundtrip" }

end Tests.RoundTripTests
