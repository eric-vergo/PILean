import Tests.Framework
import Tests.Prng

/-!
# binary tests

Extra Binary reader/writer coverage beyond the scaffold suite. Owned by WP2 — that work package fills in `cases`.
-/

namespace Tests.BinaryTests

open PILean

/-- The `binary` suite (WP2). -/
def suite : Tests.Suite := { name := "binary" }

end Tests.BinaryTests
