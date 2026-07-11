import Tests.Framework
import Tests.Prng

/-!
# core tests

Image core: map, crop, paste, alphaComposite, convert, palette ops. Owned by WP1 — that work package fills in `cases`.
-/

namespace Tests.CoreTests

open PILean

/-- The `core` suite (WP1). -/
def suite : Tests.Suite := { name := "core" }

end Tests.CoreTests
