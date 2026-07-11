import Tests.Framework
import Tests.Prng

/-!
# bmp tests

BMP encode + decode, row padding, top-down and bottom-up. Owned by WP4 — that work package fills in `cases`.
-/

namespace Tests.BmpTests

open PILean

/-- The `bmp` suite (WP4). -/
def suite : Tests.Suite := { name := "bmp" }

end Tests.BmpTests
