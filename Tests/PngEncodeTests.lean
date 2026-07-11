import Tests.Framework
import Tests.Prng

/-!
# png-encode tests

PNG chunks, scanline filters, encode goldens. Owned by WP11 — that work package fills in `cases`.
-/

namespace Tests.PngEncodeTests

open PILean

/-- The `png-encode` suite (WP11). -/
def suite : Tests.Suite := { name := "png-encode" }

end Tests.PngEncodeTests
