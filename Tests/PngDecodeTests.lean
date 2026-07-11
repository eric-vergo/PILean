import Tests.Framework
import Tests.Prng

/-!
# png-decode tests

PNG decode incl. PngSuite corpus and corrupt-file errors. Owned by WP12 — that work package fills in `cases`.
-/

namespace Tests.PngDecodeTests

open PILean

/-- The `png-decode` suite (WP12). -/
def suite : Tests.Suite := { name := "png-decode" }

end Tests.PngDecodeTests
