import Tests.Framework
import Tests.Prng

/-!
# tiff tests

Baseline TIFF, LZW earlyChange, both byte orders. Owned by WP21 — that work package fills in `cases`.
-/

namespace Tests.TiffTests

open PILean

/-- The `tiff` suite (WP21). -/
def suite : Tests.Suite := { name := "tiff" }

end Tests.TiffTests
