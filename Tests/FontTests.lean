import Tests.Framework
import Tests.Prng

/-!
# font tests

Bitmap font data, draw.text, textSize. Owned by WP6 — that work package fills in `cases`.
-/

namespace Tests.FontTests

open PILean

/-- The `font` suite (WP6). -/
def suite : Tests.Suite := { name := "font" }

end Tests.FontTests
