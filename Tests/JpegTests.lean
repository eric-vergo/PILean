import Tests.Framework
import Tests.Prng

/-!
# jpeg tests

JPEG baseline decode/encode within fixed tolerances. Owned by WP17/18 — that work package fills in `cases`.
-/

namespace Tests.JpegTests

open PILean

/-- The `jpeg` suite (WP17/18). -/
def suite : Tests.Suite := { name := "jpeg" }

end Tests.JpegTests
