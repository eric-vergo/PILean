import Tests.Framework
import Tests.Prng

/-!
# resize tests

Bicubic/Lanczos resize, affine transforms. Owned by WP20 — that work package fills in `cases`.
-/

namespace Tests.ResizeTests

open PILean

/-- The `resize` suite (WP20). -/
def suite : Tests.Suite := { name := "resize" }

end Tests.ResizeTests
