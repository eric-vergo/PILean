import Tests.Framework
import Tests.Prng

/-!
# transform tests

Flips, rotations, transpose, nearest/bilinear resize. Owned by WP7 — that work package fills in `cases`.
-/

namespace Tests.TransformTests

open PILean

/-- The `transform` suite (WP7). -/
def suite : Tests.Suite := { name := "transform" }

end Tests.TransformTests
