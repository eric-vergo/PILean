import Tests.Framework
import Tests.Prng

/-!
# draw tests

Drawing primitives incl. clipping at every edge. Owned by WP5 — that work package fills in `cases`.
-/

namespace Tests.DrawTests

open PILean

/-- The `draw` suite (WP5). -/
def suite : Tests.Suite := { name := "draw" }

end Tests.DrawTests
