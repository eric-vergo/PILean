import Tests.Framework
import Tests.Prng

/-!
# gif tests

GIF decode (disposal, interlace) and animated encode. Owned by WP15/16 — that work package fills in `cases`.
-/

namespace Tests.GifTests

open PILean

/-- The `gif` suite (WP15/16). -/
def suite : Tests.Suite := { name := "gif" }

end Tests.GifTests
