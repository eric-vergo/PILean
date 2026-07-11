import Tests.Framework
import Tests.Prng

/-!
# netpbm tests

PPM/PGM/PBM encode + decode, golden files, comments, ASCII variants. Owned by WP4 — that work package fills in `cases`.
-/

namespace Tests.NetpbmTests

open PILean

/-- The `netpbm` suite (WP4). -/
def suite : Tests.Suite := { name := "netpbm" }

end Tests.NetpbmTests
