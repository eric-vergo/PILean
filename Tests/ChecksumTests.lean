import Tests.Framework
import Tests.Prng

/-!
# checksum tests

CRC-32 and Adler-32 (known vectors, chaining, BitReader/BitWriter). Owned by WP2 — that work package fills in `cases`.
-/

namespace Tests.ChecksumTests

open PILean

/-- The `checksum` suite (WP2). -/
def suite : Tests.Suite := { name := "checksum" }

end Tests.ChecksumTests
