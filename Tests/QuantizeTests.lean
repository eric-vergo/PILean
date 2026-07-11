import Tests.Framework
import Tests.Prng

/-!
# quantize tests

Median-cut properties (never compared to Pillow's quantizer). Owned by WP13 — that work package fills in `cases`.
-/

namespace Tests.QuantizeTests

open PILean

/-- The `quantize` suite (WP13). -/
def suite : Tests.Suite := { name := "quantize" }

end Tests.QuantizeTests
