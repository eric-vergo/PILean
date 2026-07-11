import Tests.Framework
import Tests.Prng

/-!
# kernel tests

Convolution, blurs, sharpen, Pillow-parity ops. Owned by WP19 — that work package fills in `cases`.
-/

namespace Tests.KernelTests

open PILean

/-- The `kernel` suite (WP19). -/
def suite : Tests.Suite := { name := "kernel" }

end Tests.KernelTests
