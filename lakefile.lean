/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Lake

/-!
# PILean's package

The library `PILean` (imports `Init` and `Std` only), the gallery generator `pilean-gallery`
(writes `examples/*.svg`), the tool `pilean-info` (shows the source information of an image), and
the test driver `lake test` runs.
-/

open Lake DSL

package pilean where
  leanOptions := #[⟨`linter.missingDocs, true⟩, ⟨`autoImplicit, false⟩]

@[default_target]
lean_lib PILean

lean_lib PILeanTest

/-- Writes the example gallery `examples/*.svg` from the specs in `PILean.Examples`. -/
lean_exe «pilean-gallery» where
  root := `PILeanTest.Gallery

/-- Prints the source information (module, declaration, file, line, ...) recorded in an SVG, PNG,
APNG or GIF file written with `PILean.Trust.withSource`. -/
lean_exe «pilean-info» where
  root := `PILeanTest.Info

/-- The test driver: `lake test` runs it from the repository root. -/
@[test_driver]
lean_exe «pilean-test» where
  root := `PILeanTest.Main
