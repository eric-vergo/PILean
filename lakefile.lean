/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Lake

/-!
# PILean's package

The library `PILean` (imports `Init` and `Std` only), the gallery generator `pilean-gallery`
(writes `examples/*.svg`), the tool `pilean-info` (shows the source information of an image), the
build tools `pilean-build` and `pilean-verify`, and the test driver `lake test` runs.
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

/-- Renders the figures of the gallery that carry `@[figure]` into a directory with a manifest, or
checks a directory against what the build produces (`--check`). -/
lean_exe «pilean-build» where
  root := `PILeanTest.Build

/-- Checks a directory written by `pilean-build` against its `manifest.json` and the source
information inside each file. -/
lean_exe «pilean-verify» where
  root := `PILeanTest.Verify

/-- Decodes one file with a reader's default limits; the test driver runs it under CPU and memory
limits on hostile inputs. -/
lean_exe «pilean-probe» where
  root := `PILeanTest.Probe

/-- The test driver: `lake test` runs it from the repository root. It runs the tools, so they are
built first. -/
@[test_driver]
lean_exe «pilean-test» where
  root := `PILeanTest.Main
  needs := #[«pilean-probe», «pilean-info», «pilean-verify»]
