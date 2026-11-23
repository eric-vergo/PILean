/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Lake

/-!
# PILean's text through LeAnTeX

The library `PILeanLeAnTeX`: a `PILean.TextEngine` backed by LeAnTeX, so that the titles, axis
labels, tick labels, legends and node labels of PILean's figures are LaTeX typeset by LeAnTeX.
The gallery generator `pilean-leantex-gallery` writes `examples/`; `lake test` runs the checks.

PILean itself (the package in the parent directory) has no dependencies; this package adds
LeAnTeX, at a fixed commit.
-/

open Lake DSL

require leantex from git "https://github.com/eric-vergo/LeAnTeX" @
  "be3eb1be7bc199d1649e5638bf700641b90a0fdb"
require pilean from ".."

package «pilean-leantex» where
  leanOptions := #[⟨`linter.missingDocs, true⟩, ⟨`autoImplicit, false⟩]

@[default_target]
lean_lib PILeanLeAnTeX

lean_lib PILeanLeAnTeXTest

/-- Writes the gallery `examples/*.svg` and `*.png` from `PILeanLeAnTeX.Examples`. -/
lean_exe «pilean-leantex-gallery» where
  root := `PILeanLeAnTeXTest.Gallery

/-- Typesets one label with the engine; the test driver runs it under CPU and memory limits on
hostile labels. -/
lean_exe «pilean-leantex-probe» where
  root := `PILeanLeAnTeXTest.Probe

/-- The test driver: `lake test` runs it from this folder. -/
@[test_driver]
lean_exe «pilean-leantex-test» where
  root := `PILeanLeAnTeXTest.Main
  needs := #[«pilean-leantex-probe»]
