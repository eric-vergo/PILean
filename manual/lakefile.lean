/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Lake

/-!
# PILean's manual

The library `PILeanManual` is PILean's manual, a document of Verso's Manual genre: the getting
started page, the guide, trust and proofs, and the API reference (one page per module of the
core, its declarations listed from the environment with their docstrings). Its figures are drawn
by PILean when the manual is generated, through the `figure` directive of `pilean-verso-manual`.

* `lake exe pilean-manual --output _out`: generates the site (`_out/html-multi`).
* `lake exe pilean-manual-pages`: writes the API reference's page files, one per core module;
  `--check` fails when they are not current.
* `lake test`: the checks of the API reference's coverage and of a generated site.
-/

open Lake DSL

require subverso from git "https://github.com/eric-vergo/subverso" @
  "7202fb62e46825ab9a176a786f1e15b1ab40a6ae"
require verso from git "https://github.com/eric-vergo/verso" @
  "ea2e2ab37a41e50bbff0787ba896c55ea3d39df1"
require pilean from ".."
require «pilean-verso-manual» from "../verso/manual"

package «pilean-manual» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`weak.verso.code.warnLineLength, (100 : Nat)⟩]

lean_lib PILeanManual where
  roots := #[`PILeanManual]
  globs := #[.andSubmodules `PILeanManual]

/-- The manual's generator: `lake exe pilean-manual --output _out`. -/
@[default_target]
lean_exe «pilean-manual» where
  root := `Main
  supportInterpreter := true

/-- Writes the API reference's page files from the list of the core's modules. -/
lean_exe «pilean-manual-pages» where
  root := `Pages

/-- The manual's checks (`lake test`): the coverage of the API reference, the page files, and a
generated site. -/
@[test_driver]
lean_exe «pilean-manual-test» where
  root := `ManualTest
  supportInterpreter := true
  needs := #[«pilean-manual»]
