/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Lake

/-!
# PILean figures in Verso documents

The library `PILeanVerso` puts PILean figures into Verso Manual-genre documents and Verso
Blueprint sites: the directive `figure`, the figures page, and the generator wrapper that renders
every figure a document uses, writes the files with a manifest and checks them.

PILean itself (the package in the parent directory) has no dependencies; this package adds Verso
and Verso Blueprint, at fixed commits. What it shares with the adapter for plain Verso manuals
(rendering, light and dark outputs, the table of figures, the stylesheet, the records, checks and
HTML of a figure block) is the package `pilean-verso-manual` in the folder `manual/`.
-/

open Lake DSL

-- Verso Blueprint and the Verso and SubVerso revisions it is built against: the Lean 4.36.0 line
-- of each, at the revisions downstream projects use.
require subverso from git "https://github.com/eric-vergo/subverso" @
  "4e04c61d96960d5a1461c6c870572ccb8b45a495"
require verso from git "https://github.com/eric-vergo/verso" @
  "94cea086b880f61f5b3847d30151b8e5f80e1259"
require VersoBlueprint from git "https://github.com/eric-vergo/verso-blueprint.git" @
  "39675f22c94b397ca90f02131f8c39c5f11db543"
require pilean from ".."
require «pilean-verso-manual» from "manual"

-- `warningAsError`: a warning in this package's own modules fails the build; `lake build
-- --wfail` would also fail on the deprecation warnings of the pinned Verso Blueprint.
package «pilean-verso» where
  leanOptions := #[⟨`linter.missingDocs, true⟩, ⟨`autoImplicit, false⟩, ⟨`warningAsError, true⟩]

@[default_target]
lean_lib PILeanVerso
