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

-- Verso Blueprint and the Verso and SubVerso revisions it is built against.
require subverso from git "https://github.com/eric-vergo/subverso" @
  "7202fb62e46825ab9a176a786f1e15b1ab40a6ae"
require verso from git "https://github.com/eric-vergo/verso" @
  "9aa40617081ed144742d6fa31d5a24b77fde4679"
require VersoBlueprint from git "https://github.com/eric-vergo/verso-blueprint.git" @
  "cd3f3c51d7907ed27a120bb7a2b8bbe5c24c6854"
require pilean from ".."
require «pilean-verso-manual» from "manual"

package «pilean-verso» where
  leanOptions := #[⟨`linter.missingDocs, true⟩, ⟨`autoImplicit, false⟩]

@[default_target]
lean_lib PILeanVerso
