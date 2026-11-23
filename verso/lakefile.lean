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

-- Verso Blueprint and the Verso and SubVerso revisions it is built against: Verso's
-- v4.35.0-patch1 release, SubVerso and Verso Blueprint at the revisions downstream projects use.
require subverso from git "https://github.com/eric-vergo/subverso" @
  "f53c070f0357f5dcf3b03b8924deb714294dac69"
require verso from git "https://github.com/leanprover/verso" @
  "d56e6c92d8606a5ae2baf18f0090ca6e82ca38e4"
require VersoBlueprint from git "https://github.com/eric-vergo/verso-blueprint.git" @
  "9fa92b2bf1d3bf2071963157e077b011666c435d"
require pilean from ".."
require «pilean-verso-manual» from "manual"

package «pilean-verso» where
  leanOptions := #[⟨`linter.missingDocs, true⟩, ⟨`autoImplicit, false⟩]

@[default_target]
lean_lib PILeanVerso
