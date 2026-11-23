/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Lake

/-!
# PILean figures in Verso's Manual genre

The library `PILeanVersoManual` puts PILean figures into documents of Verso's Manual genre: the
directive `figure`, the figures page, references to figures and the generator wrapper that
renders every figure a document uses, writes the files with a manifest and checks them. It also
holds what the Verso Blueprint adapter (`pilean-verso`, the parent folder) builds on: the site's
rendering, the light and dark outputs, the table of figures, the stylesheet and the shared parts
of the figure blocks.

It needs Verso only (no Verso Blueprint), at the commits the Blueprint adapter uses (Verso's
v4.35.0-patch1 release).
-/

open Lake DSL

require subverso from git "https://github.com/eric-vergo/subverso" @
  "f53c070f0357f5dcf3b03b8924deb714294dac69"
require verso from git "https://github.com/leanprover/verso" @
  "d56e6c92d8606a5ae2baf18f0090ca6e82ca38e4"
require pilean from "../.."

package «pilean-verso-manual» where
  leanOptions := #[⟨`linter.missingDocs, true⟩, ⟨`autoImplicit, false⟩]

@[default_target]
lean_lib PILeanVersoManual

/-- A small manual with three figures (`ManualExample`), its figures and what they show. -/
lean_lib ManualExample where
  roots := #[`ManualExample]

/-- The example manual's generator: `lake exe pilean-verso-manual-example --output _out`. -/
lean_exe «pilean-verso-manual-example» where
  root := `ManualExampleMain
  supportInterpreter := true

/-- The checks of the Manual-genre adapter (`lake test`): the example manual is generated twice
and its pages and files are inspected. -/
@[test_driver]
lean_exe «pilean-verso-manual-test» where
  root := `PILeanVersoManualTest
