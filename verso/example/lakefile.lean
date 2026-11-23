/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Lake

/-!
# A Verso Blueprint with PILean figures

A small Blueprint project whose chapter shows four figures made by PILean, each the value of a
Lean declaration with a theorem about it: a function plot, a data plot, a graph of a relation and
an animation. `PictureExample` holds the figures and theorems, `ExampleBlueprint` the document,
`example-blueprint` the site's generator.
-/

open Lake DSL

require «pilean-verso» from ".."

package «pilean-verso-example» where
  leanOptions := #[⟨`autoImplicit, false⟩]

/-- The figures and the theorems about them. -/
@[default_target]
lean_lib PictureExample

/-- The Blueprint document. -/
lean_lib ExampleBlueprint where
  leanOptions := #[⟨`experimental.module, true⟩]

/-- The adapter's checks (`lake test`). -/
@[test_driver]
lean_exe «example-test» where
  root := `ExampleTest

/-- The site's generator: `lake exe example-blueprint --output _out/site`. -/
lean_exe «example-blueprint» where
  root := `ExampleMain
  supportInterpreter := true
