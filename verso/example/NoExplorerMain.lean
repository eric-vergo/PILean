/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint.PreviewManifest
import PILeanVerso
import ExampleBlueprint.NoExplorer

/-!
The generator of the example's site without explorers:
`lake exe example-no-explorer --output _out/no-explorer`.
-/

open Verso Doc
open Verso.Genre Manual

/-- Builds the site. -/
def main (args : List String) : IO UInt32 :=
  PILeanVerso.withFigures (%doc ExampleBlueprint.NoExplorer) site_figures% args fun doc args =>
    Informal.PreviewManifest.blueprintMainWithPreviewData doc args
      (extensionImpls := by exact extension_impls%)
