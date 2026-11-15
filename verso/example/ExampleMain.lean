/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import VersoBlueprint.PreviewManifest
import PILeanVerso
import ExampleBlueprint

/-!
The site's generator: `lake exe example-blueprint --output _out/site`. `withFigures` renders the
figures the document uses and checks the folder the generator writes.
-/

open Verso Doc
open Verso.Genre Manual

/-- Builds the site. -/
def main (args : List String) : IO UInt32 :=
  PILeanVerso.withFigures (%doc ExampleBlueprint) site_figures% args fun args =>
    Informal.PreviewManifest.blueprintMainWithPreviewData (%doc ExampleBlueprint) args
      (extensionImpls := by exact extension_impls%)
