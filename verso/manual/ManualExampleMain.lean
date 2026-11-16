/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import ManualExample
import PILeanVersoManual

/-!
# `pilean-verso-manual-example`

Generates the example manual: `lake exe pilean-verso-manual-example --output _out`.
-/

open Verso.Genre.Manual

/-- A plain picture the example's marks are drawn over, in a theme's background colour. -/
def backdrop (bg : String) : String :=
  "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"320\" height=\"200\" " ++
  "viewBox=\"0 0 320 200\">" ++
  s!"<rect width=\"320\" height=\"200\" rx=\"8\" fill=\"{bg}\"/></svg>\n"

/-- The example's configuration: the two backdrops as data files. -/
def config : RenderConfig :=
  let base : RenderConfig := {}
  { base with extraDataFiles := base.extraDataFiles.insertMany #[
      { filename := "backdrop-light.svg", contents := (backdrop "#e8ecf0").toUTF8 },
      { filename := "backdrop-dark.svg", contents := (backdrop "#2a3039").toUTF8 }] }

/-- Generates the example manual with its figures. -/
def main (args : List String) : IO UInt32 :=
  PILeanVerso.Manual.withFigures (%doc ManualExample) site_figures% args fun args =>
    manualMain (%doc ManualExample) (options := args) (config := config)
