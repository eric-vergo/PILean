/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanManual
import PILeanVersoManual

/-!
# `pilean-manual`

Generates the manual: `lake exe pilean-manual --output _out`.
-/

open Verso.Genre.Manual

-- Every theorem linked to a figure of the manual writes out the whole figure, with every
-- definition of the manual it is built from (`PILean.Trust.figurePinProblem?`).
#assert_figures_pinned PILeanManual

/-- Generates the manual with its figures. -/
def main (args : List String) : IO UInt32 :=
  PILeanVerso.Manual.withFigures (%doc PILeanManual) site_figures% args fun doc args =>
    manualMain doc (options := args)
