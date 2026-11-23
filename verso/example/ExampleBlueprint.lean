/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Summary
import PILeanVerso
import ExampleBlueprint.Pictures
import ExampleBlueprint.Diagrams

/-!
# The example Blueprint

The document of the example: a chapter of pictures (`ExampleBlueprint.Pictures`), a chapter of
diagrams (`ExampleBlueprint.Diagrams`) and the
Blueprint's summary.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal
open PILeanVerso

#doc (Manual) "PILean figures in a Blueprint" =>

A small Blueprint whose pictures are drawn by PILean from Lean declarations, each with a theorem
about what it shows.

{include 0 ExampleBlueprint.Pictures}

{include 0 ExampleBlueprint.Diagrams}

{blueprint_summary}

{figure_list}
