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

open Verso.Genre
open Verso.Genre.Manual
open Informal
open PILeanVerso

#doc (Manual) "PILean figures in a Blueprint" =>

A small Blueprint whose pictures are drawn by PILean from Lean declarations, each with a theorem
about what it shows.

{include 0 ExampleBlueprint.Pictures}

{blueprint_summary}

{figure_list}
