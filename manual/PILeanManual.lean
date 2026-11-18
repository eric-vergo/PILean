/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILeanVersoManual
import PILeanManual.GettingStarted
import PILeanManual.Guide
import PILeanManual.Trust
import PILeanManual.Api

/-!
# PILean's manual

The root of the manual: getting started, the guide, trust and proofs, the API reference and the
list of figures. `Main.lean` generates it.
-/

open Verso.Genre Manual
open PILeanVerso.Manual

#doc (Manual) "PILean" =>
%%%
tag := "pilean"
authors := ["Eric Vergo", "Claude (Anthropic)"]
%%%

PILean is a pure-Lean image library, in the role Pillow has in Python: colours, geometry, vector
paths, a drawing canvas, SVG and PNG output, plots, graphs of nodes and edges, and animations, with
a trust layer that ties every image to the Lean that produced it. This manual is a Lean program
too: its examples are elaborated, its printed results and pictures are produced when it is built,
and its API reference is read from the library's docstrings.

{include 1 PILeanManual.GettingStarted}

{include 1 PILeanManual.Guide}

{include 1 PILeanManual.Trust}

{include 1 PILeanManual.Api}

{figure_list}
