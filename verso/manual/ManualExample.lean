/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILeanVersoManual
import ManualExample.Figures

/-!
# The example manual

A small document of Verso's Manual genre with PILean figures and explorers, a reference to one
of them, the documentation of a declaration a picture links to, and the figures page;
`pilean-verso-manual-example` generates it, `lake test` checks the result.
-/

open Verso.Genre Manual
open PILeanVerso.Manual

#doc (Manual) "Figures in a Manual" =>
%%%
tag := "manual-example"
%%%

# Numbers

:::figure ManualExample.trianglePlot (label := "triangle") (alt := "A line through the points (n, n(n+1)/2) for n from 0 to 12, rising from 0 to 78.") (proves := ManualExample.trianglePoints_spec)
The triangular numbers, $`0 + 1 + \cdots + n`.
:::

{figref "triangle"}[] grows like half a square. Its points:

{docstring ManualExample.trianglePoints}

:::figure ManualExample.divisorGraph (alt := "The divisors of 12 as nodes, an edge from a to b when b covers a: 1 to 2 and 3, 2 to 4 and 6, 3 to 6, 4 and 6 to 12.") (proves := ManualExample.covers_count) (width := "60%")
:::

# Explorers

:::figure_explorer ManualExample.radiusSlider (label := "radius") (alt := "A window disk about 1/2 over the five unit steps, its radius from 0.6 to 1.0.")
The window as its radius grows.
:::

:::figure_explorer ManualExample.wordSteps (alt := "Two circles about -1 and 1 and a point moved by fifth turns about each, letter by letter.")
The word $`aba` acting on a point.
:::

:::figure ManualExample.windowInline (inline := true) (alt := "A window disk of radius 0.8 about 1/2 over the five unit steps.")
The window of radius 0.8, inline.
:::

# Marks over a picture

:::figure ManualExample.marks (alt := "A window with two numbered marks: 1 at the top left, 2 at the bottom right.") (backdrop := "-verso-data/backdrop-{theme}.svg")
Two marks over a picture of the site.
:::

{figure_list}
