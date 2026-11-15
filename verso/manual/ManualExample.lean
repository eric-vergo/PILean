/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILeanVersoManual
import ManualExample.Figures

/-!
# The example manual

A small document of Verso's Manual genre with three PILean figures, a reference to one of them
and the figures page; `pilean-verso-manual-example` generates it, `lake test` checks the result.
-/

open Verso.Genre Manual
open PILeanVerso.Manual

#doc (Manual) "Figures in a Manual" =>
%%%
tag := "manual-example"
%%%

# Numbers

:::figure ManualExample.trianglePlot (label := "triangle") (alt := "A line through the points (n, n(n+1)/2) for n from 0 to 12, rising from 0 to 78.") (proves := ManualExample.two_mul_triangle)
The triangular numbers, $`0 + 1 + \cdots + n`.
:::

{figref "triangle"}[] grows like half a square.

:::figure ManualExample.divisorGraph (alt := "The divisors of 12 as nodes, an edge from a to b when b covers a: 1 to 2 and 3, 2 to 4 and 6, 3 to 6, 4 and 6 to 12.") (proves := ManualExample.covers_count) (width := "60%")
:::

# Marks over a picture

:::figure ManualExample.marks (alt := "A window with two numbered marks: 1 at the top left, 2 at the bottom right.") (backdrop := "-verso-data/backdrop-{theme}.svg")
Two marks over a picture of the site.
:::

{figure_list}
