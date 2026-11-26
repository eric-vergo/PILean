/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILeanVersoManual
import ManualExample.Figures
import ManualExample.Motions

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

:::figure ManualExample.trianglePlot (label := "triangle") (alt := "A line through the points (n, n(n+1)/2) for n from 0 to 12, rising from 0 to 78.") (links := ManualExample.trianglePoints_spec)
The triangular numbers, $`0 + 1 + \cdots + n`.
:::

{figref "triangle"}[] grows like half a square. Its points:

{docstring ManualExample.trianglePoints}

:::figure ManualExample.divisorGraph (alt := "The divisors of 12 as nodes, an edge from a to b when b covers a: 1 to 2 and 3, 2 to 4 and 6, 3 to 6, 4 and 6 to 12.") (links := ManualExample.covers_count) (width := "60%")
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

# Motion

Two motions of plane figures, inline: each moves in the page and shows its key frames as stills
while it is hovered or focused, when the reader's system asks for reduced motion, and in print.

:::figure ManualExample.quarterTurn (label := "quarter") (alt := "A point P on the unit circle turns a quarter about the origin O, then holds.")
A point turned a quarter about the origin.
:::

:::figure ManualExample.slidePanels (alt := "Two panels on one clock: on the left a point turns by quarters about the origin; on the right a point slides one step to the right.")
A turn beside a slide, on one clock.
:::

# Marks over a picture

:::figure ManualExample.marks (alt := "A window with two numbered marks: 1 at the top left, 2 at the bottom right.") (backdrop := "-verso-data/backdrop-{theme}.svg")
Two marks over a picture of the site.
:::

# Links that say nothing

A link checks that a theorem is proved and names its figure, not what it says. These three
pictures claim false things and are linked to theorems that say nothing about them; their pages
say so.

:::figure ManualExample.vacuousOr (alt := "The text: K(5,2) has 16 edges.") (links := ManualExample.vacuousOr_spec)
:::

:::figure ManualExample.vacuousHypothesis (alt := "An empty diagram titled: All primes are odd.") (links := ManualExample.vacuousHypothesis_spec)
:::

:::figure ManualExample.vacuousBound (alt := "An empty diagram titled: π = 3.") (links := ManualExample.vacuousBound_spec)
:::

{figure_list}
