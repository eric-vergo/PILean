/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Verso
import VersoManual
import VersoBlueprint
import PILeanVerso
import PictureExample

/-!
# The chapter of pictures

Four figures of `PictureExample.Figures` in a Blueprint chapter, each linked to its declaration and to
the theorem about it.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal
open PILeanVerso
open Example

#doc (Manual) "Pictures with proofs" =>

Each picture in this chapter is the value of a Lean declaration. The site's build drew it, wrote
the declaration, its file and a fingerprint into the file, and listed it in a manifest; the line
under each caption leads back to the Lean that made it and to the theorem about it.

# A function

:::definition "cubic" (lean := "Example.cubic")
The cubic $`f(x) = x^3 - 3x`, with exact rational arithmetic.
:::

:::theorem "cubic_samples" (lean := "Example.cubicPlot_spec")
The curve of {figref "cubic"}[] is drawn from exactly 33 sample points, the points $`(x, f(x))`
with $`x` on the grid from $`-2` to $`2` in steps of $`\tfrac{1}{8}`, each converted to a
floating-point number; between two of them the picture is a straight segment, about which
nothing is proved.
This is a statement about {uses "cubic"}[].
:::

:::figure Example.cubicPlot (label := "cubic") (proves := Example.cubicPlot_spec)
The cubic $`x^3 - 3x` (solid) and its derivative $`3x^2 - 3` (dashed), drawn from exact samples.
The derivative vanishes where the cubic turns, at $`x = \pm 1`.
:::

# Data

The Collatz map sends $`n` to $`n/2` when $`n` is even and to $`3n + 1` otherwise.
{figref "collatz"}[The plot of stopping times] shows how many steps each of the numbers 1 to 40
takes to reach 1; 27 stands out with 111 steps.

:::figure Example.collatzPlot (label := "collatz") (proves := Example.collatzPlot_spec)
Collatz stopping times of 1 to 40. The line and the markers are the computed list, point for
point.
:::

# A relation

:::figure divisorGraph (label := "divisors") (proves := divisorGraph_spec) (width := "22rem")
The divisors of 24 ordered by divisibility; an edge joins $`a` to $`b` when $`b` covers $`a`.
:::

# Explorers

:::figure_explorer Example.radiusExplorer (label := "radius") (alt := "A window disk about 1/2 over the five unit steps, its radius from 0.6 to 1.0.")
The window as its radius grows.
:::

:::figure_explorer Example.wordExplorer (label := "word") (alt := "Two circles about -1 and 1 and a point moved by fifth turns about each, letter by letter.")
The word $`aba` acting on a point.
:::

:::figure Example.windowInline (label := "inline") (inline := true) (alt := "A window disk of radius 0.8 about 1/2 over the five unit steps.")
The window of radius 0.8, inline; each step's point links to its declaration.
:::

# Inside an entry

::::definition "window_family" (lean := "Example.windowAt")
The window disks of radius $`r` about $`\tfrac{1}{2}`, drawn over the five unit steps.

:::figure_explorer Example.sizesExplorer (label := "sizes") (alt := "The window disk at two widths of the picture, 360 and 220 pixels.")
The window in frames of two sizes.
:::

:::figure Example.oddInline (label := "3d-odd") (inline := true) (alt := "A disk about 1/2 and two points, whose names hold markup.")
A picture whose names and ids hold markup, under a label that starts with a digit.
:::
::::

# Escaping

:::figure_explorer Example.oddExplorer (label := "odd") (alt := "A disk about 1/2 whose radius grows, with captions that hold markup & separators.")
Captions and values that hold the separators of a frame's label and markup: `<b>` · = .
:::

# Motion

{figref "circle"}[] moves; with reduced motion the page shows a still frame instead.

:::figure circleAnimation (label := "circle") (proves := circleAnimation_spec) (width := "16rem")
A point going round the unit circle, with its height.
:::
