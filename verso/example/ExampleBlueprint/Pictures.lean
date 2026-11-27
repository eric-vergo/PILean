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

The figures of `PictureExample.Figures`, `PictureExample.Diagrams` and `PictureExample.Motions`
in a Blueprint chapter, each linked to its declaration and to the theorem about it, if any.
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

:::figure Example.cubicPlot (label := "cubic") (links := Example.cubicPlot_spec)
The cubic $`x^3 - 3x` (solid) and its derivative $`3x^2 - 3` (dashed), drawn from exact samples.
The derivative vanishes where the cubic turns, at $`x = \pm 1`.
:::

# Data

The Collatz map sends $`n` to $`n/2` when $`n` is even and to $`3n + 1` otherwise.
{figref "collatz"}[The plot of stopping times] shows how many steps each of the numbers 1 to 40
takes to reach 1; 27 stands out with 111 steps.

:::figure Example.collatzPlot (label := "collatz") (links := Example.collatzPlot_spec)
Collatz stopping times of 1 to 40. The line and the markers are the computed list, point for
point.
:::

# A relation

:::figure divisorGraph (label := "divisors") (links := divisorGraph_spec) (width := "22rem")
The divisors of 24 ordered by divisibility; an edge joins $`a` to $`b` when $`b` covers $`a`.
:::

# Explorers

:::figure_explorer Example.radiusExplorer (label := "radius") (alt := "A window disk about 1/2 over the five unit steps, its radius from 0.6 to 1.0.")
The window as its radius grows.
:::

:::figure_explorer Example.wordExplorer (label := "word") (alt := "Two circles about -1 and 1 and a point moved by fifth turns about each, letter by letter.")
The word $`aba` acting on a point.
:::

:::figure_explorer Example.familyExplorer (label := "family") (alt := "A window disk over the five unit steps, its radius from 0.6 to 1.0 and its centre from 0 to 1/2.")
The window as a function of its radius and its centre.
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

:::figure oddMotion (label := "odd-motion") (alt := "Two panels whose titles, captions and labels hold markup: <script>alert(1)</script> \"q\" ]]> -- url(#x)")
A motion whose strings hold markup & quotes: `<b>` "q" `]]>` --.
:::

# Motion

{figref "circle"}[] moves; with reduced motion the page shows a still frame instead.

:::figure circleAnimation (label := "circle") (links := circleAnimation_spec) (width := "16rem")
A point going round the unit circle, with its height.
:::

The next six figures are motions of plane figures, drawn from exact key frames: each moves
inline in the page, and shows its key frames as stills while it is hovered or focused, when
animations are turned off, when the reader's system asks for reduced motion, and in print.

:::figure quarterTurn (label := "quarter") (links := quarterTurn_spec) (alt := "A point P on the unit circle turns a quarter about the origin O, then holds.")
A point turned a quarter about the origin.
:::

:::figure twoFrames (label := "frames") (alt := "Two panels on one clock: on the left a point turns by fifths about two centres in turn while the disks stay; on the right the pair of centres with its disks turns about the active centre while the point stays.")
Two frames of one motion, on one clock.
:::

:::figure fifthTurn (label := "fifth") (alt := "A disk turns a fifth of a turn about the origin O, then holds.")
A disk turned a fifth about an outside centre.
:::

:::figure announceTurns (label := "announce") (alt := "A triangle turns a quarter about A, then a quarter about B, then slides down; before each turn a ring marks its centre, the ring at A handing over to the ring at B while the triangle rests.")
A mark that announces the next turn during a rest.
:::

:::figure announcePanels (label := "announce-panels") (alt := "Two panels on one clock: a triangle and a point turn about A, then about B, then slide down; rings mark the centre of each turn before it.")
The same marks in two panels, stacked on small screens.
:::

:::figure slideAcross (label := "slides") (alt := "A square S slides three to the right along its track, then a point B slides three to the left along its own.")
Slides only: a square, then a point, along their tracks.
:::
