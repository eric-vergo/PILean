/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Verso
import VersoManual
import VersoBlueprint
import PILeanVerso
import PictureExample
import ExampleBlueprint.Diagrams

/-!
# A Blueprint without explorers

The second document of the example: the chapter of diagrams and a chapter with a plot, an inline
picture, an animation and motions of plane figures, and no explorer. Its site
(`example-no-explorer`) carries neither the explorers' script nor their stylesheet, in any page
or file.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal
open PILeanVerso
open Example

#doc (Manual) "PILean figures without an explorer" =>

The figures of the example that are not explorers: static pictures, an inline picture, an
animation and motions.

{include 0 ExampleBlueprint.Diagrams}

# Pictures

:::figure Example.cubicPlot (label := "cubic") (links := Example.cubicPlot_spec)
The cubic $`x^3 - 3x` and its derivative, drawn from exact samples.
:::

:::figure Example.windowInline (label := "inline") (inline := true) (alt := "A window disk of radius 0.8 about 1/2 over the five unit steps.")
:::

:::figure circleAnimation (label := "circle") (links := circleAnimation_spec) (width := "16rem")
A point going round the unit circle, with its height.
:::

:::figure quarterTurn (label := "quarter") (links := quarterTurn_spec) (alt := "A point P on the unit circle turns a quarter about the origin O, then holds.")
A point turned a quarter about the origin.
:::

:::figure twoFrames (label := "frames") (alt := "Two panels on one clock: on the left a point turns by fifths about two centres in turn while the disks stay; on the right the pair of centres with its disks turns about the active centre while the point stays.")
Two frames of one motion, on one clock.
:::

{figure_list}
