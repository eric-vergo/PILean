/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILeanVersoManual
import ManualExample.Figures
import ManualExample.Motions

/-!
# A manual without explorers

A second, smaller document of the example's figures with no explorer: a plot, an inline
picture and a motion, and the figures page. The adapter's checks generate it and require that
no page or file of its site carries the explorers' script or stylesheet.
-/

open Verso.Genre Manual
open PILeanVerso.Manual

#doc (Manual) "Figures without an explorer" =>

# Pictures

:::figure ManualExample.trianglePlot (label := "triangle") (alt := "A line through the points (n, n(n+1)/2) for n from 0 to 12, rising from 0 to 78.") (links := ManualExample.trianglePoints_spec)
The triangular numbers.
:::

:::figure ManualExample.windowInline (inline := true) (alt := "A window disk of radius 0.8 about 1/2 over the five unit steps.")
The window of radius 0.8, inline.
:::

:::figure ManualExample.quarterTurn (label := "quarter") (alt := "A point P on the unit circle turns a quarter about the origin O, then holds.")
A point turned a quarter about the origin.
:::

{figure_list}
