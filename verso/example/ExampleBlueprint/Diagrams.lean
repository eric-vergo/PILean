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
# The chapter of diagrams

The figures of `PictureExample.Diagrams` in a Blueprint chapter: a Hasse diagram and a commutative
square, each tied to its object by a theorem, an illustration with none, and a figure whose name
and caption hold markup.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal
open PILeanVerso
open Example

#doc (Manual) "Diagrams" =>

Each diagram's page (linked from the line under its caption) shows its standing, its code and how
it was built.

# An order

:::figure Example.divisorHasse (label := "hasse") (proves := Example.divisorHasse_spec)
The divisors of 12 under divisibility: an edge joins $`a` below $`b` when $`b` is $`a` times a
prime.
:::

# A commutative square

:::figure Example.reductionSquare (label := "square") (proves := Example.reductionSquare_spec)
Reductions of $`\mathbb{Z}/12`: both ways round the square agree.
:::

# An illustration

:::figure Example.sketch (label := "sketch")
The Young diagram of $`(3, 2, 1)`, shown for what it shows: no theorem ties it to its object.
:::

# Markup in names and captions

:::figure Example.«hasse <b>"&'» (label := "markup") (alt := "Four divisors of 6 in a diamond.") (proves := Example.«hasse <b>"&'_spec»)
A caption with markup a page must escape: `</figcaption><script>alert(1)</script>` & <b>"q"</b> 'x'.
:::
