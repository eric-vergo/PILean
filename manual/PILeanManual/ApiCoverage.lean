/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILean
import PILean.Trust.Attr
import PILeanManual.ApiMeta

open Verso.Genre Manual
open PILeanManual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "What the Reference Covers" =>
%%%
tag := "api-coverage"
%%%

The reference has one page for every module of the core: `PILean.lean` and every file below
`PILean/`, found on disk by `lake exe pilean-manual-pages`, which writes the page files (each holds
only the module's name; `lake test` fails when they are not current). What a page shows is read
from the environment when the manual is built: the module's docstrings, then Verso's docstring
block of each *public declaration* of the module, in source order, with its signature.

A declaration of a module is public when it was written in that module's source (it has a
declaration range), is not private, has no internal name component (one that starts with `_`, or
a number), and is not one of the parts that its type's block already shows: a structure's
projections and an inductive type's constructors, whose docstrings are shown, and required, inside
the type's block. Generated code is left out too: what a `deriving` clause defines inside an
instance, and the helpers defined inside a definition (`let rec`, `where`). Instances count like
any other declaration.

A public declaration is *covered* when it and the parts its block shows have docstrings, or when
it is on the allow-list (`PILeanManual.apiAllowed?`: the names of `PILeanManual.apiAllowList`,
which is empty, and the instances whose names Lean made up, from an anonymous `instance` or a
`deriving` clause, whose class and type say what they are; the page shows the reason under each). A public declaration that is neither stops the manual's build. When this manual was built:

{apiCoverage}
