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

The selection is made by the shape of each name and by what the environment records, not by
knowing how a declaration was made. A declaration of a module is public when all of these hold:

* the environment gives it a declaration range (a position in the module's source);
* it is not private;
* no component of its name starts with `_` or is a number;
* it is not a structure's projection, a constructor or a recursor (the projections and
  constructors are shown, and their docstrings required, inside their type's block), nor an
  auxiliary recursor or a `noConfusion` declaration;
* the declaration its name is below is not an instance (where a `deriving` clause puts what it
  defines), and not a function, a value or a theorem (where `let rec` and `where` put their
  helpers).

So a declaration written by hand with such a name (below an instance or a function, or with a
component that starts with `_`) is left out as if it were generated. Instances count like any
other declaration.

A public declaration is *covered* when it and the parts its block shows have docstrings, or when
it is on the allow-list (`PILeanManual.apiAllowed?`): the names of `PILeanManual.apiAllowList`,
which is empty, and the instances without a docstring whose last name component starts with
`inst`. That is how Lean names an anonymous `instance` or one from a `deriving` clause, but an
instance named so by hand is allowed too; the page shows the reason under each. A public
declaration that is neither stops the manual's build. When this manual was built (the manual's
`lake test` counts again from the built library and checks that this sentence on the generated
page has the same numbers):

{apiCoverage}
