/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILeanManual.Trust.Sources
import PILeanManual.Trust.Builds
import PILeanManual.Trust.Proofs

open Verso.Genre Manual

#doc (Manual) "Trust and Proofs" =>
%%%
tag := "trust"
%%%

PILean is built so that an image can be traced to the Lean that made it. Three things serve
that, and each establishes less than its name might suggest, so each chapter says what it does
not establish too:

* a *source record* in the file, which says which declaration drew it: an unsigned statement by
  whoever wrote the file, present only when the file was written with one;
* a *build* that renders the declarations again, a *fingerprint* of each drawing and its
  declaration, a *manifest*, and two checkers;
* *theorems* about the Lean object a picture is drawn from: for four kinds of picture the library
  proves lemmas from which an author can state such a theorem and link it to the picture with
  `figure_proves`; a picture has a theorem only if its author wrote one.

None of them says that the pixels are right: the theorems are about exact numbers and lists, and
the step from them to pixels is floating point, tested and not proved.

{include 1 PILeanManual.Trust.Sources}

{include 1 PILeanManual.Trust.Builds}

{include 1 PILeanManual.Trust.Proofs}
