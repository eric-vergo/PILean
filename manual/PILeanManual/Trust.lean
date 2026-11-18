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

Every image PILean makes is meant to be traceable to the Lean that made it. Three things serve
that, and each establishes less than its name might suggest, so each chapter says what it does
not establish too:

* a *source record* in the file, which names the declaration that drew it;
* a *build* that renders the declarations again, a *fingerprint* of each drawing and its
  declaration, a *manifest*, and two checkers;
* *theorems* about the Lean object a picture is drawn from, for four kinds of picture, linked to
  the picture by `figure_proves`.

None of them says that the pixels are right: the theorems are about exact numbers and lists, and
the step from them to pixels is floating point, tested and not proved.

{include 1 PILeanManual.Trust.Sources}

{include 1 PILeanManual.Trust.Builds}

{include 1 PILeanManual.Trust.Proofs}
