/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILeanManual.ApiMeta
import PILean.Pdf.Check

-- Written by `lake exe pilean-manual-pages`; `lake test` fails when it is stale.

open Verso.Genre Manual
open PILeanManual

set_option maxRecDepth 16384

#doc (Manual) "PILean.Pdf.Check" =>
%%%
tag := "api-PILean.Pdf.Check"
shortTitle := "PILean.Pdf.Check"
%%%

{apiModule PILean.Pdf.Check}
