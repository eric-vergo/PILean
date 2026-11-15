/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Lean
import PILean.Trust.Attr
import PILeanVerso.Themes

/-!
# `site_figures%`

The term `site_figures%` is PILean's `figures%` for a site: an `Array PILean.Trust.FigureEntry` of
every declaration with the attribute `figure` in the environment where it is used, sorted by
module and then name, each with the files `SiteOutputs` gives (the light files and, where the
figure has them, the dark ones). A site's generator passes it to `PILeanVerso.withFigures`, which
renders the figures the document uses.
-/

namespace PILeanVerso

open Lean Elab Term PILean.Trust

/-- `site_figures%` is the `Array PILean.Trust.FigureEntry` of every declaration with the attribute
`figure` in the imported modules and the current one so far, sorted by module and then name, each
rendered to its `SiteOutputs` files. -/
syntax (name := siteFiguresTerm) "site_figures%" : term

/-- The elaborator of `site_figures%`. -/
@[term_elab siteFiguresTerm]
def elabSiteFigures : TermElab := fun _ expected? => do
  let env ← getEnv
  let entries ← (sortedFigures env).mapM fun r => do
    let outputs := mkCIdent ``SiteOutputs.siteOutputs
    `(PILean.Trust.FigureEntry.mk
        (PILean.Trust.SourceData.mk $(quote r.module.toString) $(quote r.decl.toString)
          $(quote r.file) $(quote r.line) $(quote r.column) $(quote r.sourceHash))
        (fun _ => $outputs $(mkCIdent r.decl)))
  elabTerm (← `(show Array PILean.Trust.FigureEntry from #[$entries,*])) expected?

end PILeanVerso
