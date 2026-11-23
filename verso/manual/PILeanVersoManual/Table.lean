/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Lean
import PILean.Trust.Attr
import PILeanVersoManual.Themes
import PILeanVersoManual.PageMeta

/-!
# `site_figures%`

The term `site_figures%` is PILean's `figures%` for a site: every declaration with the attribute
`figure` in the environment where it is used, sorted by module and then name, each with the files
`SiteOutputs` gives (the light files and, where the figure has them, the dark ones) and with its
standing (`PILean.Trust.figureStanding`, checked again in this environment, set on every output
with `withStanding`, as `figures%` does). Where a `SiteFigures` is expected (the argument of
`PILeanVerso.withFigures`) it also holds what each figure's page shows of the code
(`figurePageData`); elsewhere it is the `Array PILean.Trust.FigureEntry` alone.
-/

namespace PILeanVerso

open Lean Elab Term PILean.Trust

/-- `site_figures%` is the table of every declaration with the attribute `figure` in the imported
modules and the current one so far, sorted by module and then name, each rendered to its
`SiteOutputs` files with its standing set (`figureStanding`): a `SiteFigures` with the page data
of each figure where one is expected, an `Array PILean.Trust.FigureEntry` otherwise. -/
syntax (name := siteFiguresTerm) "site_figures%" : term

/-- The elaborator of `site_figures%`. -/
@[term_elab siteFiguresTerm]
def elabSiteFigures : TermElab := fun _ expected? => do
  let env ← getEnv
  let wantsPages ← match expected? with
    | some t => pure ((← instantiateMVars t).isConstOf ``SiteFigures)
    | none => pure false
  let mut entries := #[]
  let mut pages : Array FigurePageData := #[]
  for r in sortedFigures env do
    let s ← figureStanding r
    let standing ← quoteStanding s
    let outputs := mkCIdent ``SiteOutputs.siteOutputs
    entries := entries.push (← `(PILean.Trust.FigureEntry.mk
        (PILean.Trust.SourceData.mk $(quote r.module.toString) $(quote r.decl.toString)
          $(quote r.file) $(quote r.line) $(quote r.column) $(quote r.sourceHash))
        (fun _ => PILean.Trust.withStanding $standing ($outputs $(mkCIdent r.decl)))))
    if wantsPages then pages := pages.push (← figurePageData r s)
  let table ← `(show Array PILean.Trust.FigureEntry from #[$entries,*])
  if wantsPages then
    let json := (toJson pages).compress
    elabTerm (← `(PILeanVerso.SiteFigures.mk $table $(quote json))) expected?
  else elabTerm table expected?

end PILeanVerso
