/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanVerso.Block
import PILeanVersoManual.Page

/-!
# The figures page and references to figures

`{figure_list}` adds a page "Figures" that lists every figure of the document in order: a small
picture, its number and caption, the declaration that made it with its file and line, the
fingerprint, the files with their formats, the theorem when there is one, and a link to the
manifest. It is the place to see at a glance where every picture comes from.

Below it, each figure has a page of its own (`Block.figurePage`, `PILeanVersoManual.Page`; a
figure the document shows as an explorer, `Block.explorerPage`): the picture, its files, its
standing, its code and its provenance.

`{figref "label"}[]` refers to the figure with that label: "Figure 2.1", linked to it; text in the
brackets replaces the default.
-/

namespace PILeanVerso

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre.Manual
open Lean.Doc.Parser
open Verso.Output (Html)
open Verso.Doc.Html (HtmlT)
open Verso.Output.Html
open PILean.Trust

/-! ### The figures page -/

-- The figures page's block.
block_extension Block.figureList where
  traverse _ _ _ := pure none
  toHtml := some fun _goI _goB _id _json _contents => do
    let site ← (siteRef.get : IO _)
    (figureListHtmlWith blueprintDeclStyle "bp_math inline" (← HtmlT.state) site : IO Html)
  toTeX := some fun _ _ _ _ _ => pure (.text "The list of figures is in the HTML version.")
  extraCss := [figureCss]

-- The block of a figure's page; its data is the figure's declaration.
block_extension Block.figurePage (decl : String) via withHighlighting where
  data := .str decl
  traverse id json _ := do
    traversePageWith id json
    pure none
  toHtml := some fun _goI _goB id json _contents => do
    let .str decl := json
      | Verso.reportError "Malformed data of a figure's page"; pure .empty
    let some site ← (siteRef.get : IO _)
      | Verso.reportError s!"The page of {decl} has no rendered site: the generator must run \
          the document through PILeanVerso.withFigures"; pure .empty
    let st ← HtmlT.state
    figurePageHtmlWith blueprintDeclStyle "bp_math inline" st site decl (st.htmlId id)
  toTeX := some fun _ _ _ _ _ => pure (.text "The figure's page is in the HTML version.")
  extraCss := [figureCss, motionCss, pageCss]

-- The block of the page of a figure shown as an explorer somewhere in the document: the page
-- block with the explorers' script and stylesheet (see `Block.explorer`).
block_extension Block.explorerPage (decl : String) via withHighlighting where
  data := .str decl
  traverse := Block.figurePage.descr.traverse
  toHtml := Block.figurePage.descr.toHtml
  toTeX := Block.figurePage.descr.toTeX
  extraCss := [figureCss, explorerCss, pageCss]
  extraJsFiles := {explorerJsFile}

open Verso Doc Elab Syntax in
/-- The part `{figure_list}` adds: an unnumbered page "Figures". -/
def mkFigureListPart (stx : Syntax) (endPos : String.Pos.Raw) : PartElabM FinishedPart := do
  let expandedTitle := #[← ``(Verso.Doc.Inline.text "Figures")]
  let metadata : Option (TSyntax `term) := some (← `(term| { number := false }))
  let block ← ``(Verso.Doc.Block.other Block.figureList #[])
  pure <| FinishedPart.mk stx stx expandedTitle "Figures" metadata #[block] #[] endPos

open Verso Doc Elab Syntax PartElabM in
/-- `{figure_list}`: a page listing every figure of the document. -/
@[part_command Lean.Doc.Parser.Block.command]
def figureListCmd : PartCommand
  | .command v => do
    unless v.name.getId == `figure_list do Lean.Elab.throwUnsupportedSyntax
    unless v.args.isEmpty do Lean.Elab.throwUnsupportedSyntax
    let stx : Syntax := v.stx
    let endPos := stx.getTailPos?.get!
    closePartsUntil 1 endPos
    addPart (← mkFigureListPart stx endPos)
  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)

/-! ### References -/

-- The inline of `{figref "label"}[]`; its data is the label.
inline_extension Inline.figref (label : String) where
  data := .str label
  traverse _ _ _ := pure none
  toHtml := some fun goI _id json contents => do
    let .str label := json
      | Verso.reportError "Malformed data of a figure reference"; pure .empty
    let body ← contents.mapM goI
    match figrefHtml (← HtmlT.state) label body with
    | .ok h => pure h
    | .error e => Verso.reportError e; pure (.seq body)
  toTeX := some fun goI _id json contents => do
    let label := match json with
      | .str l => l
      | _ => ""
    if contents.isEmpty then pure (.text s!"Figure {label}") else .seq <$> contents.mapM goI

/-- The arguments of `figref`: the label. -/
structure FigRefConfig where
  /-- The figure's label. -/
  label : String

section
variable {m : Type → Type} [Monad m] [MonadError m]

/-- The argument parser of `figref`. -/
def FigRefConfig.parse : ArgParse m FigRefConfig :=
  FigRefConfig.mk <$> .positional `label .string

instance : FromArgs FigRefConfig m := ⟨FigRefConfig.parse⟩

end

/-- `{figref "label"}[text]`: a link to the figure with that label. -/
@[role]
def figref : RoleExpanderOf FigRefConfig
  | cfg, inlines => do
    let body ← inlines.mapM elabInline
    ``(Verso.Doc.Inline.other (Inline.figref $(quote cfg.label)) #[$body,*])

end PILeanVerso
