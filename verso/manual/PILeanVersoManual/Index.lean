/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanVersoManual.Block

/-!
# The figures page and references to figures, in the Manual genre

`{figure_list}` adds a page "Figures" that lists every figure of the document in order: a small
picture, its number and caption, the declaration that made it with its file and line, the
fingerprint, the files with their formats, the theorem when there is one, and a link to the
manifest.

`{figref "label"}[]` refers to the figure with that label: "Figure 2", linked to it; text in the
brackets replaces the default.
-/

namespace PILeanVerso.Manual

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre.Manual
open Lean.Doc.Syntax
open Verso.Output (Html)
open Verso.Doc.Html (HtmlT)
open Verso.Output.Html
open PILeanVerso

-- The figures page's block.
block_extension Block.figureList where
  traverse _ _ _ := pure none
  toHtml := some fun _goI _goB _id _json _contents => do
    let style ← (declStyleRef.get : IO DeclStyle)
    pure (figureListHtmlWith style "pilean-math" (← HtmlT.state))
  toTeX := some fun _ _ _ _ _ => pure (.text "The list of figures is in the HTML version.")
  extraCss := [figureCss]

open Verso Doc Elab Syntax in
/-- The part `{figure_list}` adds: an unnumbered page "Figures". -/
def mkFigureListPart (stx : Syntax) (endPos : String.Pos.Raw) : PartElabM FinishedPart := do
  let titleInlines ← `(inline | "Figures")
  let expandedTitle ← #[titleInlines].mapM (elabInline ·)
  let metadata : Option (TSyntax `term) := some (← `(term| { number := false }))
  let block ← ``(Verso.Doc.Block.other Block.figureList #[])
  pure <| FinishedPart.mk stx stx expandedTitle "Figures" metadata #[block] #[] endPos

open Verso Doc Elab Syntax PartElabM in
/-- `{figure_list}`: a page listing every figure of the document. -/
@[part_command Lean.Doc.Syntax.command]
def figureListCmd : PartCommand
  | stx@`(block|command{figure_list}) => do
    let endPos := stx.getTailPos?.get!
    closePartsUntil 1 endPos
    addPart (← mkFigureListPart stx endPos)
  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)

-- The inline of `{figref "label"}[]`; its data is the label.
inline_extension Inline.figref (label : String) where
  data := .str label
  traverse _ _ _ := pure none
  toHtml := some fun goI _id json contents => do
    let .str label := json
      | Verso.reportError "Malformed data of a figure reference"; pure .empty
    let st ← HtmlT.state
    let reg := Registry.get st
    let some p := reg.placed.find? (·.data.label == some label)
      | Verso.reportError s!"No figure has the label {label}"; pure .empty
    let text ← if contents.isEmpty then pure (.text true s!"Figure {p.number}")
      else .seq <$> contents.mapM goI
    match st.resolveDomainObject figureDomain label with
    | .ok link => pure {{<a class="pilean-figref" href={{link.link}}>{{text}}</a>}}
    | .error e => Verso.reportError e; pure text
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

end PILeanVerso.Manual
