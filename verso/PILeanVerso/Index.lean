/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanVerso.Block

/-!
# The figures page and references to figures

`{figure_list}` adds a page "Figures" that lists every figure of the document in order: a small
picture, its number and caption, the declaration that made it with its file and line, the
fingerprint, the files with their formats, the theorem when there is one, and a link to the
manifest. It is the place to see at a glance where every picture comes from.

`{figref "label"}[]` refers to the figure with that label: "Figure 2.1", linked to it; text in the
brackets replaces the default.
-/

namespace PILeanVerso

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre.Manual
open Lean.Doc.Syntax
open Verso.Output (Html)
open Verso.Doc.Html (HtmlT)
open Verso.Output.Html
open PILean.Trust

/-! ### The figures page -/

/-- A link to the figure placed as `p`, if the traversal gave it an anchor. -/
def placedLink? (st : TraverseState) (p : Placed) : Option String := do
  let .ok (id : InternalId) := Lean.Json.parse p.key >>= fromJson? | none
  let link ← st.resolveId id
  pure link.link

/-- The label of a file in the list of files: its format and theme. -/
def fileLabel (f : FileInfo) : String :=
  let fmt := match f.format with
    | "svg" => "SVG"
    | "png" => "PNG"
    | "apng" => "APNG"
    | "gif" => "GIF"
    | other => other
  match f.name with
  | "" => fmt
  | "-dark" => s!"{fmt} (dark)"
  | "-poster" => s!"{fmt} (still)"
  | n => s!"{fmt} ({(n.drop 1).toString})"

/-- One entry of the figures page. -/
def indexEntry (st : TraverseState) (p : Placed) : Html :=
  let d := p.data
  let href := (placedLink? st p).getD "#"
  let thumb := match pick? p.files "svg" "" <|> pick? p.files "png" "" with
    | some f => {{<a class="pilean-index-thumb" href={{href}}>
        {{imgTag f "pilean-index-img" d.alt d.title none}}</a>}}
    | none => .empty
  let files := p.files.map fun f =>
    {{<a href={{fileUrl f.path}} title={{s!"{f.bytes} bytes, SHA-256 {f.sha256}"}}>
      {{.text true (fileLabel f)}}</a>}}
  let thm : Html := match d.proves with
    | some t =>
      {{<dt>"Theorem"</dt><dd>{{declHtml t.name}} {{placeHtml t.file t.line p.theoremHref}}</dd>}}
    | none => {{<dt>"Theorem"</dt><dd>"none named"</dd>}}
  let caption : Html := .seq <| d.caption.map fun (m, t) =>
    if m then {{<code class="bp_math inline">{{.text true t}}</code>}} else .text true t
  {{<li>
      {{thumb}}
      <div class="pilean-index-body">
        <p class="pilean-index-title"><a href={{href}}>{{.text true s!"Figure {p.number}"}}</a>
          {{caption}}</p>
        <dl class="pilean-index-facts">
          <dt>"Source"</dt><dd>{{declHtml d.decl}} {{placeHtml d.file d.line p.sourceHref}}</dd>
          <dt>"Fingerprint"</dt><dd>{{fingerprintHtml (shownFingerprint p)}}</dd>
          <dt>"Files"</dt><dd class="pilean-index-files">{{files}}</dd>
          {{thm}}
        </dl>
      </div>
    </li>}}

/-- The body of the figures page. -/
def figureListHtml (st : TraverseState) : Html :=
  let reg := Registry.get st
  let placed := reg.placed.qsort (·.order < ·.order)
  let intro := {{<p class="pilean-figure-index-intro">
      "Every picture on this site was drawn by the site's build from the Lean declaration named
      beside it. The fingerprint covers what the picture shows and the declaration's source; "
      <a href={{fileUrl manifestName}}>"the manifest"</a>
      " lists every file with its SHA-256, and " <code>"pilean-verify"</code>
      " checks a copy of the folder against it."</p>}}
  if placed.isEmpty then
    {{<div class="pilean-figure-list">{{intro}}<p>"This document has no figures."</p></div>}}
  else
    {{<div class="pilean-figure-list">{{intro}}
      <ol class="pilean-figure-index">{{placed.map (indexEntry st)}}</ol></div>}}

-- The figures page's block.
block_extension Block.figureList where
  traverse _ _ _ := pure none
  toHtml := some fun _goI _goB _id _json _contents => do
    pure (figureListHtml (← HtmlT.state))
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

/-! ### References -/

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

end PILeanVerso
