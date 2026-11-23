/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoBlueprint.LeanSourceAnchor
import VersoBlueprint.Resolve
import VersoBlueprint.Informal.Block.Store
import PILeanVersoManual.Common

/-!
# Figures in Verso documents

The directive `figure` puts a PILean figure into a Manual-genre document (a Verso Blueprint
chapter, a Verso manual):

```
:::figure MyProject.Figures.sine (label := "sine") (proves := MyProject.Figures.sine_spec)
The sine function, sampled on an exact grid.
:::
```

The first argument names a declaration with the attribute `@[figure]`. The body, which may be
empty, is the caption; an empty body takes the declaration's doc string. The named arguments, all
optional:

* `label := "..."`: the name `{figref "..."}[]` refers to; it is also the figure's anchor.
* `alt := "..."`: the text alternative; the default is the declaration's doc string (or its name).
* `title := "..."`: the picture's tooltip; the default names the declaration and its file.
* `format := "svg"`: the file shown: `svg` (the default), `png`, `apng` or `gif`; an animation's
  `svg` is its animated SVG.
* `width := "..."`: the picture's width as a CSS length (`60%`, `24rem`, `480px`).
* `inline := true`: the picture put inline as an `svg` element (its narrow rendition on small
  screens, when it has one): its titles show on hover, its elements that name a declaration
  (`data-lean-decl`) link to it as the source line does (the site's link mode), and one picture
  serves both themes. A figure without an inline picture fails the site's build.
* `proves := name`: a theorem about the figure. It must exist, must not depend on `sorryAx` or any
  axiom other than `propext`, `Classical.choice` and `Quot.sound`, and its statement must name
  the figure itself (PILean's rule, `figure_proves`): a statement about a series or a relation
  the figure is built from is refused, so the theorem begins by saying what the figure holds.

The figure is numbered as the Blueprint numbers its blocks (`verso.blueprint.numbering`,
`verso.blueprint.subNumberingPrefix`), with its own counter: "Figure 2.1". Its caption ends with a
line that names the declaration that made the picture and its file and line (a link to the
repository at the build's commit when the site has one), its fingerprint and the theorem, if any.
Where a declaration's name links is the site's link mode (`--figure-lean-links`,
`PILeanVerso.LeanLinks`): `ideil` by default (`lean:decl/` links for viewers that set
`data-lean-links`, plain names otherwise), `site` (the declaration's row in the Lean panel of the
Blueprint entry that names it, an inline Lean block that defines it, or the figure it draws; the
build warns about a declaration with none of these) or `none`.

`:::figure_explorer Decl …` takes the same options and shows an explorer (`PILean.Explorer`: a
parameter axis with a slider, a step sequence with previous, play and next, or both): every frame
inline, pan and zoom, the script `pilean-explorer.js` of the site; without script the frames are
a grid with their values and captions. On a declaration of another type it is an error.

`{figure_list}` adds a page that lists every figure of the document with its source, fingerprint,
files and theorem; `{figref "label"}[]` refers to a figure by its label.

The pictures are written by the site build only (`PILeanVerso.withFigures`); this module reads
them from `siteRef` during traversal. The records, the checks and the HTML it shares with the
Manual-genre adapter are in `PILeanVersoManual.Common`; this module adds the Blueprint's
numbering and the places of declarations in a Blueprint. The `backdrop := "..."` option of that
adapter is accepted here too.
-/

namespace PILeanVerso

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre.Manual
open Verso.Output (Html)
open Verso.Doc.Html (HtmlT)
open PILean PILean.Trust

/-- The place of a declaration in a Blueprint, as a link relative to the site's root: the row of
the Lean panel of the first entry (by label) that shows it, else an inline Lean block that
defines it. -/
def blueprintTarget (st : TraverseState) (n : String) : Option String :=
  let dom := Informal.Resolve.externalRenderedDeclDomainName
  let keys := match st.domains.get? dom with
    | some d =>
      d.objects.foldl (init := (#[] : Array String)) fun (acc : Array String) (k : String) _ =>
        if k.startsWith "label:" && k.endsWith ("|" ++ n) then acc.push k else acc
    | none => #[]
  let row := (keys.qsort (· < ·)).findSome? (Informal.Resolve.resolveDomainHref? st dom ·)
  row <|> Informal.Resolve.resolveInlineLeanDeclHref? st n.toName

open Verso.Output.Html in
/-- How a Blueprint shows the declarations of its figures: the name as code, the file and line
linked to the repository when the site has one, and the place of a declaration in the
Blueprint (`blueprintTarget`). -/
def blueprintDeclStyle : DeclStyle where
  decl n := {{<code>{{.text true n}}</code>}}
  place r href := placeHtml r.file r.line href
  target := blueprintTarget

/-- The part number a figure's number goes below, as the Blueprint numbers its blocks. -/
def blueprintPrefix? (ctxt : TraverseContext) (d : FigureData) : Option String :=
  let mode : Informal.SubNumberingPrefix := if d.subPrefix == "first" then .first else .full
  if d.numbering == "global" then none else Informal.numberedPartPrefix? mode ctxt

/-- The HTML of a figure block; `site` is the site's render (inline pictures and explorers, the
link mode). -/
def figureHtml (st : TraverseState) (p : Placed) (idAttr : Array (String × String))
    (caption : Html) (site : Option SiteRender := none) : IO Html :=
  figureHtmlWith blueprintDeclStyle st p idAttr caption site

-- The block of a figure; `serialized` is its `FigureData` as JSON text.
block_extension Block.figure (serialized : String) where
  data := (Lean.Json.parse serialized).toOption.getD .null
  traverse id json _ := do
    traverseFigureWith blueprintPrefix? "PILeanVerso.withFigures" id json
    pure none
  toHtml := some fun _goI goB id json contents => do
    let .ok (d : FigureData) := fromJson? json
      | Verso.reportError "Malformed data of a figure block"; pure .empty
    let st ← HtmlT.state
    let some p := (Registry.get st).find? (toJson id).compress
      | Verso.reportError s!"The figure {d.decl} was not traversed"; pure .empty
    let caption ← contents.mapM goB
    let site ← (siteRef.get : IO _)
    (figureHtml st p (st.htmlId id) (.seq caption) site : IO Html)
  toTeX := some fun _goI goB _id json contents => do
    let name := match (fromJson? json : Except String FigureData) with
      | .ok d => d.decl
      | .error _ => "a figure"
    let caption ← contents.mapM goB
    pure (.seq #[.raw "\\begin{quote}\\emph{", .text s!"Figure {name}", .raw "} (in the HTML \
      version). ", .seq caption, .raw "\\end{quote}\n"])
  extraCss := [figureCss, explorerCss]
  extraJsFiles := {explorerJsFile}

/-! ### The directives -/

/-- The numbering of a Blueprint's figures: within chapters under `sub`, by one count otherwise
(also when the Blueprint names its own blocks by label, `none`), with the Blueprint's prefix. -/
def blueprintNumbering : CoreM (String × String) := do
  let opts ← getOptions
  let numbering := match Informal.numberingMode opts with
    | .sub => "sub"
    | .global | .local | .none => "global"
  let subPrefix := match Informal.subNumberingPrefix opts with
    | .first => "first"
    | .full => "full"
  return (numbering, subPrefix)

/-- How a Blueprint's figure directives differ from the Manual genre's: their block, the doc
string as the default text alternative, the Blueprint's numbering. -/
def blueprintGenre : FigureGenre :=
  { block := ``Block.figure, requireAlt := false, numbering := blueprintNumbering }

/-- The expansion of a figure directive (`explorer`: of `figure_explorer`). -/
def figureWith (explorer : Bool) : DirectiveExpanderOf FigureConfig :=
  expandFigure blueprintGenre explorer

/-- `:::figure Decl (options) caption :::` (see the module doc). -/
@[directive]
def figure : DirectiveExpanderOf FigureConfig := figureWith false

/-- `:::figure_explorer Decl (options) caption :::`: an explorer (a declaration of type
`PILean.Explorer`) with its frames inline, its controls and its script (see the module doc). -/
@[directive]
def figure_explorer : DirectiveExpanderOf FigureConfig := figureWith true

end PILeanVerso
