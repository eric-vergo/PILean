/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanVersoManual.Common

/-!
# Figures in Verso's Manual genre

The directive `figure` puts a PILean figure into a document of Verso's Manual genre:

```
:::figure MyManual.Figures.layers (label := "layers") (alt := "The layers of the code, ...")
The layers of the code and the imports between them.
:::
```

The first argument names a declaration with the attribute `@[figure]`. The body, which may be
empty, is the caption; an empty body takes the declaration's doc string. The named arguments:

* `alt := "..."` (required): the text alternative, what a reader who cannot see the picture
  needs to know from it.
* `label := "..."`: the name `{figref "..."}[]` refers to; it is also the figure's anchor.
* `title := "..."`: the picture's tooltip; the default names the declaration and its file.
* `format := "svg"`: the file shown: `svg` (the default), `png`, `apng` or `gif`.
* `width := "..."`: the picture's width as a CSS length (`60%`, `24rem`, `480px`).
* `backdrop := "..."`: a picture of the site (a path relative to the site's root, with `{theme}`
  standing for `light` or `dark`) that the figure is drawn over, as callouts over a screenshot:
  the backdrop carries the text alternative, the figure is laid over it at the same size.
* `inline := true`: the picture put inline as an `svg` element (with its narrow rendition, when it
  has one, on small screens), so that its titles show on hover and its elements that name a
  declaration link to it; one picture serves both themes (`PILeanVersoManual.Inline`).
* `links := name` (or `proves := name`, the same option): a theorem linked to the figure, by
  PILean's rule (`figure_links`, `PILean.Trust.figureTheoremProblem?`): it must not depend on `sorryAx` or any axiom other than
  `propext`, `Classical.choice` and `Quot.sound`, and its statement must name the figure itself
  (a statement about a definition the figure is built from is refused). A theorem about a
  function defined elsewhere is linked through a theorem that says what the figure holds and
  applies it to those values (the example's `trianglePoints_spec`).

A motion of plane figures (`PILean.Plane.Motion`, `PILean.Plane.MotionPanels`) is shown inline
by `:::figure` with its key stills and their captions (`PILeanVerso.motionHtml`); it moves only
while motion is on (`PILeanVerso.motionCss`).

`:::figure_explorer Decl …` shows an explorer (`PILean.Explorer`: a parameter axis with a slider, a
step sequence with previous, play and next, or both) with every frame inline, pan and zoom, and a
script of the site (`pilean-explorer.js`); without script the frames are listed, the poster first
in size. It takes the same options.

Figures are numbered in document order, "Figure 1", "Figure 2", …; the caption ends with a line
that names the declaration that made the picture with its file and line, the fingerprint, and the
theorem, if any. How the declaration and its place are shown is the document's choice
(`DeclStyle`, given to `PILeanVerso.Manual.withFigures`); by default the name is code and the
place links to the repository when the build has one (`--figure-repo`, `--figure-commit`).
Where the declarations link is the site's link mode (`--figure-lean-links`, `LeanLinks`; no links
by default in this genre): with `site`, a declaration documented in the manual (`{docstring}`)
links to its documentation, one that a figure draws to the figure.

`figure_explorer` on a declaration that is not a `PILean.Explorer` is an error where the
directive is; `inline := true` on a figure without an inline picture fails the site's build.

The pictures are written by the site's build only (`PILeanVerso.Manual.withFigures`); a figure's
light and dark files are shown by the stylesheet alone, following the page's `data-theme` and the
reader's system setting, with no script.
-/

namespace PILeanVerso.Manual

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre.Manual
open Verso.Output (Html)
open Verso.Doc.Html (HtmlT)
open PILean PILean.Trust
open PILeanVerso

/-- The documentation of a declaration in the manual (`{docstring}`), as a link relative to the
site's root, if the manual documents it. -/
def docstringTarget (st : TraverseState) (n : String) : Option String :=
  (st.resolveDomainObject docstringDomain n).toOption.map (·.relativeLink)

open Verso.Output.Html in
/-- The default way to show a declaration: its name as code, its file and line linked to the
repository when the build has one. -/
def defaultDeclStyle : DeclStyle where
  decl n := html%{<code class="pilean-decl">{.text n}</code>}
  place r href := placeHtml r.file r.line href
  target := docstringTarget

/-- How the document being generated shows declarations; set by `withFigures`. -/
initialize declStyleRef : IO.Ref DeclStyle ← IO.mkRef defaultDeclStyle

-- The block of a figure in the Manual genre; `serialized` is its `FigureData` as JSON text.
block_extension Block.figure (serialized : String) where
  data := (Lean.Json.parse serialized).toOption.getD .null
  traverse id json _ := do
    traverseFigureWith (fun _ _ => none) "PILeanVerso.Manual.withFigures" id json
    pure none
  toHtml := some fun _goI goB id json contents => do
    let .ok (d : FigureData) := fromJson? json
      | Verso.reportError "Malformed data of a figure block"; pure .empty
    let st ← HtmlT.state
    let some p := (Registry.get st).find? (toJson id).compress
      | Verso.reportError s!"The figure {d.decl} was not traversed"; pure .empty
    let caption ← contents.mapM goB
    let style ← (declStyleRef.get : IO DeclStyle)
    let site ← (siteRef.get : IO _)
    (figureHtmlWith style st p (st.htmlId id) (.seq caption) site : IO Html)
  toTeX := some fun _goI goB _id json contents => do
    let name := match (fromJson? json : Except String FigureData) with
      | .ok d => d.decl
      | .error _ => "a figure"
    let caption ← contents.mapM goB
    pure (.seq #[.raw "\\begin{quote}\\emph{", .text s!"Figure {name}", .raw "} (in the HTML \
      version). ", .seq caption, .raw "\\end{quote}\n"])
  extraCss := [figureCss, motionCss]

-- The block of an explorer (`figure_explorer`): the figure block with the explorers' script and
-- stylesheet, which Verso then writes into every page of the site; a site without an explorer
-- carries neither.
block_extension Block.explorer (serialized : String) where
  data := (Lean.Json.parse serialized).toOption.getD .null
  traverse := Block.figure.descr.traverse
  toHtml := Block.figure.descr.toHtml
  toTeX := Block.figure.descr.toTeX
  extraCss := [figureCss, explorerCss]
  extraJsFiles := {explorerJsFile}

/-- How this genre's figure directives differ from the Blueprint's: their block, a required
text alternative, one counter for the document. -/
def manualGenre : FigureGenre :=
  { block := ``Block.figure, explorerBlock := ``Block.explorer, requireAlt := true }

/-- The expansion of a figure directive (`explorer`: of `figure_explorer`). -/
def figureWith (explorer : Bool) : DirectiveExpanderOf FigureConfig :=
  expandFigure manualGenre explorer

/-- `:::figure Decl (alt := "...") (options) caption :::` (see the module doc). -/
@[directive]
def figure : DirectiveExpanderOf FigureConfig := figureWith false

/-- `:::figure_explorer Decl (alt := "...") (options) caption :::`: an explorer (a declaration of
type `PILean.Explorer`) with its frames inline and its controls (see the module doc). -/
@[directive]
def figure_explorer : DirectiveExpanderOf FigureConfig := figureWith true

end PILeanVerso.Manual
