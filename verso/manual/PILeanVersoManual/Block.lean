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
* `proves := name`: a theorem about the figure, by PILean's rule (`figure_proves`,
  `PILean.Trust.figureTheoremProblem?`): it must not depend on `sorryAx` or any axiom other than
  `propext`, `Classical.choice` and `Quot.sound`, and its statement must mention the figure or a
  declaration of the figure's module that the figure uses directly. A theorem about a function
  defined elsewhere is linked through a theorem of the figure's module that applies it to the
  values the figure draws (the example's `trianglePoints_spec`).

Figures are numbered in document order, "Figure 1", "Figure 2", …; the caption ends with a line
that names the declaration that made the picture with its file and line, the fingerprint, and the
theorem, if any. How the declaration and its place are shown is the document's choice
(`DeclStyle`, given to `PILeanVerso.Manual.withFigures`); by default the name is code and the
place links to the repository when the build has one (`--figure-repo`, `--figure-commit`).

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

open Verso.Output.Html in
/-- The default way to show a declaration: its name as code, its file and line linked to the
repository when the build has one. -/
def defaultDeclStyle : DeclStyle where
  decl n := {{<code class="pilean-decl">{{.text true n}}</code>}}
  place r href := placeHtml r.file r.line href

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
    pure (figureHtmlWith style p (st.htmlId id) (.seq caption))
  toTeX := some fun _goI goB _id json contents => do
    let name := match (fromJson? json : Except String FigureData) with
      | .ok d => d.decl
      | .error _ => "a figure"
    let caption ← contents.mapM goB
    pure (.seq #[.raw "\\begin{quote}\\emph{", .text s!"Figure {name}", .raw "} (in the HTML \
      version). ", .seq caption, .raw "\\end{quote}\n"])
  extraCss := [figureCss]

/-- `:::figure Decl (alt := "...") (options) caption :::` (see the module doc). -/
@[directive]
def figure : DirectiveExpanderOf FigureConfig
  | cfg, contents => do
    let (decl, r) ← figureRecord cfg.decl
    let env ← getEnv
    let some alt := cfg.alt
      | throwErrorAt cfg.decl "give the figure {decl} a text alternative, (alt := \"...\"): what \
          a reader who cannot see the picture needs to know from it"
    if alt.trimAscii.isEmpty || alt.length > 2000 then
      throwErrorAt cfg.decl "alt := \"{alt}\": expected 1 to 2000 characters"
    let (format, width, backdrop) ← checkOptions cfg
    let summary := (← findDocString? env decl).map docSummary
    if contents.isEmpty && summary.isNone then
      throwErrorAt cfg.decl "{decl} has no doc string: give the figure a caption (the body of the \
        directive) or the declaration a doc string"
    let proves ← match cfg.proves with
      | none => pure none
      | some t => some <$> (declRef (← checkTheorem decl t))
    let title := cfg.title.getD s!"Generated by {decl} ({r.file}:{r.line})"
    let data : FigureData := {
      decl := decl.toString, module := r.module.toString, file := r.file, line := r.line,
      label := cfg.label, alt, title, format, width, backdrop,
      caption := if contents.isEmpty then #[(false, summary.getD "")]
        else captionRuns env contents,
      docCaption := if contents.isEmpty then summary else none,
      proves, numbering := "global" }
    let body ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.figure $(quote (toJson data).compress)) #[$body,*])

end PILeanVerso.Manual
