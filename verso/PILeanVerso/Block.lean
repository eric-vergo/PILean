/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Lean.Util.CollectAxioms
import VersoManual
import VersoBlueprint.LeanSourceAnchor
import VersoBlueprint.Informal.Block.Store
import PILean.Trust.Attr
import PILeanVerso.Render
import PILeanVerso.Style

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
* `proves := name`: a theorem about the figure. It must exist, must not depend on `sorryAx` or any
  axiom other than `propext`, `Classical.choice` and `Quot.sound`, and its statement must mention
  the figure's declaration or a declaration of the figure's module that the figure's definition
  uses directly (the theorems of PILean's exact layer speak of the series or the relation a figure
  is built from).

The figure is numbered as the Blueprint numbers its blocks (`verso.blueprint.numbering`,
`verso.blueprint.subNumberingPrefix`), with its own counter: "Figure 2.1". Its caption ends with a
line that names the declaration that made the picture and its file and line (a `lean:decl/` link
for viewers that set `data-lean-links`, a link to the repository at the build's commit when the
site has one), its fingerprint and the theorem, if any.

`{figure_list}` adds a page that lists every figure of the document with its source, fingerprint,
files and theorem; `{figref "label"}[]` refers to a figure by its label.

The pictures are written by the site build only (`PILeanVerso.withFigures`); this module reads
them from `siteRef` during traversal.
-/

namespace PILeanVerso

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre.Manual
open Lean.Doc.Syntax
open Verso.Output (Html)
open Verso.Doc.Html (HtmlT)
open PILean PILean.Trust

/-! ### What the directive records -/

/-- A declaration a figure links to: its name and where it is declared. -/
structure DeclRef where
  /-- The declaration's name. -/
  name : String
  /-- The file of its module, relative to the package's source folder. -/
  file : String
  /-- The line where it starts. -/
  line : Nat
deriving ToJson, FromJson, Inhabited, Repr

/-- The data of one figure block, recorded when the directive is elaborated. -/
structure FigureData where
  /-- The figure's declaration. -/
  decl : String
  /-- Its module. -/
  module : String
  /-- Its file, relative to the package's source folder. -/
  file : String
  /-- Its line. -/
  line : Nat
  /-- The label `figref` uses, if any. -/
  label : Option String := none
  /-- The text alternative. -/
  alt : String
  /-- The tooltip. -/
  title : String
  /-- The format of the file shown: `svg`, `png`, `apng` or `gif`. -/
  format : String := "svg"
  /-- The picture's CSS width, if given. -/
  width : Option String := none
  /-- The caption for the figures page: runs of text, and of TeX for the runs marked `true`. -/
  caption : Array (Bool × String) := #[]
  /-- The caption from the doc string, when the directive has no body. -/
  docCaption : Option String := none
  /-- The theorem about the figure, if named. -/
  proves : Option DeclRef := none
  /-- The Blueprint's numbering mode: `global` or `sub`. -/
  numbering : String := "sub"
  /-- With `sub`: `full` (the whole section path) or `first` (the chapter) as prefix. -/
  subPrefix : String := "full"
deriving ToJson, FromJson, Inhabited, Repr

/-- The parsed arguments of the directive. -/
structure FigureConfig where
  /-- The figure's declaration. -/
  decl : Ident
  /-- `label := "..."`. -/
  label : Option String
  /-- `alt := "..."`. -/
  alt : Option String
  /-- `title := "..."`. -/
  title : Option String
  /-- `format := "..."`. -/
  format : Option (ArgParse.WithSyntax String)
  /-- `width := "..."`. -/
  width : Option (ArgParse.WithSyntax String)
  /-- `proves := name`. -/
  proves : Option Ident

section
variable {m : Type → Type} [Monad m] [MonadError m]

/-- The argument parser of `figure`. -/
def FigureConfig.parse : ArgParse m FigureConfig :=
  FigureConfig.mk <$> .positional `decl .ident <*> .named `label .string true <*>
    .named `alt .string true <*> .named `title .string true <*>
    .named `format (.withSyntax .string) true <*> .named `width (.withSyntax .string) true <*>
    .named `proves .ident true

instance : FromArgs FigureConfig m := ⟨FigureConfig.parse⟩

end

/-! ### Checks made when the directive is elaborated -/

/-- The axioms a theorem about a figure may depend on. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `s` is a CSS length `figure` accepts for `width`: a number of at most six digits with
an optional fraction, then `%`, `px`, `rem`, `em`, `ch` or `vw`. -/
def isCssLength (s : String) : Bool :=
  let units := ["%", "px", "rem", "em", "ch", "vw"]
  units.any fun u =>
    s.endsWith u &&
      let n := (s.dropEnd u.length).toString
      let parts := n.splitOn "."
      !n.isEmpty && n.length ≤ 9 && parts.length ≤ 2 &&
        parts.all (fun p => p.all Char.isDigit) && !(parts.headD "").isEmpty

/-- White space runs as one space, ends trimmed. -/
def collapseSpace (s : String) : String :=
  " ".intercalate ((s.split Char.isWhitespace).toList.map (·.toString) |>.filter (!·.isEmpty))

/-- The first paragraph of a doc string as one line, at most 400 characters. -/
def docSummary (doc : String) : String :=
  let para := (doc.splitOn "\n\n").headD ""
  let s := collapseSpace para
  if s.length ≤ 400 then s else (s.take 399).toString ++ "…"

/-- Where a declaration is: its module's file and the line its range starts at (0 if unknown). -/
def declRef (n : Name) : CoreM DeclRef := do
  let env ← getEnv
  let mod := match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => env.mainModule
  let line := match ← findDeclarationRanges? n with
    | some r => r.range.pos.line
    | none => 0
  return { name := n.toString, file := moduleFile mod, line }

/-- The module a declaration is in (`none` for the current module). -/
def moduleOf? (env : Environment) (n : Name) : Option ModuleIdx := env.getModuleIdxFor? n

/-- Checks the theorem `thm` named by `proves :=` for the figure `fig` (see the module doc). -/
def checkTheorem (fig : Name) (thm : Ident) : CoreM Name := do
  let env ← getEnv
  let thmName ← realizeGlobalConstNoOverloadWithInfo thm
  let some info := env.find? thmName | throwErrorAt thm "unknown declaration {thmName}"
  unless info matches .thmInfo _ do
    throwErrorAt thm "{thmName} is not a theorem; `proves :=` names a theorem about the figure"
  let axioms ← collectAxioms thmName
  if axioms.contains ``sorryAx then
    throwErrorAt thm "{thmName} depends on `sorry`; a figure links only to a proved theorem"
  for a in axioms do
    unless standardAxioms.contains a do
      throwErrorAt thm "{thmName} depends on the axiom {a}; a figure links only to theorems \
        that use propext, Classical.choice and Quot.sound at most"
  let used := info.type.getUsedConstants
  let figValue := (env.find? fig).bind (·.value?) |>.map (·.getUsedConstants) |>.getD #[]
  let ingredients := figValue.filter fun c => moduleOf? env c == moduleOf? env fig
  unless used.contains fig || ingredients.any used.contains do
    throwErrorAt thm "{thmName} does not mention {fig} or a declaration of its module that \
      {fig} uses directly, so it is not a statement about this figure"
  return thmName

/-- The record of a declaration with `@[figure]`, or an error naming the declaration. -/
def figureRecord (decl : Ident) : CoreM (Name × FigureRecord) := do
  let n ← realizeGlobalConstNoOverloadWithInfo decl
  let some r := (registeredFigures (← getEnv)).find? (·.decl == n)
    | throwErrorAt decl "{n} does not have the attribute @[figure]; mark the declaration of the \
        picture with it (import PILean.Trust.Attr)"
  return (n, r)

/-- The runs of an inline of the body for the figures page: text, and TeX (marked `true`) for
inline and display math. -/
partial def inlineRuns (env : Environment) (stx : Syntax) : Array (Bool × String) :=
  match stx with
  | `(inline| \math code($s)) => #[(true, s.getString)]
  | `(inline| \displaymath code($s)) => #[(true, s.getString)]
  | `(inline| code($s)) => #[(false, s.getString)]
  | `(inline| role{ $_ $_* }[ $body* ]) => body.flatMap (inlineRuns env ·.raw)
  | `(inline| link[ $args* ] $_:link_target) => args.flatMap (inlineRuns env ·.raw)
  | other => #[(false, Verso.Doc.Elab.inlineToString env other)]

/-- The runs of the paragraphs of the body, white space collapsed in the text runs, adjacent text
runs joined. -/
def captionRuns (env : Environment) (blocks : Array (TSyntax `block)) : Array (Bool × String) :=
  let runs := blocks.flatMap fun b => match b with
    | `(block|para[$inlines*]) => (inlines.flatMap (inlineRuns env ·.raw)).push (false, " ")
    | _ => #[]
  let joined := runs.foldl (init := #[]) fun (acc : Array (Bool × String)) (m, t) =>
    match acc.back? with
    | some (false, prev) => if m then acc.push (m, t) else acc.pop.push (false, prev ++ t)
    | _ => acc.push (m, t)
  joined.filterMap fun (m, t) =>
    if m then some (m, t)
    else
      let c := collapseSpace t
      let c := (if t.startsWith " " || t.startsWith "\n" then " " else "") ++ c ++
        (if !c.isEmpty && (t.endsWith " " || t.endsWith "\n") then " " else "")
      if c.trimAscii.isEmpty then none else some (false, c)

/-! ### Traversal: numbers, anchors, files -/

/-- The name of the domain the figures are saved in (`figref` resolves labels there). -/
def figureDomain : Name := `PILeanVerso.figure

/-- One file of a figure as the pages show it. -/
structure FileInfo where
  /-- The path below the figures folder. -/
  path : String
  /-- The format's name. -/
  format : String
  /-- The output's name suffix: `""`, `"-dark"`, `"-poster"`. -/
  name : String
  /-- The size in bytes. -/
  bytes : Nat
  /-- The SHA-256 of the file. -/
  sha256 : String
  /-- The fingerprint recorded in it. -/
  fingerprint : String
  /-- The width and height it asks for, if known. -/
  size : Option (Nat × Nat) := none
deriving ToJson, FromJson, Inhabited, Repr

/-- What the traversal records about one figure block. -/
structure Placed where
  /-- The block's internal id, as JSON text. -/
  key : String
  /-- Its position in document order, from 1. -/
  order : Nat
  /-- Its number, such as `2.1` or `7`. -/
  number : String
  /-- The block's data. -/
  data : FigureData
  /-- The figure's files. -/
  files : Array FileInfo
  /-- The repository link of the figure's source, if the site has a repository and a commit. -/
  sourceHref : Option String := none
  /-- The repository link of the theorem, likewise. -/
  theoremHref : Option String := none
deriving ToJson, FromJson, Inhabited, Repr

/-- The figures placed so far and the counters, kept in the traversal state. -/
structure Registry where
  /-- The placed figures, in document order. -/
  placed : Array Placed := #[]
  /-- The last number given under each prefix. -/
  counters : Array (String × Nat) := #[]
deriving ToJson, FromJson, Inhabited

/-- The key of the registry in the traversal state. -/
def registryKey : Name := `PILeanVerso.figures

/-- The registry in a traversal state (empty if there is none or it cannot be read). -/
def Registry.get (st : TraverseState) : Registry :=
  match st.get? registryKey with
  | some (.ok r) => r
  | _ => {}

/-- The figure placed with the key `key`. -/
def Registry.find? (r : Registry) (key : String) : Option Placed :=
  r.placed.find? (·.key == key)

/-- A link to `file` at `line` in the site's repository at its commit, when it has both. -/
def repoHref (o : SiteOptions) (file : String) (line : Nat) : Option String := do
  let repo ← o.repo
  let commit ← o.commit
  let fragment := if line > 0 then s!"#L{line}" else ""
  safeLink? s!"{repo}/blob/{commit}/{o.sourcePrefix}{file}{fragment}"

/-- The files of a figure as the pages show them. -/
def fileInfos (f : SiteFigure) : Array FileInfo :=
  f.files.map fun sf => {
    path := sf.built.entry.path, format := sf.format.name, name := sf.name,
    bytes := sf.built.entry.bytes, sha256 := sf.built.entry.sha256,
    fingerprint := sf.built.entry.fingerprint, size := imageSize? sf.format sf.built.bytes }

/-- The data files of a figure for Verso's data directory, and the manifest. -/
def dataFiles (r : SiteRender) (f : SiteFigure) : Array DataFile :=
  let one (sf : SiteFile) : DataFile :=
    ⟨figureFolder ++ "/" ++ sf.built.entry.path, sf.built.bytes⟩
  (f.files.map one).push ⟨figureFolder ++ "/" ++ manifestName, r.manifest.toUTF8⟩

/-- The number of the next figure under `pfx`, and the registry with it counted. -/
def Registry.next (r : Registry) (pfx : String) : Nat × Registry :=
  match r.counters.findIdx? (·.1 == pfx) with
  | some i =>
    let n := r.counters[i]!.2 + 1
    (n, { r with counters := r.counters.set! i (pfx, n) })
  | none => (1, { r with counters := r.counters.push (pfx, 1) })

/-- The traversal of a figure block: its files go into the data directory, it gets its number and
anchor (once; later passes keep them), and it is saved in the domain under its label. -/
def traverseFigure (id : InternalId) (json : Lean.Json) :
    ReaderT TraverseContext (StateT TraverseState (BuildLogT IO)) Unit := do
  let .ok (d : FigureData) := fromJson? json
    | Verso.reportError "Malformed data of a figure block"
  let some site ← (siteRef.get : IO _)
    | Verso.reportError s!"The figure {d.decl} was not rendered: the site's generator must run \
        the document through PILeanVerso.withFigures"
  let some fig := site.figures[d.decl]?
    | Verso.reportError s!"The figure {d.decl} was not rendered by PILeanVerso.withFigures"
  modify fun st => st.modifyHtmlAssets fun a =>
    { a with extraDataFiles := a.extraDataFiles.insertMany (dataFiles site fig) }
  let ctxt ← read
  let key := (toJson id).compress
  let reg := Registry.get (← get)
  if (reg.find? key).isNone then
    let mode : Informal.SubNumberingPrefix := if d.subPrefix == "first" then .first else .full
    let pfx := if d.numbering == "global" then none else Informal.numberedPartPrefix? mode ctxt
    let (n, reg) := reg.next (pfx.getD "")
    let number := match pfx with
      | some p => s!"{p}.{n}"
      | none => toString n
    let placed : Placed := {
      key, order := reg.placed.size + 1, number, data := d, files := fileInfos fig,
      sourceHref := repoHref site.options d.file d.line,
      theoremHref := d.proves.bind fun t => repoHref site.options t.file t.line }
    let reg := { reg with placed := reg.placed.push placed }
    modify fun st => st.set registryKey reg
  let _ ← Verso.Genre.Manual.externalTag id ctxt.path (d.label.getD s!"figure-{d.decl}")
  if let some l := d.label then
    modify fun st => st.saveDomainObject figureDomain l id

/-! ### HTML -/

open Verso.Output.Html in
/-- The address of a file of the figures folder, from the site's root. -/
def fileUrl (path : String) : String := s!"/-verso-data/{figureFolder}/{path}"

/-- The address of a file of the figures folder relative to a page's `<base>` (for `srcset`,
which Verso does not rewrite). -/
def fileUrlRelative (path : String) : String := s!"-verso-data/{figureFolder}/{path}"

/-- The file of a figure with the format `fmt` and the name suffix `name`, if it has one. -/
def pick? (files : Array FileInfo) (fmt name : String) : Option FileInfo :=
  files.find? fun f => f.format == fmt && f.name == name

/-- The first 12 digits of a fingerprint. -/
def shortFingerprint (fp : String) : String := (fp.take 12).toString

/-- An `<img>` of a figure's file. -/
def imgTag (f : FileInfo) (cls alt title : String) (width : Option String) : Html :=
  let size := match f.size with
    | some (w, h) => #[("width", toString w), ("height", toString h)]
    | none => #[]
  let style := match width with
    | some w => #[("style", s!"width: {w}")]
    | none => #[]
  .tag "img" (#[("class", cls), ("src", fileUrl f.path), ("alt", alt), ("title", title)] ++
    size ++ style ++ #[("decoding", "async")]) .empty

/-- The pictures of a figure: the chosen format in the light theme and, when the figure has one,
the dark theme; an animation's poster frame for readers who ask for reduced motion. `none` if the
figure has no file in the chosen format. -/
def pictureHtml (p : Placed) : Option Html := do
  let d := p.data
  let light ← pick? p.files d.format ""
  let dark := pick? p.files d.format "-dark"
  let poster := pick? p.files "png" "-poster"
  let one (f : FileInfo) (cls : String) : Html :=
    let img := imgTag f s!"pilean-figure-img {cls}" d.alt d.title d.width
    match poster with
    | some pf =>
      .tag "picture" #[("class", s!"pilean-figure-motion {cls}")] (.seq #[
        .tag "source" #[("media", "(prefers-reduced-motion: reduce)"),
          ("srcset", fileUrlRelative pf.path)] .empty,
        imgTag f "pilean-figure-img" d.alt d.title d.width])
    | none => img
  match dark with
  | some df => pure (.seq #[one light "pilean-figure-light", one df "pilean-figure-dark"])
  | none => pure (one light "pilean-figure-only")

open Verso.Output.Html in
/-- A declaration as the source line shows it: a `lean:decl/` link for viewers that set
`data-lean-links`, plain code otherwise. -/
def declHtml (name : String) : Html :=
  let href := Informal.LeanSourceAnchor.declHref name.toName
  .seq #[
    {{<a class="pilean-lean-link" href={{href}}><code>{{.text true name}}</code></a>}},
    {{<code class="pilean-lean-text">{{.text true name}}</code>}}]

open Verso.Output.Html in
/-- A file and line, linked to the repository when the site has one. -/
def placeHtml (file : String) (line : Nat) (href? : Option String) : Html :=
  let text := if line > 0 then s!"{file}:{line}" else file
  match href? with
  | some href => {{<a class="pilean-repo-link" href={{href}}>{{.text true text}}</a>}}
  | none => {{<span class="pilean-place">{{.text true text}}</span>}}

open Verso.Output.Html in
/-- A fingerprint: the full digits, shown shortened, the whole on hover and when copied. -/
def fingerprintHtml (fp : String) : Html :=
  {{<code class="pilean-fingerprint" title={{fp}}>{{.text true fp}}</code>}}

open Verso.Output.Html in
/-- The source line under a figure's caption. -/
def sourceLine (p : Placed) (fp : String) : Html :=
  let d := p.data
  let thm : Html := match d.proves with
    | some t => {{<span class="pilean-source-item">
        <span class="pilean-source-key">"Proved by"</span> {{declHtml t.name}}
        {{placeHtml t.file t.line p.theoremHref}}</span>}}
    | none => .empty
  {{<span class="pilean-figure-source">
      <span class="pilean-source-item"><span class="pilean-source-key">"Source"</span>
        {{declHtml d.decl}} {{placeHtml d.file d.line p.sourceHref}}</span>
      <span class="pilean-source-item"><span class="pilean-source-key">"Fingerprint"</span>
        {{fingerprintHtml fp}}</span>
      {{thm}}
    </span>}}

/-- The fingerprint of the file a figure shows. -/
def shownFingerprint (p : Placed) : String :=
  (pick? p.files p.data.format "").map (·.fingerprint) |>.getD ""

open Verso.Output.Html in
/-- The HTML of a figure block. -/
def figureHtml (p : Placed) (idAttr : Array (String × String)) (caption : Html) : Html :=
  let d := p.data
  let hasDark := (pick? p.files d.format "-dark").isSome
  let cls := if hasDark then "pilean-figure pilean-figure-has-dark" else "pilean-figure"
  let picture := (pictureHtml p).getD
    {{<p class="pilean-figure-missing">{{.text true s!"No {d.format} file for {d.decl}."}}</p>}}
  let captionBody : Html := match d.docCaption with
    | some c => {{<span class="pilean-figure-text">{{.text true c}}</span>}}
    | none => {{<span class="pilean-figure-text">{{caption}}</span>}}
  .tag "figure" (idAttr ++ #[("class", cls), ("data-lean-decl", d.decl)]) (.seq #[
    {{<div class="pilean-figure-frame">{{picture}}</div>}},
    {{<figcaption class="pilean-figure-caption">
      <span class="pilean-figure-number">{{.text true s!"Figure {p.number}"}}</span>
      {{captionBody}}
      {{sourceLine p (shownFingerprint p)}}
    </figcaption>}}])

-- The block of a figure; `serialized` is its `FigureData` as JSON text.
block_extension Block.figure (serialized : String) where
  data := (Lean.Json.parse serialized).toOption.getD .null
  traverse id json _ := do
    traverseFigure id json
    pure none
  toHtml := some fun _goI goB id json contents => do
    let .ok (d : FigureData) := fromJson? json
      | Verso.reportError "Malformed data of a figure block"; pure .empty
    let st ← HtmlT.state
    let some p := (Registry.get st).find? (toJson id).compress
      | Verso.reportError s!"The figure {d.decl} was not traversed"; pure .empty
    let caption ← contents.mapM goB
    pure (figureHtml p (st.htmlId id) (.seq caption))
  toTeX := some fun _goI goB _id json contents => do
    let name := match (fromJson? json : Except String FigureData) with
      | .ok d => d.decl
      | .error _ => "a figure"
    let caption ← contents.mapM goB
    pure (.seq #[.raw "\\begin{quote}\\emph{", .text s!"Figure {name}", .raw "} (in the HTML \
      version). ", .seq caption, .raw "\\end{quote}\n"])
  extraCss := [figureCss]

/-! ### The directive -/

/-- `:::figure Decl (options) caption :::` (see the module doc). -/
@[directive]
def figure : DirectiveExpanderOf FigureConfig
  | cfg, contents => do
    let (decl, r) ← figureRecord cfg.decl
    let env ← getEnv
    let doc? ← findDocString? env decl
    let summary := doc?.map docSummary
    let format ← match cfg.format with
      | none => pure "svg"
      | some f =>
        if ["svg", "png", "apng", "gif"].contains f.val then pure f.val
        else throwErrorAt f.syntax "format := \"{f.val}\": expected svg, png, apng or gif"
    let width ← match cfg.width with
      | none => pure none
      | some w =>
        if isCssLength w.val then pure (some w.val)
        else throwErrorAt w.syntax "width := \"{w.val}\": expected a length such as 60%, 24rem \
          or 480px"
    if let some l := cfg.label then
      if l.isEmpty || l.length > 200 then
        throwError "label := \"{l}\": expected 1 to 200 characters"
    let proves ← match cfg.proves with
      | none => pure none
      | some t => some <$> (declRef (← checkTheorem decl t))
    let alt := match cfg.alt, summary with
      | some a, _ => a
      | none, some s => s
      | none, none => s!"Figure generated by {decl}"
    if cfg.alt.isNone && summary.isNone then
      logWarningAt cfg.decl m!"{decl} has no doc string; give the figure a text alternative with \
        (alt := \"...\")"
    let title := cfg.title.getD s!"Generated by {decl} ({r.file}:{r.line})"
    let opts ← getOptions
    let numbering := match Informal.numberingMode opts with
      | .global | .local => "global"
      | .sub => "sub"
    let subPrefix := match Informal.subNumberingPrefix opts with
      | .first => "first"
      | .full => "full"
    let data : FigureData := {
      decl := decl.toString, module := r.module.toString, file := r.file, line := r.line,
      label := cfg.label, alt, title, format, width,
      caption := if contents.isEmpty then #[(false, summary.getD "")]
        else captionRuns env contents,
      docCaption := if contents.isEmpty then summary else none,
      proves, numbering, subPrefix }
    let body ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other (Block.figure $(quote (toJson data).compress)) #[$body,*])

end PILeanVerso
