/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILean.Trust.Attr
import PILeanVersoManual.Render
import PILeanVersoManual.Style
import PILeanVersoManual.Inline

/-!
# The parts every figure block shares

A figure block of a Verso document, whichever genre's numbering it follows, records the same
data when its directive is elaborated, makes the same checks, keeps its number and files in the
same registry of the traversal state and is written with the same HTML. This module holds those
parts; `PILeanVersoManual.Block` (Verso's Manual genre) and `PILeanVerso.Block` (Verso Blueprint)
add the numbering and the way a declaration's name is shown.

## Main definitions

* `FigureData`, `FigureConfig`: what a figure block records, and its directive's arguments
* `checkTheorem`: the check of the theorem named by `proves :=` (PILean's own rule)
* `expandFigure`: the expansion of the directives `figure` and `figure_explorer`
* `Placed`, `Registry`, `traverseFigureWith`: numbers, anchors and files during traversal
* `DeclStyle`, `Links`: how a document shows declarations and where their links lead
* `figureHtmlWith`, `figureListHtmlWith`, `figrefHtml`: the HTML of a figure, of the figures page
  and of a reference to a figure
* `pageSlug`, `traversePageWith`, `pageLink?`: the addresses of the figures' pages
  (the pages themselves are `PILeanVersoManual.Page`, the wrapper `PILeanVersoManual.Wrapper`)
-/

namespace PILeanVerso

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre.Manual
open Lean.Doc.Parser
open Verso.Output (Html)
open PILean PILean.Trust

/-! ### What the directive records -/

/-- A declaration a figure links to: its name and where it is declared. -/
structure DeclRef where
  /-- The declaration's name. -/
  name : String
  /-- The name of its module. -/
  module : String := ""
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
  /-- A picture of the site the figure is drawn over (`backdropUrl` gives its address in each
  theme), if any. -/
  backdrop : Option String := none
  /-- The caption for the figures page: runs of text, and of TeX for the runs marked `true`. -/
  caption : Array (Bool × String) := #[]
  /-- The caption from the doc string, when the directive has no body. -/
  docCaption : Option String := none
  /-- The theorem about the figure, if named. -/
  proves : Option DeclRef := none
  /-- The numbering: `global` (one counter for the document) or `sub` (a counter below the
  enclosing part's number). -/
  numbering : String := "sub"
  /-- With `sub`: `full` (the whole section path) or `first` (the chapter) as prefix. -/
  subPrefix : String := "full"
  /-- Whether the picture is put inline as an `svg` element (`inline := true`). -/
  inline : Bool := false
  /-- Whether the figure is an explorer (`figure_explorer`): its frames inline, with controls. -/
  explorer : Bool := false
deriving ToJson, FromJson, Inhabited, Repr

/-- The parsed arguments of a figure directive. -/
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
  /-- `backdrop := "..."`. -/
  backdrop : Option (ArgParse.WithSyntax String)
  /-- `inline := true`. -/
  inline : Option Bool

section
variable {m : Type → Type} [Monad m] [MonadError m] [MonadLiftT CoreM m]

/-- The argument parser of a figure directive. -/
def FigureConfig.parse : ArgParse m FigureConfig :=
  FigureConfig.mk <$> .positional `decl .ident <*> .named `label .string true <*>
    .named `alt .string true <*> .named `title .string true <*>
    .named `format (.withSyntax .string) true <*> .named `width (.withSyntax .string) true <*>
    .named `proves .ident true <*> .named `backdrop (.withSyntax .string) true <*>
    .named `inline .bool true

instance : FromArgs FigureConfig m := ⟨FigureConfig.parse⟩

end

/-! ### Checks made when the directive is elaborated -/

/-- Whether `s` is a CSS length a figure accepts for `width`: a number of at most six digits with
an optional fraction, then `%`, `px`, `rem`, `em`, `ch` or `vw`. -/
def isCssLength (s : String) : Bool :=
  let units := ["%", "px", "rem", "em", "ch", "vw"]
  units.any fun u =>
    s.endsWith u &&
      let n := (s.dropEnd u.length).toString
      let parts := n.splitOn "."
      !n.isEmpty && n.length ≤ 9 && parts.length ≤ 2 &&
        parts.all (fun p => p.all Char.isDigit) && !(parts.headD "").isEmpty

/-- Whether `s` is a backdrop a figure accepts: a relative path of the site of at most 200
characters, in components of letters, digits, `-`, `_` and `.` (none of them `.` or `..`),
separated by `/`, in which `{theme}` may stand for `light` or `dark`. -/
def validBackdrop (s : String) : Bool :=
  let plain := (s.replace "{theme}" "x")
  let comps := plain.splitOn "/"
  !s.isEmpty && s.length ≤ 200 && !s.startsWith "/" &&
    comps.all fun c => !c.isEmpty && c != "." && c != ".." &&
      c.all fun ch => ch.isAlphanum || ch == '-' || ch == '_' || ch == '.'

/-- The address of a backdrop in a theme (`light` or `dark`): `{theme}` replaced by it. -/
def backdropUrl (b theme : String) : String := b.replace "{theme}" theme

/-- Whether a backdrop has a picture for each theme (it contains `{theme}`). -/
def backdropThemed (b : String) : Bool := (b.splitOn "{theme}").length > 1

/-- White space runs as one space, ends trimmed. -/
def collapseSpace (s : String) : String :=
  " ".intercalate ((s.split Char.isWhitespace).toList.map (·.toString) |>.filter (!·.isEmpty))

/-- The first paragraph of a doc string as one line, at most 400 characters. -/
def docSummary (doc : String) : String :=
  let para := (doc.splitOn "\n\n").headD ""
  let s := collapseSpace para
  if s.length ≤ 400 then s else (s.take 399).toString ++ "…"

/-- Where a declaration is: its module, the module's file and the line its range starts at (0 if
unknown). -/
def declRef (n : Name) : CoreM DeclRef := do
  let env ← getEnv
  let mod := match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => env.mainModule
  let line := match ← findDeclarationRanges? n with
    | some r => r.range.pos.line
    | none => 0
  return { name := n.toString, module := mod.toString, file := moduleFile mod, line }

/-- The module a declaration is in (`none` for the current module). -/
def moduleOf? (env : Environment) (n : Name) : Option ModuleIdx := env.getModuleIdxFor? n

/-- Checks the theorem `thm` named by `proves :=` for the figure `fig`, by PILean's own rule
(`PILean.Trust.figureTheoremProblem?`, the check of `figure_proves`): it is a theorem, depends on
no `sorry` and no axiom beyond `propext`, `Classical.choice` and `Quot.sound`, and its statement
names `fig` itself (a statement about a definition `fig` is built from is refused). A theorem
about a function the figure calls from elsewhere is linked through a theorem that says what the
figure holds and applies it to those values. -/
def checkTheorem (fig : Name) (thm : Ident) : CoreM Name := do
  let thmName ← realizeGlobalConstNoOverloadWithInfo thm
  if let some msg ← figureTheoremProblem? fig thmName then throwErrorAt thm msg
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
partial def inlineRuns (env : Environment) (stx : Lean.Doc.VersoInline) : Array (Bool × String) :=
  match Lean.Doc.InlineView.of stx with
  | some (.math v) => #[(true, v.getVersoCode)]
  | some (.code v) => #[(false, v.getVersoCode)]
  | some (.role v) =>
    if v.brackets.isSome then v.content.flatMap (inlineRuns env)
    else #[(false, Verso.Doc.Elab.inlineToString env stx)]
  | some (.link v) => v.content.flatMap (inlineRuns env)
  | _ => #[(false, Verso.Doc.Elab.inlineToString env stx)]

/-- The runs of the paragraphs of the body, white space collapsed in the text runs, adjacent text
runs joined. -/
def captionRuns (env : Environment) (blocks : Array Lean.Doc.VersoBlock) : Array (Bool × String) :=
  let runs := blocks.flatMap fun b => match Lean.Doc.BlockView.of b with
    | some (.para v) => (v.content.flatMap (inlineRuns env)).push (false, " ")
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

/-- The checks of the options `format`, `width`, `label` and `backdrop`, with their values:
the format (`svg` by default), the width and the backdrop, if given. -/
def checkOptions (cfg : FigureConfig) : CoreM (String × Option String × Option String) := do
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
  let backdrop ← match cfg.backdrop with
    | none => pure none
    | some b =>
      if validBackdrop b.val then pure (some b.val)
      else throwErrorAt b.syntax "backdrop := \"{b.val}\": expected a relative path of the \
        site such as \"shots/editor-\{theme}.png\""
  return (format, width, backdrop)

/-- Why `decl` cannot be shown by `figure_explorer`, if it cannot: its type must be
`PILean.Explorer`. -/
def explorerProblem? (decl : Name) : CoreM (Option MessageData) := do
  let ty := (← getConstInfo decl).type
  if ty.isConstOf `PILean.Explorer then return none
  return some m!"{decl} has the type {ty}, not PILean.Explorer: figure_explorer shows an \
    explorer (made with Plane.slider, Plane.stepper or Explorer.grid); use figure for a picture"

/-- How the directives of one genre differ: the block a figure becomes, whether `alt` must be
given, and the numbering of the figures (`numbering` and `subPrefix` of `FigureData`). -/
structure FigureGenre where
  /-- The constant of the genre's figure block, applied to the block's data as JSON text. -/
  block : Name
  /-- Whether the directive must give `alt` and the figure a caption or a doc string; otherwise
  the doc string is the default text alternative, with a warning when there is none. -/
  requireAlt : Bool
  /-- The numbering and the numbering's prefix of the figures. -/
  numbering : CoreM (String × String) := pure ("global", "full")

/-- The message of a figure without a text alternative. -/
def altMissing (decl : Name) : MessageData :=
  m!"give the figure {decl} a text alternative, (alt := \"...\"): what a reader who cannot see \
    the picture needs to know from it"

/-- The expansion of a figure directive (`explorer`: of `figure_explorer`) in the genre `g`. -/
def expandFigure (g : FigureGenre) (explorer : Bool) : DirectiveExpanderOf FigureConfig
  | cfg, contents => do
    let (decl, r) ← figureRecord cfg.decl
    let env ← getEnv
    if explorer then
      if let some why ← explorerProblem? decl then throwErrorAt cfg.decl why
    let summary := (← findDocString? env decl).map docSummary
    let alt ← match cfg.alt, summary with
      | some a, _ => pure a
      | none, some s => if g.requireAlt then throwErrorAt cfg.decl (altMissing decl) else pure s
      | none, none =>
        if g.requireAlt then throwErrorAt cfg.decl (altMissing decl)
        logWarningAt cfg.decl m!"{decl} has no doc string; give the figure a text \
          alternative with (alt := \"...\")"
        pure s!"Figure generated by {decl}"
    if alt.trimAscii.isEmpty || alt.length > 2000 then
      throwErrorAt cfg.decl "alt := \"{alt}\": expected 1 to 2000 characters"
    let (format, width, backdrop) ← checkOptions cfg
    if g.requireAlt && contents.isEmpty && summary.isNone then
      throwErrorAt cfg.decl "{decl} has no doc string: give the figure a caption (the body of the \
        directive) or the declaration a doc string"
    let proves ← match cfg.proves with
      | none => pure none
      | some t => some <$> (declRef (← checkTheorem decl t))
    let title := cfg.title.getD s!"Generated by {decl} ({r.file}:{r.line})"
    let (numbering, subPrefix) ← g.numbering
    let data : FigureData := {
      decl := decl.toString, module := r.module.toString, file := r.file, line := r.line,
      label := cfg.label, alt, title, format, width, backdrop,
      caption := if contents.isEmpty then #[(false, summary.getD "")]
        else captionRuns env contents,
      docCaption := if contents.isEmpty then summary else none,
      proves, numbering, subPrefix, inline := cfg.inline.getD false, explorer }
    let body ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other ($(mkCIdent g.block) $(quote (toJson data).compress)) #[$body,*])

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

/-- What the traversal records about one figure's page. -/
structure PagePlaced where
  /-- The figure's declaration. -/
  decl : String
  /-- The page block's internal id, as JSON text. -/
  key : String
  /-- The path of the page's file, as Verso's traversal gives it. -/
  path : Array String
deriving ToJson, FromJson, Inhabited, Repr

/-- The figures placed so far and the counters, kept in the traversal state. -/
structure Registry where
  /-- The placed figures, in document order. -/
  placed : Array Placed := #[]
  /-- The figures' pages. -/
  pages : Array PagePlaced := #[]
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
anchor (once; later passes keep them), and it is saved in the domain under its label. `prefix?`
gives the part number its number goes below (`none`: the document's own counter); `wrapper`
names the generator wrapper in the messages. -/
def traverseFigureWith (prefix? : TraverseContext → FigureData → Option String)
    (wrapper : String) (id : InternalId) (json : Lean.Json) :
    ReaderT TraverseContext (StateT TraverseState (BuildLogT IO)) Unit := do
  let .ok (d : FigureData) := fromJson? json
    | Verso.reportError "Malformed data of a figure block"
  let some site ← (siteRef.get : IO _)
    | Verso.reportError s!"The figure {d.decl} was not rendered: the site's generator must run \
        the document through {wrapper}"
  let some fig := site.figures[d.decl]?
    | Verso.reportError s!"The figure {d.decl} was not rendered by {wrapper}"
  modify fun st => st.modifyHtmlAssets fun a =>
    { a with extraDataFiles := a.extraDataFiles.insertMany (dataFiles site fig) }
  let ctxt ← read
  let key := (toJson id).compress
  let reg := Registry.get (← get)
  if (reg.find? key).isNone then
    let pfx := prefix? ctxt d
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

/-- The address of a figure's page in the site, from its declaration's name: the name with
every character outside `[A-Za-z0-9._-]` replaced by `_` (and a leading `.` too), cut to 100
characters, and, when that changed the name, `-` and the first 12 digits of the name's SHA-256
after it, so that two names never share a page. -/
def pageSlug (decl : String) : String :=
  let clean := String.ofList (decl.toList.map fun c =>
    if c.toNat < 128 && (c.isAlphanum || c == '.' || c == '_' || c == '-') then c else '_')
  let cut := (clean.take 100).toString
  let cut := if cut.startsWith "." then "_" ++ (cut.drop 1).toString else cut
  if cut == decl then cut else s!"{cut}-{(Sha256.hex (Sha256.hash decl.toUTF8)).take 12}"

/-- The traversal of a figure's page block: it gets its anchor (once) and is recorded with the
path of its file. -/
def traversePageWith (id : InternalId) (json : Lean.Json) :
    ReaderT TraverseContext (StateT TraverseState (BuildLogT IO)) Unit := do
  let .str decl := json | Verso.reportError "Malformed data of a figure's page"
  let ctxt ← read
  let key := (toJson id).compress
  let reg := Registry.get (← get)
  if !reg.pages.any (·.key == key) then
    let reg := { reg with pages := reg.pages.push { decl, key, path := ctxt.path } }
    modify fun st => st.set registryKey reg
  let _ ← Verso.Genre.Manual.externalTag id ctxt.path s!"figure-page-{pageSlug decl}"

/-- The link to the page of the figure `decl`, relative to the site's root, if it has one. -/
def pageLink? (st : TraverseState) (decl : String) : Option String := do
  let pp ← (Registry.get st).pages.find? (·.decl == decl)
  let .ok (id : InternalId) := Lean.Json.parse pp.key >>= fromJson? | none
  let link ← st.resolveId id
  pure link.relativeLink

/-! ### HTML -/

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
  .element "img" (#[("class", cls), ("src", fileUrl f.path), ("alt", alt), ("title", title)] ++
    size ++ style ++ #[("decoding", "async")]) .empty

/-- The pictures of a figure: the chosen format in the light theme and, when the figure has one,
the dark theme; an animation's poster frame for readers who ask for reduced motion. With a
backdrop, the figure is drawn over the backdrop's picture of the same theme, and the backdrop's
picture carries the text alternative. `none` if the figure has no file in the chosen format. -/
def pictureHtml (p : Placed) : Option Html := do
  let d := p.data
  let light ← pick? p.files d.format ""
  let dark := pick? p.files d.format "-dark"
  let poster := pick? p.files "png" "-poster"
  let alt := if d.backdrop.isSome then "" else d.alt
  let narrowOf := fun (f : FileInfo) => pick? p.files d.format (if f.name == "-dark" then
    "-narrow-dark" else "-narrow")
  let one (f : FileInfo) (cls : String) : Html :=
    let img := match narrowOf f with
      | some nf =>
        .element "picture" #[("class", s!"pilean-figure-motion {cls}")] (.seq #[
          .element "source" #[("media", "(max-width: 560px)"),
            ("srcset", fileUrlRelative nf.path)] .empty,
          imgTag f "pilean-figure-img" alt d.title d.width])
      | none => imgTag f s!"pilean-figure-img {cls}" alt d.title d.width
    match poster with
    | some pf =>
      .element "picture" #[("class", s!"pilean-figure-motion {cls}")] (.seq #[
        .element "source" #[("media", "(prefers-reduced-motion: reduce)"),
          ("srcset", fileUrlRelative pf.path)] .empty,
        imgTag f "pilean-figure-img" alt d.title d.width])
    | none => img
  let pics := match dark with
    | some df => Html.seq #[one light "pilean-figure-light", one df "pilean-figure-dark"]
    | none => one light "pilean-figure-only"
  match d.backdrop with
  | none => pure pics
  | some b =>
    let back (theme cls : String) : Html :=
      .element "img" #[("class", s!"pilean-backdrop-img {cls}"), ("src", backdropUrl b theme),
        ("alt", d.alt), ("decoding", "async")] .empty
    let backs := if backdropThemed b then
        Html.seq #[back "light" "pilean-figure-light", back "dark" "pilean-figure-dark"]
      else back "light" "pilean-figure-only"
    let style := match d.width with
      | some w => #[("style", s!"width: {w}")]
      | none => #[]
    pure (.element "div" (#[("class", "pilean-figure-stack")] ++ style) (.seq #[backs,
      .element "div" #[("class", "pilean-figure-over"), ("aria-hidden", "true")] pics]))

open Verso.Output.Html in
/-- A file and line, linked to the repository when the site has one. -/
def placeHtml (file : String) (line : Nat) (href? : Option String) : Html :=
  let text := if line > 0 then s!"{file}:{line}" else file
  match href? with
  | some href => html%{<a class="pilean-repo-link" href={href}>{.text text}</a>}
  | none => html%{<span class="pilean-place">{.text text}</span>}

open Verso.Output.Html in
/-- A fingerprint: the full digits, shown shortened, the whole on hover and when copied. -/
def fingerprintHtml (fp : String) : Html :=
  html%{<code class="pilean-fingerprint" title={fp}>{.text fp}</code>}

/-- The fingerprint of the file a figure shows. -/
def shownFingerprint (p : Placed) : String :=
  (pick? p.files p.data.format "").map (·.fingerprint) |>.getD ""

/-- How a document shows a declaration a figure names: `decl` gives the declaration's name as
the source line shows it, `place` its file and line (with the repository link of the site's
options, if any), and `target` the declaration's own place in the document for the link mode
`site` (`LeanLinks`), if it has one: a Blueprint entry, a docstring. The figure a declaration
draws is its place too, without `target` saying so. -/
structure DeclStyle where
  /-- The declaration's name. -/
  decl : String → Html
  /-- The file and line of a declaration, and the repository link the traversal computed. -/
  place : DeclRef → Option String → Html
  /-- The declaration's place in the document, as a link relative to the site's root. -/
  target : TraverseState → String → Option String := fun _ _ => none

instance : Inhabited DeclStyle := ⟨{ decl := fun _ => .empty, place := fun _ _ => .empty }⟩

/-- Whether a character is left as it is in a `lean:decl/` link. -/
def declLinkChar (c : Char) : Bool :=
  c.toNat < 128 && (c.isAlphanum || c == '.' || c == '_' || c == '~' || c == '-' || c == '\'' ||
    c == '!' || c == '/' || c == ':')

/-- The `lean:decl/<Name>` link of a declaration, everything outside `declLinkChar`
percent-encoded as UTF-8 (the form Verso Blueprint's Lean anchors use). -/
def leanDeclHref (name : String) : String :=
  let hex := fun (n : Nat) => Char.ofNat (if n < 10 then 48 + n else 55 + n)
  "lean:decl/" ++ name.foldl (init := "") fun out c =>
    if declLinkChar c then out.push c
    else (String.singleton c).toUTF8.foldl (init := out) fun out b =>
      ((out.push '%').push (hex (b.toNat / 16))).push (hex (b.toNat % 16))

/-- A link to the figure placed as `p`, relative to the site's root, if the traversal gave it an
anchor. -/
def placedLink? (st : TraverseState) (p : Placed) : Option String := do
  let .ok (id : InternalId) := Lean.Json.parse p.key >>= fromJson? | none
  let link ← st.resolveId id
  pure link.relativeLink

/-- Where the pages being written link declarations: the mode, and in the mode `site` the place
of each declaration that has one. -/
structure Links where
  /-- The mode. -/
  mode : LeanLinks
  /-- The place of a declaration in the site. -/
  place : String → Option String

/-- The links of a document: the site's mode (`ideil` without a rendered site), the document's
places of declarations (`DeclStyle.target`), then the figures they draw. -/
def Links.of (s : DeclStyle) (st : TraverseState) (site : Option SiteRender) : Links :=
  let placed := (Registry.get st).placed.qsort (·.order < ·.order)
  { mode := (site.map (·.options.leanLinks)).getD .ideil,
    place := fun n => s.target st n <|>
      placed.findSome? fun p => if p.data.decl == n then placedLink? st p else none }

/-- The link of the declaration `n`, if the mode gives it one; in the mode `site`, a declaration
without a place is recorded in `unlinkedRef` (the build warns about it) unless `here` says the
reader is at its place already (the figure it draws). -/
def Links.href (l : Links) (n : String) (here : Option String := none) : IO (Option String) :=
  match l.mode with
  | .ideil => pure (some (leanDeclHref n))
  | .none => pure none
  | .site => match l.place n with
    | some h => pure (if some h == here then none else some h)
    | none => do unlinkedRef.modify (·.insert n); pure none

open Verso.Output.Html in
/-- A declaration as a page shows it with its link (`Links.href`): in the mode `ideil` a
`lean:decl/` link shown only when the page's root has `data-lean-links`, with the plain name
otherwise; in the mode `site` a link into the site; else the name alone. -/
def declLinkHtml (s : DeclStyle) (l : Links) (n : String) (here : Option String := none) :
    IO Html := do
  match ← l.href n here with
  | none => pure (s.decl n)
  | some h =>
    if l.mode == .ideil then
      pure (.seq #[html%{<a class="pilean-lean-link" href={h}>{s.decl n}</a>},
        html%{<span class="pilean-lean-text">{s.decl n}</span>}])
    else pure html%{<a class="pilean-site-link" href={h}>{s.decl n}</a>}

open Verso.Output.Html in
/-- The source line under a figure's caption; the figure's own declaration gets no link to the
figure itself (`here`). -/
def sourceLineWith (s : DeclStyle) (l : Links) (st : TraverseState) (p : Placed) (fp : String)
    (here : Option String := none) : IO Html := do
  let d := p.data
  let thm : Html ← match d.proves with
    | some t => pure html%{<span class="pilean-source-item">
        <span class="pilean-source-key">{"Theorem"}</span>{← declLinkHtml s l t.name}
        {s.place t p.theoremHref}</span>}
    | none => pure .empty
  let src : DeclRef := { name := d.decl, module := d.module, file := d.file, line := d.line }
  let pageItem : Html := match pageLink? st d.decl with
    | some h => html%{<span class="pilean-source-item"><span class="pilean-source-key">{"Page"}</span>
        <a class="pilean-page-link" href={h}>{"code, standing and provenance"}</a></span>}
    | none => .empty
  pure html%{<span class="pilean-figure-source">
      <span class="pilean-source-item"><span class="pilean-source-key">{"Source"}</span>
        {← declLinkHtml s l d.decl here}{s.place src p.sourceHref}</span>
      <span class="pilean-source-item"><span class="pilean-source-key">{"Fingerprint"}</span>
        {fingerprintHtml fp}</span>
      {thm}
      {pageItem}
    </span>}

open Verso.Genre.Manual in
/-- The script of explorers (`explorerJs`) as a file of the site, `pilean-explorer.js`, loaded
deferred. -/
def explorerJsFile : JsFile :=
  { filename := "pilean-explorer.js", defer := true, contents := ⟨explorerJs⟩, sourceMap? := none }

/-- The id a figure's elements are named after: its anchor's id, or one from its declaration and
its place in the document. -/
def figureDomId (p : Placed) (idAttr : Array (String × String)) : String :=
  match idAttr.find? (·.1 == "id") with
  | some (_, v) => v
  | none => s!"pilean-figure-{p.order}"

/-- The declarations the elements of an inline picture name (`data-lean-decl`), in document
order. -/
partial def nodeDecls : Svg.Node → Array String
  | .text _ => #[]
  | .element _ attrs kids =>
    let own := (attrs.find? (·.1 == "data-lean-decl")).map (·.2) |>.toArray
    own ++ kids.flatMap nodeDecls

/-- The links of the declarations the pictures `is` name, as a function for `prefixNode`. -/
def pictureLinks (l : Links) (is : Array InlineSvg) : IO (String → Option String) := do
  let names := (is.flatMap fun i => i.nodes.flatMap nodeDecls).foldl (init := #[])
    fun acc n => if acc.contains n then acc else acc.push n
  let mut m : Std.HashMap String String := {}
  for n in names do
    if let some h ← l.href n then m := m.insert n h
  return fun n => m[n]?

/-- The inline markup of a figure (`inline := true`, and explorers), from the site's render: the
picture (and its narrow rendition, shown on small screens) as `svg` elements, or an explorer's
frames and controls; `none` when the figure is shown as files. Each picture names its file. -/
def inlinePicture? (l : Links) (site : Option SiteRender) (p : Placed)
    (idAttr : Array (String × String)) : IO (Option Html) := do
  let d := p.data
  if !d.inline && !d.explorer then return none
  let base := figureDomId p idAttr
  let some site := site | return none
  let some fig := site.figures[d.decl]? | return none
  let file := fun (name : String) => fig.files.find? fun f => f.format == .svg && f.name == name
  let path := fun (name : String) => (file name).map (·.built.entry.path)
  if d.explorer then
    let some f := file "" | return none
    let some fs := f.frames | return none
    let href ← pictureLinks l fs.frames
    return some (.raw (explorerHtml s!"{base}-x" fs href d.alt s!"Figure {p.number}"
      (fun k => path s!"-frame-{k}")))
  let some f := file "" | return none
  let some i := f.inline | return none
  let narrow := (file "-narrow").bind (·.inline)
  let href ← pictureLinks l (#[i] ++ narrow.toArray)
  let wide := inlineSvgText s!"{base}-svg" i href d.alt (file := path "")
  match narrow with
  | some n =>
    let narrow := inlineSvgText s!"{base}-svg-narrow" n href d.alt (file := path "-narrow")
    return some (.element "div" #[("class", "pilean-has-narrow")] (.seq #[
      .element "div" #[("class", "pilean-inline-frame pilean-inline-wide")] (.raw wide),
      .element "div" #[("class", "pilean-inline-frame pilean-inline-narrow")] (.raw narrow)]))
  | none => return some (.element "div" #[("class", "pilean-inline-frame")] (.raw wide))

open Verso.Output.Html in
/-- The HTML of a figure block; `site` is the site's render, which inline pictures and explorers
are read from and which sets the link mode. -/
def figureHtmlWith (s : DeclStyle) (st : TraverseState) (p : Placed)
    (idAttr : Array (String × String)) (caption : Html) (site : Option SiteRender := none) :
    IO Html := do
  let d := p.data
  let l := Links.of s st site
  let hasDark := (pick? p.files d.format "-dark").isSome ||
    (d.backdrop.map backdropThemed).getD false
  let cls := if hasDark then "pilean-figure pilean-figure-has-dark" else "pilean-figure"
  let picture := match ← inlinePicture? l site p idAttr with
    | some h => h
    | none => (pictureHtml p).getD
      html%{<p class="pilean-figure-missing">{.text s!"No {d.format} file for {d.decl}."}</p>}
  let captionBody : Html := match d.docCaption with
    | some c => html%{<span class="pilean-figure-text">{.text c}</span>}
    | none => html%{<span class="pilean-figure-text">{caption}</span>}
  let capId := s!"{figureDomId p idAttr}-caption"
  let cls := if d.explorer then cls ++ " pilean-figure-explorer" else cls
  let role := if d.explorer then #[("role", "group"), ("aria-labelledby", capId)] else #[]
  let source ← sourceLineWith s l st p (shownFingerprint p) (here := placedLink? st p)
  pure <| .element "figure" (idAttr ++ #[("class", cls), ("data-lean-decl", d.decl)] ++ role)
    (.seq #[
      html%{<div class="pilean-figure-frame">{picture}</div>},
      .element "figcaption" #[("class", "pilean-figure-caption"), ("id", capId)] (.seq #[
        html%{<span class="pilean-figure-number">{.text s!"Figure {p.number}"}</span>},
        captionBody, source])])

/-! ### The figures page and references -/

/-- The words of a figure's standing, as its page and the figures page say them first. -/
def standingWords (s : Standing) : String :=
  match s with
  | .proved #[_] => "Tied to its object by the theorem"
  | .proved _ => "Tied to its object by the theorems"
  | .illustration _ => "Illustration: not tied to a Lean object by a theorem"

open Verso.Output.Html in
/-- The standing of the figure `decl` in the figures page's list: the words of `standingWords`
and, for a proved figure, each theorem with its link and place. -/
def standingSummaryHtml (s : DeclStyle) (l : Links) (site : Option SiteRender) (decl : String) :
    IO Html := do
  let some fig := site.bind (·.figures[decl]?)
    | return html%{<dt>{"Standing"}</dt><dd>{"not rendered"}</dd>}
  let page := site.bind (·.pages[decl]?)
  let thms ← fig.standing.theorems.mapM fun t => do
    let place : Html := match page.bind (·.theorems.find? (·.decl.name == t)) with
      | some ti =>
        let r : DeclRef := { name := t, module := ti.decl.module, file := ti.decl.file,
                             line := ti.decl.line }
        s.place r (site.bind fun x => repoHref x.options r.file r.line)
      | none => .empty
    pure html%{<span class="pilean-standing-theorem">{← declLinkHtml s l t}{place}</span>}
  let cls := s!"pilean-standing pilean-standing-{fig.standing.word}"
  pure html%{<dt>{"Standing"}</dt><dd class={cls}>{.text (standingWords fig.standing)}
    {if thms.isEmpty then Html.empty else .seq (#[Html.text " "] ++ thms)}</dd>}

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

open Verso.Output.Html in
/-- One entry of the figures page; `math` is the class of a run of TeX in the caption. -/
def indexEntryWith (s : DeclStyle) (l : Links) (math : String) (st : TraverseState)
    (site : Option SiteRender) (p : Placed) : IO Html := do
  let d := p.data
  let href := (placedLink? st p).getD "#"
  let thumb := match pick? p.files "svg" "" <|> pick? p.files "png" "" with
    | some f =>
      let img := imgTag f "pilean-index-img" (if d.backdrop.isSome then "" else d.alt) d.title none
      let inner := match d.backdrop with
        | some b => Html.element "span" #[("class", "pilean-index-stack")] (.seq #[
            .element "img" #[("class", "pilean-index-img"), ("src", backdropUrl b "light"),
              ("alt", d.alt), ("decoding", "async")] .empty,
            .element "span" #[("class", "pilean-index-over")] img])
        | none => img
      html%{<a class="pilean-index-thumb" href={href}>{inner}</a>}
    | none => .empty
  let files := p.files.map fun f =>
    html%{<a href={fileUrl f.path} title={s!"{f.bytes} bytes, SHA-256 {f.sha256}"}>
      {.text (fileLabel f)}</a>}
  let standing ← standingSummaryHtml s l site d.decl
  let page : Html := match pageLink? st d.decl with
    | some h => html%{<dt>{"Page"}</dt><dd><a class="pilean-page-link" href={h}>
        {"code, standing and provenance"}</a></dd>}
    | none => .empty
  let caption : Html := .seq <| d.caption.map fun (m, t) =>
    if m then html%{<code class={math}>{.text t}</code>} else .text t
  let src : DeclRef := { name := d.decl, module := d.module, file := d.file, line := d.line }
  pure html%{<li>
      {thumb}
      <div class="pilean-index-body">
        <p class="pilean-index-title"><a href={href}>{.text s!"Figure {p.number}"}</a>
          {caption}</p>
        <dl class="pilean-index-facts">
          <dt>{"Source"}</dt><dd>{← declLinkHtml s l d.decl}{s.place src p.sourceHref}</dd>
          <dt>{"Fingerprint"}</dt><dd>{fingerprintHtml (shownFingerprint p)}</dd>
          <dt>{"Files"}</dt><dd class="pilean-index-files">{files}</dd>
          {standing}
          {page}
        </dl>
      </div>
    </li>}

open Verso.Output.Html in
/-- The body of the figures page; `site` sets the link mode. -/
def figureListHtmlWith (s : DeclStyle) (math : String) (st : TraverseState)
    (site : Option SiteRender := none) : IO Html := do
  let reg := Registry.get st
  let placed := reg.placed.qsort (·.order < ·.order)
  let l := Links.of s st site
  let intro := html%{<p class="pilean-figure-index-intro">
      {"Every picture on this site was drawn by the site's build from the Lean declaration named
      beside it. The fingerprint covers what the picture shows and the declaration's source; "}
      <a href={fileUrl manifestName}>{"the manifest"}</a>
      {" lists every file with its SHA-256, and "}<code>{"pilean-verify"}</code>
      {" checks a copy of the folder against it."}</p>}
  if placed.isEmpty then
    return html%{<div class="pilean-figure-list">{intro}
      <p>{"This document has no figures."}</p></div>}
  let entries ← placed.mapM (indexEntryWith s l math st site)
  return html%{<div class="pilean-figure-list">{intro}
    <ol class="pilean-figure-index">{entries}</ol></div>}

open Verso.Output.Html in
/-- The link of `{figref "label"}[contents]`: "Figure 2" (or `contents`), linked to the figure
with that label; an error names a label no figure has. -/
def figrefHtml (st : TraverseState) (label : String) (contents : Array Html) :
    Except String Html := do
  let reg := Registry.get st
  let some p := reg.placed.find? (·.data.label == some label)
    | throw s!"No figure has the label {label}"
  let text := if contents.isEmpty then .text s!"Figure {p.number}" else .seq contents
  match st.resolveDomainObject figureDomain label with
  | .ok link => pure html%{<a class="pilean-figref" href={link.link}>{text}</a>}
  | .error e => throw e

end PILeanVerso
