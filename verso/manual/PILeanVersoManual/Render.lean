/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Trust.Build
import PILean.Svg.Inert

/-!
# Rendering the figures of a site

`renderSite` renders the figures a document uses, each output with its source record (and the
site's repository and commit, when given) as `pilean-build` writes it, and the manifest of all of
them. The files go below the folder `figureFolder` of the site's data directory, at the paths
`pilean-build` uses, with `manifest.json` beside them, so `pilean-verify` checks the published
folder as it checks one made by `pilean-build`. Every SVG output must be inert
(`PILean.Svg.inertProblem?`): no script, no event handler, nothing loaded from elsewhere; so must
every picture a page puts inline (`Output.inline`, every frame of an explorer, `Output.frames`).
What a document asks of a figure (`FigureUse`: inline, or as an explorer) is checked against what
the figure has, and the inline SVG of one figure, counted once over everything the pages put
inline for it, may not pass `SiteOptions.inlineLimit` bytes.

The rendered site is kept in `siteRef` while the document is rendered: the generator wrapper
(`PILeanVerso.withFigures`) sets it, and the figure blocks read it during traversal.

## Main definitions

* `LeanLinks`, `SiteOptions`, `FigureUse`, `SiteFile`, `SiteFigure`, `SiteRender`
* `renderSite`: the files and the manifest of the figures a site uses
* `SiteRender.checkFolder`: the differences between a folder and the render
* `imageSize?`: the size in pixels a picture asks for
-/

namespace PILeanVerso

open PILean PILean.Trust

/-- The folder of the figures below the site's data directory. -/
def figureFolder : String := "pilean-figures"

/-- Where the links to Lean declarations of a site's figures lead: the declaration named in a
figure's source line and on the figures page, and each element of an inline picture that names a
declaration (`data-lean-decl`).

* `ideil`: `lean:decl/<Name>` links, for an editor that shows the site beside the code (IDEiL);
  in the source line they are shown only when the page's root has `data-lean-links`.
* `site`: a link to the declaration's own place in the built site (a Blueprint entry or its Lean
  panel, a docstring of a Verso manual, the figure the declaration draws); a declaration with no
  such place gets no link, and the build warns.
* `none`: no link; the name stays text and an element of a picture keeps its hover text. -/
inductive LeanLinks where
  /-- `lean:decl/<Name>` links. -/
  | ideil
  /-- Links into the built site. -/
  | site
  /-- No links. -/
  | none
deriving Inhabited, Repr, BEq, DecidableEq

/-- The mode of a command-line value: `ideil`, `site` or `none`. -/
def LeanLinks.ofString? : String → Option LeanLinks
  | "ideil" => some .ideil
  | "site" => some .site
  | "none" => some .none
  | _ => Option.none

/-- What a site's build records in its figures besides their source, and how the pages link
them. -/
structure SiteOptions where
  /-- The repository's URL (`http` or `https`), recorded in every file and in the manifest. -/
  repo : Option String := none
  /-- The commit the site is built from (4 to 64 lowercase hexadecimal digits). -/
  commit : Option String := none
  /-- The folder of the package's sources within the repository (empty, or ending in `/`), put
  before a figure's file in links to the repository. -/
  sourcePrefix : String := ""
  /-- The most bytes of SVG one figure may put inline in a page (its inline picture, or all the
  frames of an explorer); a figure above it fails the build. -/
  inlineLimit : Nat := 2000000
  /-- Where the links to Lean declarations lead (`--figure-lean-links`). -/
  leanLinks : LeanLinks := .ideil
deriving Inhabited, Repr

/-- How a document uses one figure: by its declaration's name, put inline (`inline := true`), or
as an explorer (`figure_explorer`). -/
structure FigureUse where
  /-- The figure's declaration. -/
  decl : String
  /-- Whether a page puts the picture inline. -/
  inline : Bool := false
  /-- Whether a page shows it as an explorer. -/
  explorer : Bool := false
deriving Inhabited, Repr, BEq

/-- A plain use of a figure, as a picture file. -/
instance : Coe String FigureUse := ⟨fun d => { decl := d }⟩

/-- Whether `s` is empty, or relative path components of `nameChar` characters each followed by
`/`. -/
def validPrefix (s : String) : Bool :=
  s.isEmpty || (s.endsWith "/" && safePath (s.dropEnd 1).toString)

/-- The options, or why they cannot be used: the repository must be an `http` or `https` link
(`safeLink?`), the commit 4 to 64 lowercase hexadecimal digits, the prefix `validPrefix`. -/
def SiteOptions.validate (o : SiteOptions) : Except String SiteOptions := do
  if let some r := o.repo then
    if (safeLink? r).isNone then throw s!"the repository {r} is not an http or https link"
  if let some c := o.commit then
    if !isCommit c then throw s!"the commit {c} is not 4 to 64 lowercase hexadecimal digits"
  if !validPrefix o.sourcePrefix then
    throw s!"the source prefix {o.sourcePrefix} is not a relative folder ending in /"
  return o

/-- One file of a figure: the output's name suffix and format, and the file PILean built. -/
structure SiteFile where
  /-- The suffix of the output's name: `""`, `"-dark"`, `"-poster"`, `"-poster-dark"`. -/
  name : String
  /-- The format. -/
  format : Format
  /-- The manifest entry and the bytes. -/
  built : BuiltFile
  /-- The picture as nodes, for a page that puts it inline (an SVG output that has one, of a
  figure the document uses inline or as an explorer). -/
  inline : Option InlineSvg := none
  /-- Every frame of an explorer, for a page that shows them inline (of a figure the document
  uses as an explorer). -/
  frames : Option FrameSet := none
  /-- The layout warnings of the figure. -/
  problems : Array String := #[]

/-- The files of one figure declaration. -/
structure SiteFigure where
  /-- The recorded source of the declaration. -/
  source : SourceData
  /-- Its files, in the order of its outputs. -/
  files : Array SiteFile

/-- The figures of a site, rendered. -/
structure SiteRender where
  /-- The options of the build. -/
  options : SiteOptions := {}
  /-- The figures, by declaration name. -/
  figures : Std.HashMap String SiteFigure := {}
  /-- Every file, sorted by path. -/
  files : Array BuiltFile := #[]
  /-- The text of `manifest.json`. -/
  manifest : String := Manifest.render #[]
  /-- The layout warnings of the figures (`Output.problems`), one per line. -/
  warnings : Array String := #[]

instance : Inhabited SiteRender := ⟨{}⟩

/-- Renders the output `o` of `e` as `pilean-build` does, and checks that an SVG is inert. The
inline picture and the frames are kept only when the document puts them in a page (`u`). -/
def renderSiteFile (e : FigureEntry) (o : Output) (opts : SiteOptions) (u : FigureUse) :
    Except String SiteFile := do
  let built ← renderOutput e o { repo := opts.repo, commit := opts.commit }
  if o.format == .svg then
    match String.fromUTF8? built.bytes with
    | none => throw s!"{built.entry.path}: the SVG is not UTF-8"
    | some text =>
      if let some why := Svg.inertProblem? text then
        throw s!"{built.entry.path}: the SVG is not inert ({why})"
  let wanted := o.format == .svg && (u.inline || u.explorer)
  let inline := if wanted then o.inline () else none
  let frames := if wanted && u.explorer then o.frames () else none
  return { name := o.name, format := o.format, built, inline, frames, problems := o.problems () }

/-- The pictures a page puts inline for a figure used as `u`, from its files: the picture and
its narrow rendition (`inline := true`), or every frame (an explorer). -/
def inlinePictures (u : FigureUse) (fs : Array SiteFile) : Array InlineSvg :=
  let svg := fun (name : String) => fs.find? fun f => f.format == .svg && f.name == name
  if u.explorer then ((svg "").bind (·.frames)).map (·.frames) |>.getD #[]
  else if u.inline then
    ((svg "").bind (·.inline)).toArray ++ ((svg "-narrow").bind (·.inline)).toArray
  else #[]

/-- Why the figure `n`, used as `u`, cannot be shown so, if it cannot: an explorer must have
frames, an inline figure an inline picture. -/
def useProblem? (n : String) (u : FigureUse) (fs : Array SiteFile) : Option String :=
  let svg := fs.find? fun f => f.format == .svg && f.name == ""
  if u.explorer && (svg.bind (·.frames)).isNone then
    some s!"{n} is shown with figure_explorer but is not an explorer (a declaration of type \
      PILean.Explorer, made with Plane.slider, Plane.stepper or Explorer.grid)"
  else if u.inline && !u.explorer && (svg.bind (·.inline)).isNone then
    some s!"{n} is shown with (inline := true) but has no inline picture (plane figures, plots \
      and explorers have one); remove the option to show its file"
  else none

/-- The checks of the pictures a page puts inline for the figure `n` used as `u`: each is inert,
and together they are at most `limit` bytes. -/
def inlineProblems (n : String) (u : FigureUse) (fs : Array SiteFile) (limit : Nat) :
    Array String := Id.run do
  let docs := (inlinePictures u fs).map (·.document)
  let mut out := #[]
  for (doc, i) in docs.zipIdx do
    if let some why := Svg.inertProblem? doc then
      out := out.push s!"{n}: inline picture {i} is not inert ({why})"
  let size := docs.foldl (fun k d => k + d.utf8ByteSize) 0
  if size > limit then
    out := out.push s!"{n}: {size} bytes of inline SVG, more than the limit of {limit} \
      (--figure-inline-limit)"
  return out

/-- The uses of the figures, one per declaration (in name order): inline or as an explorer when
any use is. -/
def mergeUses (used : Array FigureUse) : Array FigureUse :=
  let m : Std.HashMap String FigureUse := used.foldl (init := {}) fun m u =>
    match m[u.decl]? with
    | some v =>
      m.insert u.decl
        { v with inline := v.inline || u.inline, explorer := v.explorer || u.explorer }
    | none => m.insert u.decl u
  m.toArray.map (·.2) |>.qsort (·.decl < ·.decl)

/-- Renders the figures `used` (repeated names count once) from the table `entries`, with all
the messages (one per line) if a name has no entry, a figure cannot be rendered (then only
that is reported for it) or cannot be shown as it is used (`useProblem?`), an SVG or an inline
picture is not inert, a figure's inline
SVG passes the limit, two files have one path, or there are more than `maxEntries` figures. -/
def renderSite (entries : Array FigureEntry) (used : Array FigureUse) (opts : SiteOptions) :
    Except String SiteRender := do
  let opts ← opts.validate
  let byName : Std.HashMap String FigureEntry := entries.foldl (init := {}) fun m e =>
    m.insert e.decl e
  let uses := mergeUses used
  if uses.size > maxEntries then throw s!"more than {maxEntries} figures"
  let mut figures : Std.HashMap String SiteFigure := {}
  let mut files : Array BuiltFile := #[]
  let mut errors : Array String := #[]
  let mut warnings : Array String := #[]
  for u in uses do
    let n := u.decl
    match byName[n]? with
    | none => errors := errors.push s!"{n}: no figure of that name in the generator's table \
        (is its module imported, and is it marked @[figure]?)"
    | some e =>
      let mut fs : Array SiteFile := #[]
      let mut refused := false
      for o in e.outputs () do
        match renderSiteFile e o opts u with
        | .ok f => fs := fs.push f
        | .error msg => errors := errors.push msg; refused := true
      -- a figure with an output refused is reported for that alone: what its use needs from
      -- the outputs that were not made is not known
      if !refused then
        match useProblem? n u fs with
        | some why => errors := errors.push why
        | none => errors := errors ++ inlineProblems n u fs opts.inlineLimit
      for f in fs do
        for w in f.problems do warnings := warnings.push s!"{n}: {w}"
      figures := figures.insert n { source := e.toSourceData, files := fs }
      files := files ++ fs.map (·.built)
  files := files.qsort (fun a b => a.entry.path < b.entry.path)
  for i in [1:files.size] do
    if files[i - 1]!.entry.path == files[i]!.entry.path then
      errors := errors.push s!"two outputs have the path {files[i]!.entry.path}"
  if !errors.isEmpty then throw ("\n".intercalate errors.toList)
  return { options := opts, figures, files, manifest := Manifest.render (files.map (·.entry)),
           warnings }

/-- The lines `pilean-build --check` prints for the folder `dir` against this render
(`missing:`, `stale:`, `extra:`); none if the folder holds exactly the render. -/
def SiteRender.checkFolder (r : SiteRender) (dir : System.FilePath) : IO (Array String) := do
  let root ← if ← dir.pathExists then IO.FS.realPath dir else pure dir
  checkLines r.files r.manifest.toUTF8 root

/-- The rendered site while a document is rendered; set by `withFigures`. -/
initialize siteRef : IO.Ref (Option SiteRender) ← IO.mkRef none

/-- The declarations the pages wanted to link with `--figure-lean-links site` and found no place
of the site for, collected while the document is rendered; `withFigures` warns about them. -/
initialize unlinkedRef : IO.Ref (Std.HashSet String) ← IO.mkRef {}

/-! ### Picture sizes -/

private def u8 (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat

/-- The whole-number part of a decimal number at the start of `s`, if it starts with a digit. -/
def leadingNat? (s : String) : Option Nat :=
  let ds := s.toList.takeWhile Char.isDigit
  if ds.isEmpty || ds.length > 9 then none
  else some (ds.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0)

/-- The value of the attribute `name` in the first `<svg` tag of `s`, read from at most the first
4096 bytes. -/
def svgAttr? (s : String) (name : String) : Option String := do
  let head := (s.take 4096).toString
  let tag := (head.splitOn "<svg").drop 1 |>.head?
  let tag ← tag
  let tag := (tag.splitOn ">").head!
  let after ← ((" " ++ tag).splitOn s!" {name}=\"").drop 1 |>.head?
  (after.splitOn "\"").head?

/-- The size in pixels a picture asks for: an SVG's `width` and `height` (whole numbers), a PNG's
header, a GIF's logical screen; `none` for anything else or a size of 0 or above 100000. -/
def imageSize? (format : Format) (b : ByteArray) : Option (Nat × Nat) := do
  let (w, h) ← match format with
    | .svg =>
      let s ← String.fromUTF8? b
      pure (← (svgAttr? s "width").bind leadingNat?, ← (svgAttr? s "height").bind leadingNat?)
    | .png | .apng =>
      if b.size < 24 then none
      else pure (((u8 b 16 * 256 + u8 b 17) * 256 + u8 b 18) * 256 + u8 b 19,
        ((u8 b 20 * 256 + u8 b 21) * 256 + u8 b 22) * 256 + u8 b 23)
    | .gif => if b.size < 10 then none else pure (u8 b 6 + 256 * u8 b 7, u8 b 8 + 256 * u8 b 9)
  if w == 0 || h == 0 || w > 100000 || h > 100000 then none else some (w, h)

end PILeanVerso
