/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanVersoManual.Common
import PILeanVersoManual.Highlight
import PILean.Trust.Verify

/-!
# A figure's page

Every figure a site uses has a page of its own, below the figures page, at an address made from
its declaration's name (`pageSlug`). The figure's source line and its entry on the figures page
link to it. From top to bottom it shows:

1. the picture at full size (the light and the dark files, following the page's theme; an
   animation's still frame for readers who ask for reduced motion; an explorer as it is shown
   where it is used; a motion moving, without its stills), and every file of the figure to
   download, with its size (folded in a `details` element above `foldFilesAbove` files);
2. its number and caption, and every place the document shows it;
3. its *standing* (`PILean.Trust.Standing`), as `site_figures%` derived it from the environment
   of the site's generator: "Linked theorem: T" with each theorem's statement as Lean, the axioms
   it rests on and what PILean checked of it (`linkCheckedText`), then what a linked theorem does
   and does not cover (`theoremScopeText`, `theoremLinkText`; all three sentences of
   `docs/TRUST.md`); or "Illustration: no theorem is linked to it";
4. for a motion (`motionSection`): what the animation is, the table of its steps and its key
   stills with their captions, in a grid whose columns follow the stills' widths;
5. the code: the figure's declaration in full, then the declarations of the project that its
   value and its theorems' statements use (`figurePageData`, with its caps), each highlighted with
   the hovers of the genre's Lean code and linked to its source at the build's commit, then the
   declarations of other packages they name; folded in a `details` element, closed, when it is
   longer than `codeFoldAbove` lines;
6. provenance: each file's fingerprint, renderer and text engine, what `pilean-verify` says of
   the file against the site's manifest, the toolchain and the packages that draw the picture,
   the build's commit and the continuous-integration run;
7. how to reproduce: the commands that build the site again and check the files.

Everything on the page that comes from the project (names, captions, code, paths) is text, which
the HTML writer escapes; the pictures are the site's own inert files. The page adds no script:
an explorer uses the script it uses everywhere, and the code the hovers of the genre's Lean code.

What a page states about the files and the standing is recorded (`pageStatedRef`); after the
site is written the generator wrapper checks it against a fresh render, the written manifest and
`pilean-verify` (`PILeanVersoManual.Wrapper`).
-/

namespace PILeanVerso

open Lean Verso Doc Html Genre Manual
open Verso.Output (Html)
open Verso.Output.Html
open PILean PILean.Trust
open SubVerso.Highlighting

/-! ### Words -/

/-- What PILean checked of the theorem `t` linked to a figure, and what it did not, in the words
of `docs/TRUST.md` ("Standing", with `T` for the theorem). -/
def linkCheckedText (t : String) : String :=
  s!"PILean checked that {t} is proved from the standard axioms and that its statement names \
    this figure; it did not check what {t} says."

/-- What a theorem linked to a figure covers, in the words of `docs/TRUST.md` ("Standing"). -/
def theoremScopeText : String :=
  "What a linked theorem says is in its statement. The theorems of this library state the \
    figure's data and, where written, its colour roles, texts and title; none says how text is \
    rendered, which colour values a style gives, or how the exact numbers become pixels."

/-- What a link from a figure to a theorem is, in the words of `docs/TRUST.md`. -/
def theoremLinkText : String :=
  "A link is a pointer from a picture to a statement to read, not a certificate that the \
    picture is correct."

/-- What an illustration is, on its page. -/
def illustrationText (marked : Bool) : String :=
  if marked then
    "Its declaration marks it as an illustration (@[figure illustration]): a picture shown for \
      what it shows, with no theorem about the object it is drawn from."
  else
    "No theorem is linked to it by figure_links in the modules the site's generator imports, \
      and its declaration does not mark it as an illustration (pilean-build \
      --require-standing refuses such a figure)."

/-- The sentence above the code of the project's declarations. -/
def relatedIntroText : String :=
  s!"The declarations of the project that the figure's value and its theorems' statements use, \
    and those that these use in turn (to depth {codeDepth}), nearest first; a theorem is followed \
    by its statement, not its proof. At most {codeInlineCap} are shown in full."

/-- The sentence of a declaration shown only by its signature. -/
def signatureOnlyText : String :=
  "Shown by its signature: the highlighted source of its module was not available when the \
    site was built."

/-! ### What a page states, for the check after the build -/

/-- What a figure's page states about the figure, recorded when it is written. -/
structure PageStated where
  /-- The page's path in the site, as Verso's traversal gives it. -/
  path : Array String
  /-- The standing's word and its theorems. -/
  standing : String × Array String
  /-- Each file: its path, size, SHA-256 and the verdict the page shows for it. -/
  files : Array (String × Nat × String × String)
deriving Inhabited, Repr, BEq

/-- The statements of the pages written so far, by declaration. -/
initialize pageStatedRef : IO.Ref (Std.HashMap String PageStated) ← IO.mkRef {}

/-! ### Pieces -/

private def txt (s : String) : Html := .text s

private def el (tag cls : String) (content : Html) (attrs : Array (String × String) := #[]) :
    Html :=
  .element tag (#[("class", cls)] ++ attrs) content

/-- A number of bytes with a comma between groups of three digits. -/
def groupDigits (n : Nat) : String := Id.run do
  let ds := (toString n).toList.toArray
  let mut out := ""
  for h : i in [0:ds.size] do
    if i > 0 && (ds.size - i) % 3 == 0 then out := out.push ','
    out := out.push ds[i]
  return out

/-- What `pilean-verify` says of a file of the render against the render's manifest entry, made
in memory: `ok` when the bytes have the listed size, SHA-256 and format and carry the listed
source record. -/
def builtVerdict (b : BuiltFile) : Verdict :=
  if b.bytes.size != b.entry.bytes || Sha256.hex (Sha256.hash b.bytes) != b.entry.sha256 then
    .changed
  else if detectedFormat? b.bytes != some b.entry.format then .formatDiffers
  else match Source.read? b.bytes with
    | .error _ => .noSource
    | .ok s => if b.entry.matches s then .ok else .sourceDiffers

/-- The source link of a declaration at the build's commit, over its lines when they are known. -/
def declHref (o : SiteOptions) (d : CodeDecl) : Option String := do
  let repo ← o.repo
  let commit ← o.commit
  let fragment := if d.line == 0 then ""
    else if d.endLine > d.line then s!"#L{d.line}-L{d.endLine}" else s!"#L{d.line}"
  safeLink? s!"{repo}/blob/{commit}/{o.sourcePrefix}{d.file}{fragment}"

/-- The place of a declaration: its file and lines, linked to its source when the site has a
repository and a commit. -/
def declPlaceHtml (o : SiteOptions) (d : CodeDecl) : Html :=
  let lines := if d.line == 0 then ""
    else if d.endLine > d.line then s!":{d.line}–{d.endLine}" else s!":{d.line}"
  match declHref o d with
  | some h => .element "a" #[("class", "pilean-repo-link"), ("href", h)] (txt (d.file ++ lines))
  | Option.none => el "span" "pilean-place" (txt (d.file ++ lines))

/-- Highlighted code as the genre shows Lean code: Verso's code blocks, with their hovers, no
proof states and no definition anchors (the same declaration may be on several pages). -/
def codeBlock {m : Type → Type} [Monad m] (hs : Array Highlighted) :
    HtmlT Manual m Html :=
  withReader (fun c => { c with codeOptions.inlineProofStates := false,
                                codeOptions.definitionsAsTargets := false }) <|
    (Highlighted.seq hs).blockHtml (g := Manual) "pilean-figure-page" (trim := true)

/-- Text shown as code without hovers, for a signature or a statement Lean printed. -/
def plainBlock (s : String) : Html :=
  el "pre" "pilean-page-plain" (.element "code" #[] (txt s))

/-- A declaration's section: its kind, name and place, then its source as highlighted Lean (at
most `codeLineCap` lines), or its signature when its module's highlighted source is not there.
`statementOnly` shows a theorem's statement only, in a section of the class `pilean-page-theorem`.
-/
def declSection {m : Type → Type} [Monad m] [MonadLiftT IO m] (o : SiteOptions)
    (s : DeclStyle) (d : CodeDecl) (note : Html := .empty) (statementOnly : Bool := false)
    (fallback : String := d.signature) : HtmlT Manual m Html := do
  let cls := if statementOnly then "pilean-page-decl pilean-page-theorem" else "pilean-page-decl"
  let code? ← (declCode? d : IO _)
  let body : Html ← match code? with
    | some hl =>
      let leaves := plainCode hl
      let shown := if statementOnly then (statementPart leaves).getD leaves else leaves
      let (shown, cut) := takeLines codeLineCap shown
      let code ← codeBlock shown
      pure (.seq #[el "div" "pilean-page-code" code,
        if cut then el "p" "pilean-page-cut"
          (txt s!"The first {codeLineCap} lines; the rest is at the source link.") else .empty])
    | Option.none =>
      pure (.seq #[el "p" "pilean-page-note" (txt signatureOnlyText), plainBlock fallback])
  let kind := el "span" "pilean-page-kind" (txt d.kind)
  pure <| el "section" cls (.seq #[
      el "h3" "pilean-page-decl-title" (.seq #[kind, txt " ", s.decl d.name, txt " ",
        declPlaceHtml o d]),
      note, body]) #[("data-lean-decl", d.name)]

/-- The address of a declaration of the Lean or Mathlib documentation, for the modules it covers
(`Init`, `Std`, `Lean`, `Lake`, `Mathlib`, `Batteries`); `none` for others. -/
def docsHref? (e : ExternalName) : Option String :=
  let root := (e.module.splitOn ".").headD ""
  if ["Init", "Std", "Lean", "Lake", "Mathlib", "Batteries"].contains root &&
      e.module.all (fun c => c.isAlphanum || c == '.' || c == '_') then
    let path := e.module.replace "." "/"
    safeLink? s!"https://leanprover-community.github.io/mathlib4_docs/{path}.html#{
      String.join (e.name.toList.map fun c =>
        if c.isAlphanum || c == '.' || c == '_' then c.toString else "_")}"
  else none

/-- The most files a figure's page lists unfolded; a figure with more (a motion, with its key
stills at each width and in each theme) has its lists of files and of their provenance in a
`details` element. -/
def foldFilesAbove : Nat := 12

/-- The most lines of code (`shownLines`, over the declarations of the section) a figure's page
shows unfolded; longer code is in a `details` element, closed, after everything about the picture
(its caption, standing and animation). -/
def codeFoldAbove : Nat := 60

/-- The lines a page shows of a declaration's code: its source's lines, at most `codeLineCap`,
or, when its place is not known, the lines of its signature. -/
def shownLines (d : CodeDecl) : Nat :=
  if d.line > 0 && d.endLine ≥ d.line then min codeLineCap (d.endLine - d.line + 1)
  else (d.signature.splitOn "\n").length

/-! ### A motion -/

/-- A duration in seconds, exactly: `1 s`, `3/2 s`. -/
def secondsText (q : Rat) : String :=
  if q.den == 1 then s!"{q.num} s" else s!"{q.num}/{q.den} s"

/-- The table of a motion's steps: for each step, the keys it goes between, its duration, and
each move with its panel (in a picture of panels), its actor and what it is
(`MotionMoveRow.words`, which says when a move is drawn as a crossfade); an idle step says that
nothing moves. Every string is text, which the HTML writer escapes. -/
def motionStepTable (rows : Array MotionStepRow) : Html :=
  let head := Html.element "thead" #[] (.element "tr" #[] (.seq #[
    .element "th" #[("scope", "col")] (txt "Step"),
    .element "th" #[("scope", "col")] (txt "Duration"),
    .element "th" #[("scope", "col")] (txt "What moves")]))
  let move (r : MotionMoveRow) : Html :=
    let cls := if r.asDeclared then "pilean-motion-move"
      else "pilean-motion-move pilean-motion-crossfade"
    .element "li" #[("class", cls)] (.seq #[
      if r.panel.isEmpty then .empty
      else .seq #[el "span" "pilean-motion-panel" (txt r.panel), txt ": "],
      .element "code" #[] (txt r.actor), txt s!": {r.words}"])
  let body := rows.map fun row =>
    let what : Html :=
      if row.moves.isEmpty then
        txt (if row.idle then "Nothing moves (it holds its key frame)." else "Nothing moves.")
      else .element "ul" #[("class", "pilean-motion-moves")] (.seq (row.moves.map move))
    Html.element "tr" #[] (.seq #[
      .element "th" #[("scope", "row")]
        (txt s!"{row.step + 1}: key frame {row.step + 1} to {row.step + 2}"),
      .element "td" #[] (txt (secondsText row.duration)),
      .element "td" #[] what])
  el "div" "pilean-motion-steps-wrap" (.element "table" #[("class", "pilean-motion-steps")]
    (.seq #[.element "caption" #[] (txt "The steps of the animation, from key frame to key frame"),
      head, .element "tbody" #[] (.seq body)]))

/-- The section of a figure's page about a motion (`m`, with its narrow rendition `n`): what the
animation is (`MotionData.words`, with `MotionData.checkWords` when it was not checked strictly),
the table of its steps (`motionStepTable`) and its key stills with their captions, as a grid
whose columns follow the stills' widths (`stillColumnClasses`), always shown here (the motion at
the top of the page is shown without them, `pilean-motion-bare`, so nothing is shown twice; the
contact sheet is offered among the files). -/
def motionSection (idBase : String) (m : MotionData) (n : Option MotionData)
    (files : Array FileInfo) : Html :=
  let captions := m.stills.stepCaptions
  let narrowOf := fun (k : Nat) => n.map fun _ => s!"-narrow-key-{k}"
  let stills := (Array.range m.stills.frames.size).map fun k =>
    Html.element "li" #[("class", "pilean-page-motion-key")] (.seq #[
      themedPictures files s!"-key-{k}" (narrowOf k) (lazy := true),
      el "p" "pilean-motion-key-caption" (txt (motionStepText captions k))])
  el "section" "pilean-page-motion" (.seq #[
    el "h2" "pilean-page-h" (txt "Animation"),
    el "p" (if m.unchecked then "pilean-motion-words pilean-motion-unchecked"
      else "pilean-motion-words") (txt m.words),
    motionStepTable m.steps,
    el "h3" "pilean-page-decl-title" (txt "Key frames"),
    el "ol" (s!"pilean-page-motion-keys " ++ stillColumnClasses
      (stillWidth? files s!"-key-{m.stills.poster}")
      (n.bind fun _ => stillWidth? files s!"-narrow-key-{m.stills.poster}")).trimAscii.toString
      (.seq stills),
    el "p" "pilean-page-note" (txt "The contact sheet of these stills, for print, is among the \
      files.")]) #[("id", s!"{idBase}-animation")]

/-! ### The page -/

/-- The page of the figure `decl`; `math` is the class of TeX in captions, and `idAttr` the
anchor of the page's block (`TraverseState.htmlId`). The anchor is an empty element at the start
of the page (`span.pilean-figure-page-anchor`, hidden from assistive technology, of no size and
never highlighted; `pageCss`), where the links of `pageLink?` lead. The page's own element
(`div.pilean-figure-page`) and its sections carry ids that start with
`pilean-page-<pageSlug decl>`. -/
def figurePageHtmlWith {m : Type → Type} [Monad m] [MonadLiftT IO m] (s : DeclStyle)
    (math : String) (st : TraverseState) (site : SiteRender) (decl : String)
    (idAttr : Array (String × String)) : HtmlT Manual m Html := do
  let anchor : Html := if idAttr.isEmpty then .empty else
    el "span" "pilean-figure-page-anchor" .empty (#[("aria-hidden", "true")] ++ idAttr)
  let reg := Registry.get st
  let placed := (reg.placed.filter (·.data.decl == decl)).qsort (·.order < ·.order)
  let some p := placed[0]?
    | return .seq #[anchor, el "p" "pilean-figure-missing" (txt s!"{decl} is not shown.")]
  let some fig := site.figures[decl]?
    | return .seq #[anchor, el "p" "pilean-figure-missing" (txt s!"{decl} was not rendered.")]
  let o := site.options
  let l := Links.of s st site
  let idBase := s!"pilean-page-{pageSlug decl}"
  -- the picture, full size
  let full : Placed := { p with data := { p.data with width := none } }
  let motion := motionOf? fig.files
  let picture ← match ← (inlinePicture? l site full #[("id", idBase)]
      (motionStills := false) : IO _) with
    | some h => pure (if p.data.explorer || motion.isSome then h else (pictureHtml full).getD h)
    | Option.none => pure ((pictureHtml full).getD (el "p" "pilean-figure-missing" (txt "No file.")))
  let hasDark := (pick? p.files p.data.format "-dark").isSome ||
    p.files.any (·.name.endsWith "-dark")
  let verdicts := fig.files.map fun f => (f, builtVerdict f.built)
  let downloads := el "ul" "pilean-page-files" (.seq (verdicts.map fun (f, _) =>
    let info := (fileInfos fig).find? (·.path == f.built.entry.path)
    let label := (info.map fileLabel).getD f.built.entry.path
    .element "li" #[] (.seq #[
      .element "a" #[("href", fileUrl f.built.entry.path), ("download", ""),
          ("class", "pilean-page-download"), ("data-sha256", f.built.entry.sha256),
          ("data-bytes", toString f.built.entry.bytes)] (txt label),
      txt s!", {groupDigits f.built.entry.bytes} bytes"])))
  -- a figure with many files (a motion: its stills at each width) lists them folded
  let folded := fun (what : String) (body : Html) =>
    if verdicts.size ≤ foldFilesAbove then body
    else .element "details" #[("class", "pilean-page-files-more")] (.seq #[
      .element "summary" #[] (txt s!"{verdicts.size} {what}"), body])
  let downloads := folded "files" downloads
  -- caption, number, uses
  let caption : Html := .seq <| p.data.caption.map fun (isMath, t) =>
    if isMath then .element "code" #[("class", math)] (txt t) else txt t
  let uses := el "ul" "pilean-page-uses" (.seq (placed.map fun q =>
    let target := (placedLink? st q).getD "#"
    .element "li" #[] (.element "a" #[("href", target), ("class", "pilean-page-use")]
      (txt s!"Figure {q.number}"))))
  let heading := el "section" "pilean-page-caption" (.seq #[
    el "p" "pilean-page-number" (txt s!"Figure {p.number}"),
    el "p" "pilean-page-caption-text" caption,
    el "h2" "pilean-page-h" (txt "Where it is shown"), uses])
  -- standing
  let data := site.pages[decl]?
  let standing ← match fig.standing with
    | .linked ts => do
      let thms ← ts.mapM fun t => do
        let checked := el "p" "pilean-standing-checked" (txt (linkCheckedText t))
        match data.bind (·.theorems.find? (·.decl.name == t)) with
        | some ti =>
          let axioms := if ti.axioms.isEmpty then "Axioms: none."
            else s!"Axioms: {", ".intercalate ti.axioms.toList}."
          let sec ← declSection o s ti.decl (statementOnly := true) (fallback := ti.statement)
            (note := el "p" "pilean-page-axioms" (txt axioms))
          pure (Html.seq #[sec, checked])
        | Option.none => pure (.seq #[el "p" "pilean-figure-missing"
            (txt s!"{t}: no statement recorded."), checked])
      let names := .seq <| (ts.map fun t => s.decl t).toList.intersperse (txt ", ") |>.toArray
      pure <| el "section" "pilean-page-standing pilean-standing-linked" (.seq #[
        el "h2" "pilean-page-h" (txt "Standing"),
        el "p" "pilean-standing-words" (.seq #[txt (standingWords fig.standing), txt " ", names]),
        .seq thms,
        if motion.isSome then el "p" "pilean-standing-scope pilean-motion-linked"
          (txt motionLinkedWords) else .empty,
        el "p" "pilean-standing-scope" (txt theoremScopeText),
        el "p" "pilean-standing-scope" (txt theoremLinkText)])
        #[("id", s!"{idBase}-standing")]
    | .illustration marked =>
      pure <| el "section" "pilean-page-standing pilean-standing-illustration" (.seq #[
        el "h2" "pilean-page-h" (txt "Standing"),
        el "p" "pilean-standing-words" (txt (standingWords fig.standing ++ ".")),
        el "p" "pilean-standing-scope" (txt (illustrationText marked))])
        #[("id", s!"{idBase}-standing")]
  -- the motion: what it is, its steps and its key frames
  let animation := match motion with
    | some (m, n) => motionSection idBase m n p.files
    | Option.none => Html.empty
  -- code
  let code ← match data with
    | Option.none => pure (el "section" "pilean-page-codes" (.seq #[
        el "h2" "pilean-page-h" (txt "Code"),
        el "p" "pilean-page-note" (txt "The site's table of figures holds no code for this \
          figure (it was not made by site_figures%).")]))
    | some d => do
      let own ← declSection o s d.figure
      let rel ← d.related.mapM fun r => declSection o s r
        (note := if r.via.isEmpty then .empty else
          el "p" "pilean-page-via" (.seq #[txt "Used by ", s.decl r.via, txt "."]))
      let more := if d.more.isEmpty then Html.empty else
        .element "details" #[("class", "pilean-page-more")] (.seq #[
          .element "summary" #[] (txt s!"{d.more.size + d.moreOmitted} more declarations of the \
            project"),
          el "ul" "pilean-page-more-list" (.seq (d.more.map fun r =>
            .element "li" #[] (.seq #[s.decl r.name, txt " ", declPlaceHtml o r]))),
          if d.moreOmitted > 0 then el "p" "pilean-page-note"
            (txt s!"and {d.moreOmitted} more not listed (at most {codeMoreCap} are).") else .empty])
      let ext := if d.external.isEmpty then Html.empty else
        el "section" "pilean-page-external" (.seq #[
          el "h3" "pilean-page-decl-title" (txt "From other packages"),
          el "ul" "pilean-page-external-list" (.seq (d.external.map fun e =>
            let name := match docsHref? e with
              | some h => .element "a" #[("href", h), ("class", "pilean-page-docs-link")]
                  (.element "code" #[] (txt e.name))
              | Option.none => .element "code" #[] (txt e.name)
            .element "li" #[] (.seq #[name, txt " ", el "span" "pilean-page-module"
              (txt s!"({e.module})")]))),
          if d.externalOmitted > 0 then el "p" "pilean-page-note"
            (txt s!"and {d.externalOmitted} more (at most {externalCap} are listed).") else .empty])
      let body : Html := .seq #[
        el "p" "pilean-page-note" (txt "The declaration that draws the figure:"), own,
        if rel.isEmpty && d.more.isEmpty then .empty else
          el "p" "pilean-page-note" (txt relatedIntroText),
        .seq rel, more, ext]
      -- long code is folded, so that it does not push the rest of the page down
      let shown := #[d.figure] ++ d.related
      let lines := shown.foldl (fun n r => n + shownLines r) 0
      let body := if lines ≤ codeFoldAbove then body
        else .element "details" #[("class", "pilean-page-code-fold")] (.seq #[
          .element "summary" #[] (txt s!"Show the code: {shown.size} \
            {if shown.size == 1 then "declaration" else "declarations"}, {lines} lines"), body])
      pure <| el "section" "pilean-page-codes" (.seq #[
        el "h2" "pilean-page-h" (txt "Code"), body]) #[("id", s!"{idBase}-code")]
  -- provenance
  let pr := site.provenance
  let row (k : String) (v : Html) : Html := .seq #[.element "dt" #[] (txt k), .element "dd" #[] v]
  let fileRows := verdicts.map fun (f, v) =>
    let entry := f.built.entry
    let verdict := match v with
      | .ok => s!"ok{recordedStanding entry}"
      | v => v.text
    el "li" "pilean-page-prov-file" (.seq #[
      .element "code" #[] (txt entry.path),
      .element "dl" #[("class", "pilean-page-facts")] (.seq #[
        row "Fingerprint" (fingerprintHtml entry.fingerprint),
        row "SHA-256" (.element "code" #[] (txt entry.sha256)),
        row "Renderer" (.element "code" #[] (txt f.renderer)),
        row "Text engine" (if f.textEngine.isEmpty then txt "PILean's built-in lettering"
          else .element "code" #[] (txt f.textEngine)),
        row "pilean-verify" (el "span" "pilean-page-verdict" (txt verdict)
          #[("data-verdict", v.text)])])])
  let packages := pr.packages.map fun (n, r) => .seq #[.element "code" #[] (txt n), txt s!" {r}"]
  let commit : Html := match pr.commit with
    | some c => .element "code" #[] (txt c)
    | Option.none => txt "not known (the site was not built from a Git checkout, or no commit was given)"
  let ci : Html := match pr.ciRun with
    | some h => .element "a" #[("href", h), ("class", "pilean-page-ci-link")]
        (txt "The continuous-integration run that built this site")
    | Option.none => txt "not built in continuous integration"
  let provenance := el "section" "pilean-page-provenance" (.seq #[
    el "h2" "pilean-page-h" (txt "Provenance"),
    .element "dl" #[("class", "pilean-page-facts")] (.seq #[
      row "Declaration" (.seq #[s.decl decl, txt " ",
        declPlaceHtml o ((data.map (·.figure)).getD
          { name := decl, module := fig.source.module, file := fig.source.file,
            line := fig.source.line })]),
      row "Lean" (.element "code" #[] (txt pr.toolchain)),
      row "PILean" (.element "code" #[] (txt pr.pileanVersion)),
      row "Packages" (if packages.isEmpty then txt "not recorded"
        else .seq ((packages.toList.intersperse (txt "; ")).toArray)),
      row "Commit" commit,
      row "Build" ci,
      row "Manifest" (.element "a" #[("href", fileUrl manifestName)] (txt manifestName))]),
    el "p" "pilean-page-note" (txt "Each file of the figure, with what pilean-verify says of it \
      against the site's manifest (the file's size, SHA-256, format and source record) and the \
      standing the file records:"),
    folded "files with what pilean-verify says of each" (el "ul" "pilean-page-prov-files"
      (.seq fileRows))]) #[("id", s!"{idBase}-provenance")]
  -- reproduce
  let gen := if pr.generator.isEmpty then "GENERATOR" else pr.generator
  let flags := " ".intercalate pr.flags.toList
  let flags := if flags.isEmpty then "" else " " ++ flags
  let dir := s!"_out/html-multi/-verso-data/{figureFolder}"
  let cmds := (match pr.commit with
    | some c => s!"git checkout {c}\n"
    | Option.none => "") ++ s!"lake build {gen}\nlake exe {gen} --output _out{flags}\n\
      lake exe pilean-verify {dir}\nlake exe {gen} --check-figures {dir}{flags}"
  let reproduce := el "section" "pilean-page-reproduce" (.seq #[
    el "h2" "pilean-page-h" (txt "How to reproduce"),
    el "p" "pilean-page-note" (txt "From the repository's checkout of the site's project: build \
      the site again, check the folder against its manifest, and check that it holds exactly what \
      the build draws now."),
    plainBlock cmds]) #[("id", s!"{idBase}-reproduce")]
  -- record what the page states
  let path := ((reg.pages.find? (·.decl == decl)).map (·.path)).getD #[]
  let stated : PageStated := {
    path, standing := (fig.standing.word, fig.standing.theorems),
    files := verdicts.map fun (f, v) =>
      (f.built.entry.path, f.built.entry.bytes, f.built.entry.sha256, v.text) }
  -- one page per file in the multi-page output; the single-page output, whose traversal gives
  -- every part the empty path, is not what the check after the build reads
  unless path.isEmpty do (pageStatedRef.modify (·.insert decl stated) : IO _)
  let cls := if hasDark then "pilean-figure-page pilean-figure-has-dark" else "pilean-figure-page"
  pure <| el "div" cls (.seq #[anchor,
      el "div" "pilean-page-picture" (el "div" "pilean-figure-frame" picture),
      el "h2" "pilean-page-h" (txt "Files"), downloads,
      heading, standing, animation, code, provenance, reproduce])
    #[("data-pilean-page", decl), ("data-pilean-standing", fig.standing.word),
      ("data-pilean-theorems", " ".intercalate fig.standing.theorems.toList), ("id", idBase)]

end PILeanVerso
