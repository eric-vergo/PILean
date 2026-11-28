/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanVersoManual.Page

/-!
# The generator wrapper's work

`withFiguresFor` is what both adapters' `withFigures` do around a site's generator: it finds the
figures the document uses, renders them, adds a page for each below the figures page
(`withPages`), builds the highlighted source those pages show (`prepare`), runs the generator on
that document and then checks what it wrote: the figures folder against a fresh render, and each
figure's page against the render, the written manifest and `pilean-verify` (`checkPages`).

## Main definitions

* `partFigures`: the figures a document's blocks use
* `parseWrapperArgs`: the wrapper's own command-line options
* `withPages`, `checkPages`, `withFiguresFor`
* `ciRunHref?`, `drawingPackages`: what the pages say about the build
-/

namespace PILeanVerso

open Lean Verso Doc Genre Manual PILean PILean.Trust


open Verso.Genre (Manual) in
/-- The figures the blocks of `b` use, appended to `acc`: the blocks whose name is in `names` and
whose data is a `FigureData`. -/
partial def blockFigures (names : Array Name) (acc : Array FigureUse) (b : Doc.Block Manual) :
    Array FigureUse :=
  match b with
  | .other container contents =>
    let acc := if names.contains container.name then
        match (fromJson? container.data : Except String FigureData) with
        | .ok d => acc.push { decl := d.decl, inline := d.inline, explorer := d.explorer,
                              proves := d.proves.map (·.name) }
        | .error _ => acc
      else acc
    contents.foldl (blockFigures names) acc
  | .ul items | .ol _ items =>
    items.foldl (fun a i => i.contents.foldl (blockFigures names) a) acc
  | .dl items => items.foldl (fun a i => i.desc.foldl (blockFigures names) a) acc
  | .blockquote bs | .concat bs => bs.foldl (blockFigures names) acc
  | .para _ | .code _ => acc

open Verso.Genre (Manual) in
/-- The figures the blocks named `names` of a document use, in document order (repeated as often
as used). -/
partial def partFigures (names : Array Name) (p : Part Manual) : Array FigureUse :=
  p.subParts.foldl (fun acc s => acc ++ partFigures names s)
    (p.content.foldl (blockFigures names) #[])

/-- What a generator wrapper takes from the command line. -/
structure WrapperArgs where
  /-- The options of the site's figures. -/
  options : SiteOptions
  /-- `--check-figures DIR`. -/
  checkDir : Option System.FilePath := none
  /-- `--strict-figures`. -/
  strict : Bool := false
  /-- Whether the figures' pages show highlighted source (`--figure-code highlight`, the
  default) or signatures only (`--figure-code signatures`, which runs no `lake build`). -/
  highlight : Bool := true
  /-- The arguments left for the generator. -/
  rest : List String := []

/-- Takes the wrapper's own options out of `args`, over the defaults `opts`. -/
def parseWrapperArgs (opts : SiteOptions) (args : List String) : Except String WrapperArgs := do
  let mut w : WrapperArgs := { options := opts }
  let mut rest := args
  let mut kept : Array String := #[]
  for _ in [0:args.length + 1] do
    match rest with
    | [] => break
    | "--figure-repo" :: u :: r => w := { w with options.repo := some u }; rest := r
    | "--figure-commit" :: c :: r => w := { w with options.commit := some c }; rest := r
    | "--figure-source-prefix" :: p :: r =>
      w := { w with options.sourcePrefix := p }; rest := r
    | "--check-figures" :: d :: r => w := { w with checkDir := some d }; rest := r
    | "--strict-figures" :: r => w := { w with strict := true }; rest := r
    | "--figure-allow-unchecked" :: r => w := { w with options.allowUnchecked := true }; rest := r
    | "--figure-code" :: "highlight" :: r => w := { w with highlight := true }; rest := r
    | "--figure-code" :: "signatures" :: r => w := { w with highlight := false }; rest := r
    | "--figure-code" :: m :: _ => throw s!"--figure-code {m}: expected highlight or signatures"
    | "--figure-inline-limit" :: n :: r =>
      match n.toNat? with
      | some k => w := { w with options.inlineLimit := k }; rest := r
      | Option.none => throw s!"--figure-inline-limit {n}: expected a number of bytes"
    | "--figure-lean-links" :: m :: r =>
      match LeanLinks.ofString? m with
      | some k => w := { w with options.leanLinks := k }; rest := r
      | Option.none => throw s!"--figure-lean-links {m}: expected ideil, site or none"
    | a@"--figure-repo" :: [] | a@"--figure-commit" :: [] | a@"--figure-source-prefix" :: []
    | a@"--check-figures" :: [] | a@"--figure-inline-limit" :: []
    | a@"--figure-lean-links" :: [] | a@"--figure-code" :: [] => throw s!"{a} needs a value"
    | a :: r => kept := kept.push a; rest := r
  return { w with rest := kept.toList }

/-- The folder the generator writes with `args` (`--output DIR`, the last one; `_out` without). -/
def outputDir (args : List String) : System.FilePath := Id.run do
  let mut out : System.FilePath := "_out"
  let mut rest := args
  for _ in [0:args.length + 1] do
    match rest with
    | "--output" :: d :: r => out := d; rest := r
    | _ :: r => rest := r
    | [] => break
  return out

/-- The commit of the working directory's Git checkout, if it has one. -/
def headCommit? : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"] }
    let c := out.stdout.trimAscii.toString
    return if out.exitCode == 0 && isCommit c then some c else none
  catch _ => return none

/-- The address of a GitHub Actions run from the values of `GITHUB_SERVER_URL`,
`GITHUB_REPOSITORY` and `GITHUB_RUN_ID`, when all three are there and well formed: an `https://`
server that is a host name only, a repository `owner/name` of letters, digits, `-`, `_` and `.`,
and a numeric run; `none` otherwise. -/
def ciRunHrefOf (server repo run : Option String) : Option String := do
  let server ← server
  let repo ← repo
  let run ← run
  let host := (server.drop 8).toString
  let hostOk := server.startsWith "https://" && !host.isEmpty && host.length ≤ 253 &&
    host.all fun c => c.isAlphanum || c == '.' || c == '-'
  let parts := repo.splitOn "/"
  let repoOk := parts.length == 2 && repo.length ≤ 200 &&
    parts.all (fun p => !p.isEmpty && p != "." && p != "..") &&
    repo.all fun c => c.isAlphanum || c == '-' || c == '_' || c == '.' || c == '/'
  let runOk := !run.isEmpty && run.length ≤ 20 && run.all Char.isDigit
  if hostOk && repoOk && runOk then some s!"{server}/{repo}/actions/runs/{run}" else none

/-- The continuous-integration run that is building the site (`ciRunHrefOf` of the
environment); `none` outside GitHub Actions. -/
def ciRunHref? : IO (Option String) :=
  return ciRunHrefOf (← IO.getEnv "GITHUB_SERVER_URL") (← IO.getEnv "GITHUB_REPOSITORY")
    (← IO.getEnv "GITHUB_RUN_ID")

/-- The revisions of the packages that draw the pictures (`pilean`, `leantex`) in the workspace's
`lake-manifest.json` in the working directory (a regular file of at most 1 MiB): the revision of a
Git dependency, or `a folder of the workspace` for a path dependency. Empty if there is no
readable manifest. -/
def drawingPackages : IO (Array (String × String)) := do
  try
    let p : System.FilePath := "lake-manifest.json"
    let md ← p.symlinkMetadata
    if md.type != .file || md.byteSize > 1024 * 1024 then return #[]
    let .ok j := Lean.Json.parse (← IO.FS.readFile p) | return #[]
    let .ok (pkgs : Array Lean.Json) := j.getObjValAs? (Array Lean.Json) "packages" | return #[]
    let mut out := #[]
    for pkg in pkgs do
      let .ok name := pkg.getObjValAs? String "name" | continue
      unless name == "pilean" || name == "leantex" do continue
      match pkg.getObjValAs? String "type", pkg.getObjValAs? String "rev" with
      | .ok "git", .ok rev =>
        if isCommit rev then out := out.push (name, s!"at {rev}")
      | .ok "path", _ => out := out.push (name, "from a folder of the workspace")
      | _, _ => pure ()
    return out
  catch _ => return #[]

/-- `s` as one word of a POSIX shell command: as it is when it has only letters, digits and
`-_./:=@+,`, in single quotes otherwise. -/
def shellWord (s : String) : String :=
  let safe := ['-', '_', '.', '/', ':', '=', '@', '+', ',']
  if !s.isEmpty && s.toList.all (fun (c : Char) => c.isAlphanum || safe.contains c) then s
  else "'" ++ s.replace "'" "'\\''" ++ "'"

/-- The figure options of a build that change its files or links, as a command line repeats them. -/
def figureFlags (o : SiteOptions) : Array String :=
  (match o.repo with | some r => #["--figure-repo", shellWord r] | Option.none => #[]) ++
  (match o.commit with | some c => #["--figure-commit", c] | Option.none => #[]) ++
  (if o.sourcePrefix.isEmpty then #[] else #["--figure-source-prefix", shellWord o.sourcePrefix]) ++
  (if o.allowUnchecked then #["--figure-allow-unchecked"] else #[])

/-- How a genre's adapter puts figure pages into a document: the names of its figure blocks and
of its figures page's block, the figures page's block, and a figure's page block. -/
structure PageBlocks where
  /-- The names of the genre's figure blocks (explorers' among them). -/
  figures : Array Name
  /-- The name of the block of the figures page (`{figure_list}`). -/
  listName : Name
  /-- The block of the figures page. -/
  list : Doc.Block Manual
  /-- The page block of a figure, from its declaration's name and whether the document shows it
  as an explorer (whose page then carries the explorers' script and stylesheet). -/
  page : String → Bool → Doc.Block Manual

/-- Whether a block is, or holds, the block named `n`. -/
partial def hasBlock (n : Name) : Doc.Block Manual → Bool
  | .other b cs => b.name == n || cs.any (hasBlock n)
  | .concat bs | .blockquote bs => bs.any (hasBlock n)
  | _ => false

/-- The page of the figure `decl` (`explorer`: shown as an explorer in the document): an
unnumbered part titled with the name, in the file `pageSlug decl`, holding the figure's page
block. -/
def pagePart (b : PageBlocks) (decl : String) (explorer : Bool) : Part Manual :=
  { title := #[.text decl], titleString := decl,
    metadata := some { number := false, file := some (pageSlug decl) },
    content := #[b.page decl explorer], subParts := #[] }

/-- An unnumbered part "Figures" with the figures page's block and the parts `pages` below it. -/
def figuresPart (b : PageBlocks) (pages : Array (Part Manual)) : Part Manual :=
  { title := #[.text "Figures"], titleString := "Figures", metadata := some { number := false },
    content := #[b.list], subParts := pages }

/-- The document with a page for each of the figures `decls`, below the figures page (the page of
one of `explorers`, the figures the document shows as explorers, with their script): the
top-level part that holds the figures page's block, or a part "Figures" with that block added at
the end of the document when it has none. -/
def withPages (b : PageBlocks) (doc : Part Manual) (decls : Array String)
    (explorers : Array String := #[]) : Part Manual :=
  if decls.isEmpty then doc else
  let pages := decls.map fun d => pagePart b d (explorers.contains d)
  match doc.subParts.findIdx? (·.content.any (hasBlock b.listName)) with
  | some i =>
    let p := doc.subParts[i]!
    let p' : Part Manual := { p with subParts := p.subParts ++ pages }
    { doc with subParts := doc.subParts.set! i p' }
  | Option.none =>
    { doc with subParts := doc.subParts.push (figuresPart b pages) }

/-- The declarations of the figures `used`, each once, in the order of their first use. -/
def usedDecls (used : Array FigureUse) : Array String :=
  used.foldl (init := #[]) fun acc u => if acc.contains u.decl then acc else acc.push u.decl

/-- The modules whose highlighted source the pages of the figures `decls` show. -/
def pageModules (site : SiteRender) (decls : Array String) : Array Name :=
  decls.foldl (init := #[]) fun acc d =>
    match site.pages[d]? with
    | some p =>
      let ms := #[p.figure.module] ++ p.theorems.map (·.decl.module) ++ p.related.map (·.module)
      ms.foldl (fun acc m => if acc.contains m.toName then acc else acc.push m.toName) acc
    | Option.none => acc

/-- Why the page data of a figure cannot be shown with its standing, if it cannot: a linked
figure's page must hold each theorem of the standing, and no other. -/
def pageDataProblem? (decl : String) (fig : SiteFigure) (data : Option FigurePageData) :
    Option String :=
  match fig.standing, data with
  | .linked ts, some d =>
    if d.theorems.map (·.decl.name) == ts then none
    else some s!"{decl}: the page data's theorems are not those of the figure's standing"
  | .linked _, Option.none => some s!"{decl}: it has linked theorems, but the table of figures \
      holds no page data for it (use site_figures%)"
  | .illustration _, some d =>
    if d.theorems.isEmpty then none
    else some s!"{decl}: the page data names theorems of an illustration"
  | .illustration _, Option.none => none

/-- The problems of the pages written below `out` (`<out>/html-multi`) for the figures `decls`
of the render `site`: each has a page whose file is there and carries its standing; what the page
states (`pageStatedRef`) is the render's standing and files, every verdict it shows is `ok`; and
the written figures folder, checked as `pilean-verify` checks it, holds each file of the figure
with that verdict and the standing the page states. -/
def checkPages (site : SiteRender) (decls : Array String) (out : System.FilePath) :
    IO (Array String) := do
  let root := out / "html-multi"
  unless ← root.pathExists do return #[]
  let stated ← pageStatedRef.get
  let verified ← verifyDirEntries (root / "-verso-data" / figureFolder)
  let mut problems := #[]
  for d in decls do
    let some fig := site.figures[d]? | continue
    let some s := stated[d]? | problems := problems.push s!"{d}: no page was written for it"; continue
    let word := (fig.standing.word, fig.standing.theorems)
    if s.standing != word then
      problems := problems.push s!"{d}: its page states the standing {s.standing.1}, the render \
        has {word.1}"
    let want := fig.files.map fun f => (f.built.entry.path, f.built.entry.bytes, f.built.entry.sha256)
    if s.files.map (fun (p, b, h, _) => (p, b, h)) != want then
      problems := problems.push s!"{d}: its page lists other files than the render"
    for (p, _, _, v) in s.files do
      if v != "ok" then problems := problems.push s!"{d}: its page shows the verdict {v} for {p}"
    if s.path.isEmpty || s.path.any (fun c => c.isEmpty || c == "." || c == ".." ||
        c.any (· == '/')) then
      problems := problems.push s!"{d}: its page has no usable path"
    else
      let file := (s.path.foldl (· / ·) root) / "index.html"
      let text ← try IO.FS.readFile file catch _ => pure ""
      if (text.splitOn s!"data-pilean-standing=\"{word.1}\"").length != 2 then
        problems := problems.push s!"{d}: its page file does not carry its standing once"
    match verified with
    | .error e => problems := problems.push s!"{d}: the figures folder cannot be verified: {e}"
    | .ok rows =>
      for f in fig.files do
        let path := f.built.entry.path
        match rows.find? (·.1 == path) with
        | some (_, .ok, some m) =>
          if m.standing != some word.1 || m.sha256 != f.built.entry.sha256 then
            problems := problems.push s!"{d}: the written manifest differs from its page for {path}"
        | some (_, v, _) =>
          problems := problems.push s!"{d}: pilean-verify says {v.text} for {path}, its page ok"
        | Option.none => problems := problems.push s!"{d}: {path} is not in the written manifest"
  return problems

/-- Renders the figures the document `doc` uses (its blocks named in `blocks.figures`) from the
table `figures` (`site_figures%`), adds a page for each (`withPages`), runs the generator
`generate` on that document and the remaining arguments, and checks what it wrote: a figures
folder that differs from a fresh render or misses a file fails, a file left from an earlier build
is reported (and fails with `--strict-figures`), and so does a page whose statements differ from
the render, the written manifest or `pilean-verify` (`checkPages`). `options` are the defaults of
the command-line options, `ciRun` finds the continuous-integration run. With the link mode `site`,
a declaration the pages name and the site has no place for is reported as a warning. -/
def withFiguresFor (blocks : PageBlocks) (doc : Part Manual) (figures : SiteFigures)
    (args : List String) (generate : Part Manual → List String → IO UInt32)
    (options : SiteOptions := {}) (ciRun : IO (Option String) := ciRunHref?) : IO UInt32 := do
  let used := partFigures blocks.figures doc
  let w ← match parseWrapperArgs options args with
    | .ok w => pure w
    | .error e => IO.eprintln s!"figures: {escapeControl e}"; return 2
  let opts ← if w.options.repo.isSome && w.options.commit.isNone then
      pure { w.options with commit := ← headCommit? }
    else pure w.options
  let pages ← match figures.pages with
    | .ok p => pure p
    | .error e => IO.eprintln s!"figures: the table's page data cannot be read: {escapeControl e}"
                  return 1
  let site ← match renderSite figures.entries used opts with
    | .ok s => pure { s with pages }
    | .error e =>
      for l in e.splitOn "\n" do IO.eprintln s!"figures: {escapeControl l}"
      return 1
  let decls := usedDecls used
  let dataProblems := decls.filterMap fun d =>
    (site.figures[d]?).bind fun f => pageDataProblem? d f site.pages[d]?
  if !dataProblems.isEmpty then
    for l in dataProblems do IO.eprintln s!"figures: {escapeControl l}"
    return 1
  for l in site.warnings do IO.eprintln s!"figures: warning: {escapeControl l}"
  if let some dir := w.checkDir then
    let lines ← site.checkFolder dir
    for l in lines do IO.println (escapeControl l)
    if lines.isEmpty then IO.println s!"ok: {site.files.size} figure files match"
    return if lines.isEmpty then 0 else 1
  if w.highlight && !decls.isEmpty then
    for l in ← prepare (pageModules site decls) do
      IO.eprintln s!"figures: warning: {escapeControl l}"
  let generator := ((← IO.appPath).fileName.getD "").takeWhile
    (fun c => c.isAlphanum || c == '-' || c == '_' || c == '.') |>.toString
  let site := { site with provenance := {
    toolchain := Lean.versionString, pileanVersion := PILean.version,
    packages := ← drawingPackages, commit := opts.commit <|> (← headCommit?),
    generator, flags := figureFlags opts, ciRun := ← ciRun } }
  siteRef.set (some site)
  unlinkedRef.set {}
  pageStatedRef.set {}
  let explorers := usedDecls (used.filter (·.explorer))
  let code ← generate (withPages blocks doc decls explorers) w.rest
  siteRef.set none
  let unlinked := (← unlinkedRef.get).toArray.qsort (· < ·)
  unlinkedRef.set {}
  for n in unlinked do
    IO.eprintln s!"figures: warning: {escapeControl n} has no place in the site to link to; \
      it is shown without a link (--figure-lean-links site)"
  if code != 0 || site.files.isEmpty then return code
  let out := outputDir w.rest
  let mut failed := false
  let mut seen := false
  for flavour in ["html-multi", "html-single"] do
    let dir := out / flavour / "-verso-data" / figureFolder
    unless ← dir.pathExists do continue
    seen := true
    for l in ← site.checkFolder dir do
      let extra := l.startsWith "extra: "
      IO.eprintln s!"figures: {flavour}: {escapeControl l}{if extra then
        " (not made by this build; remove the folder and build again)" else ""}"
      if !extra || w.strict then failed := true
  if !seen then
    IO.eprintln s!"figures: no figures folder was written below {out}"
    failed := true
  if !failed then
    for l in ← checkPages site decls out do
      IO.eprintln s!"figures: page: {escapeControl l}"
      failed := true
  pageStatedRef.set {}
  return if failed then 1 else code

end PILeanVerso
