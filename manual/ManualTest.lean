/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanManual.ApiScope
import PILeanManual.PageFiles
import PILean

/-!
# The manual's checks

`lake test` (run from the manual's folder) checks:

1. *The page files.* The API reference has exactly one page file per module of the core, and the
   files are what `lake exe pilean-manual-pages` writes (`PILeanManual.Pages.stale`).
2. *Coverage.* Every public declaration of every core module (`PILeanManual.publicDecls`) has
   its docstrings or is on the allow-list (`PILeanManual.apiAllowed?`). The counts are printed;
   any uncovered declaration fails the check, with its name. The environment is the core's, read
   from its built modules (`PILean` and `PILean.Trust.Attr`).
3. *A generated site.* The generator (`pilean-manual`, built first) writes the site into a scratch
   folder: it must exit 0; every core module must have its page; the figures folder must agree
   with its manifest as `pilean-verify` checks it (`PILean.Trust.verifyDir`: every listed file
   there, of its size, hash, format and source record, and no other file); every figure a page
   refers to must be a file of that manifest, and every file of the manifest must be referred
   to by a page; every SVG figure must pass `PILean.Svg.isInert`; every link must show text
   (`emptyLinks`); the coverage page must print the counts of step 2; and no page may name a
   path of the machine it was built on (`machinePaths`: the folders of this build and the home
   folder, and the usual forms of home and temporary folders on macOS, Linux and Windows).
4. *The whole program of Getting Started.* `FirstProgram/Main.lean`, which the page shows, is run
   with `lean --run` against the core's built library in a scratch folder, and must write its
   four files.

Each scanner is also run on a planted page that it must report.
-/

open Lean PILeanManual

/-- The files below `dir`, recursively. -/
partial def filesBelow (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← filesBelow e.path) else out := out.push e.path
  return out

/-- Whether `s` contains `t`. -/
def has (s t : String) : Bool := (s.splitOn t).length > 1

/-- The opening tags of the links in `html` that show no text: an `<a ` element with an `href`
whose content, with its tags removed, is empty or white space, that holds no image with a
non-empty `alt` text, and that has no `aria-label` and no `title` attribute either. -/
def emptyLinks (html : String) : Array String := Id.run do
  let mut out := #[]
  for piece in (html.splitOn "<a ").drop 1 do
    let tag := (piece.splitOn ">").head!
    if !has tag "href=" || has tag "aria-label=" || has tag "title=" then continue
    let content := ((piece.drop (tag.length + 1)).toString.splitOn "</a>").head!
    let mut text := ""
    let mut inTag := false
    for c in content.toList do
      if c == '<' then inTag := true
      else if c == '>' then inTag := false
      else if !inTag then text := text.push c
    let alts := ((content.splitOn "alt=\"").drop 1).map fun a => (a.splitOn "\"").head!
    if text.trimAscii.isEmpty && alts.all (·.trimAscii.isEmpty) then
      out := out.push ("<a " ++ tag ++ ">")
  return out

/-- The entries of `forbidden` (paths of the machine) that `text` names; empty entries are
skipped. -/
def machinePaths (text : String) (forbidden : Array String) : Array String :=
  forbidden.filter fun p => !p.isEmpty && has text p

/-- The figure files the pages refer to: every path after `pilean-figures/` up to a quote. -/
def figureRefs (html : String) : Array String :=
  ((html.splitOn "pilean-figures/").drop 1).toArray.map fun r =>
    ((r.splitOn "\"").head!.splitOn "'").head!

/-- The environment of the core's built modules (`PILean` and `PILean.Trust.Attr`). -/
unsafe def coverageEnv : IO Environment := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  importModules #[{ module := `PILean }, { module := `PILean.Trust.Attr }] {} (loadExts := true)

/-- The coverage of the core's API in the environment `env`. -/
def coverage (env : Environment) : IO (Nat × Nat × Nat × Nat × Array Name) := do
  let ctx : Core.Context := { fileName := "<coverage>", fileMap := default }
  let (r, _) ← (coverageCounts.run ctx { env }).toIO (fun _ => IO.userError "coverage failed")
  return r

/-- Runs the checks; exit status 0 when all hold. -/
unsafe def main : IO UInt32 := do
  let failures ← IO.mkRef 0
  let check (ok : Bool) (what : String) : IO Unit := do
    unless ok do failures.modify (· + 1)
    IO.println s!"{if ok then "ok" else "FAIL"}: {what}"
  -- 1. the page files
  let bad ← Pages.stale
  for l in bad do IO.println s!"  {l}"
  check bad.isEmpty "the API reference's page files are current"
  -- 2. coverage
  let env ← coverageEnv
  let (mods, total, documented, allowed, gaps) ← coverage env
  IO.println s!"coverage: {mods} modules, {total} public declarations, {documented} documented, \
    {allowed} allowed, {gaps.size} uncovered"
  for g in gaps do IO.println s!"  uncovered: {g}"
  check (gaps.isEmpty && total == documented + allowed && total > 0)
    "every public declaration of the core is documented or allowed"
  check (apiAllowed? env `PILean.Rgba.hex).isNone
    "the allow-list does not accept a definition that is not on it"
  let fileMods ← Pages.coreModules ".."
  check (mods == fileMods.size) s!"the environment has the core's {fileMods.size} modules"
  -- 3. a generated site
  let out : System.FilePath := ".lake" / s!"pilean-manual-test-{← IO.monoNanosNow}"
  let child ← IO.Process.spawn
    { cmd := "./.lake/build/bin/pilean-manual", args := #["--output", out.toString] }
  let code ← child.wait
  check (code == 0) "the manual is generated"
  let site := out / "html-multi"
  for m in fileMods do
    let dir := site / "API-Reference" / ("___".intercalate m)
    check (← (dir / "index.html").pathExists) s!"{Pages.dotted m} has its page"
  let figs := site / "-verso-data" / "pilean-figures"
  check (← (figs / "manifest.json").pathExists) "the figures folder has its manifest"
  let verdicts ← PILean.Trust.verifyDir figs
  let listed : Array String := match verdicts with
    | .ok vs => (vs.filter (·.2 == .ok)).map (·.1)
    | .error _ => #[]
  match verdicts with
  | .ok vs => for (p, v) in vs do if v != .ok then IO.println s!"  {v.text}: {p}"
  | .error e => IO.println s!"  {e}"
  check ((verdicts.toOption.map (·.all (·.2 == .ok))).getD false && listed.size > 0)
    s!"the {listed.size} files of the figures folder agree with its manifest"
  let files ← filesBelow figs
  let svgs := files.filter (·.toString.endsWith ".svg")
  let mut inert : Bool := svgs.size > 0
  for f in svgs do
    unless PILean.Svg.isInert (← IO.FS.readFile f) do
      inert := false
      IO.println s!"  not inert: {f}"
  check inert s!"all {svgs.size} SVG figures are inert"
  let pages := (← filesBelow site).filter (·.toString.endsWith ".html")
  let here ← IO.currentDir
  let repo ← IO.FS.realPath ".."
  let forbidden := #["/Users/", "/home/", "/root/", "/private/var/folders/", "/var/folders/",
    "/private/tmp/", "C:\\Users\\", "C:/Users/", "\\\\wsl", here.toString,
    (← IO.FS.realPath here).toString, repo.toString, ((← IO.getEnv "HOME").getD "")]
  check (machinePaths "<p>built in /var/folders/x/T/a</p>" forbidden == #["/var/folders/"] &&
      (machinePaths s!"<code>{repo}/PILean.lean</code>" forbidden).contains repo.toString &&
      emptyLinks "<p>see (<a href=\"x/#y\"></a>)</p>" == #["<a href=\"x/#y\">"] &&
      (emptyLinks "<a href=\"x\"><code>y</code></a><a href=\"z\" title=\"z\"></a>").isEmpty &&
      emptyLinks "<a href=\"i\"><img src=\"f.svg\" alt=\"\"></a>" == #["<a href=\"i\">"] &&
      (emptyLinks "<a href=\"i\"><img src=\"f.svg\" alt=\"a plot\"></a>").isEmpty)
    "the scanners report a planted machine path and a planted empty link"
  let mut clean := true
  let mut linked := true
  let mut referred : Std.HashSet String := {}
  let mut coveragePrinted := false
  let coverageText := s!"the {mods} modules of the core had {total} public declarations: \
    {documented} with docstrings, {allowed} on the allow-list, none uncovered."
  for p in pages do
    let t ← IO.FS.readFile p
    for m in machinePaths t forbidden do
      clean := false
      IO.println s!"  names the machine path {m}: {p}"
    for l in emptyLinks t do
      linked := false
      IO.println s!"  a link without text in {p}: {l}"
    for r in figureRefs t do referred := referred.insert r
    if has t coverageText then coveragePrinted := true
  check clean s!"none of the {pages.size} pages names a path of this machine"
  check linked s!"every link of the {pages.size} pages shows text"
  let unknown := referred.toArray.filter fun r => r != "manifest.json" && !listed.contains r
  let unused := listed.filter (!referred.contains ·)
  for r in unknown do IO.println s!"  a page refers to a figure the manifest does not list: {r}"
  for r in unused do IO.println s!"  no page refers to the figure {r}"
  check (unknown.isEmpty && unused.isEmpty && referred.size > 0)
    s!"the pages refer to exactly the {listed.size} figure files of the manifest"
  check coveragePrinted "the coverage page prints the counts of the coverage check"
  IO.FS.removeDirAll out
  -- 4. the whole program of Getting Started
  let run : System.FilePath := ".lake" / s!"pilean-manual-program-{← IO.monoNanosNow}"
  IO.FS.createDirAll run
  let lean := (← findSysroot) / "bin" / "lean"
  let mainFile ← IO.FS.realPath ("FirstProgram" / "Main.lean")
  let libPath := (repo / ".lake" / "build" / "lib" / "lean").toString
  let prog ← IO.Process.output
    { cmd := lean.toString, cwd := run, args := #["--run", mainFile.toString],
      env := #[("LEAN_PATH", some libPath)] }
  unless prog.exitCode == 0 do IO.println s!"  {prog.stderr.trimAscii}"
  let mut written := prog.exitCode == 0
  let svg := "<?xml".toUTF8
  let png := PILean.Png.pngSignature
  for (f, start) in [("trig.svg", svg), ("trig-dark.svg", svg), ("trig.png", png),
      ("banner.png", png)] do
    let ok ← try pure ((← IO.FS.readBinFile (run / f)).extract 0 start.size == start)
      catch _ => pure false
    unless ok do written := false
  check written "the whole program of Getting Started runs and writes its four files"
  IO.FS.removeDirAll run
  let n ← failures.get
  IO.println (if n == 0 then "all checks passed" else s!"{n} checks failed")
  return if n == 0 then 0 else 1
