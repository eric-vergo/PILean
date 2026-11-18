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
   folder: it must exit 0; every core module must have its page; the figures folder must hold a
   manifest; every SVG figure must pass `PILean.Svg.isInert`; every page must name no file of the
   machine it was built on (no `/Users/` or `/home/`).
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
  let files ← filesBelow figs
  let svgs := files.filter (·.toString.endsWith ".svg")
  let mut inert : Bool := svgs.size > 0
  for f in svgs do
    unless PILean.Svg.isInert (← IO.FS.readFile f) do
      inert := false
      IO.println s!"  not inert: {f}"
  check inert s!"all {svgs.size} SVG figures are inert"
  let pages := (← filesBelow site).filter (·.toString.endsWith ".html")
  let mut clean := true
  for p in pages do
    let t ← IO.FS.readFile p
    if has t "/Users/" || has t "/home/" then
      clean := false
      IO.println s!"  names a machine path: {p}"
  check clean s!"none of the {pages.size} pages names a machine path"
  IO.FS.removeDirAll out
  let n ← failures.get
  IO.println (if n == 0 then "all checks passed" else s!"{n} checks failed")
  return if n == 0 then 0 else 1
