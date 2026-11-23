/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# The API reference's page files

What `lake exe pilean-manual-pages` writes and `lake test` checks: one file per module of PILean's
core (`PILeanManual/Api/<module path>.lean`, holding only the module's name and
`{apiModule …}`: the page's content is read from the environment when it is elaborated) and the
part that includes them (`PILeanManual/Api.lean`), which lists them grouped by the first component
below `PILean`.

The modules are the files `PILean.lean` and `PILean/**/*.lean` of the repository (the parent of
the manual's folder), found on disk, so a new module of the core needs a page before the check
passes.

## Main definitions

* `coreModules`: the core's modules, from the files.
* `expected`: the files and their text.
* `stale`: the differences between the files on disk and `expected`.
-/

namespace PILeanManual.Pages

/-- The licence header of every generated file. -/
def header : String :=
  "/-\nReleased under Apache 2.0 license as described in the file LICENSE.\n" ++
  "Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)\n-/\n"

/-- The note under the imports of every generated file. -/
def note : String :=
  "-- Written by `lake exe pilean-manual-pages`; `lake test` fails when it is stale.\n"

/-- The `.lean` files below `dir`, as module name components relative to it, sorted. -/
partial def leanFiles (dir : System.FilePath) (pre : List String := []) :
    IO (Array (List String)) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then
      out := out ++ (← leanFiles e.path (pre ++ [e.fileName]))
    else if e.fileName.endsWith ".lean" then
      out := out.push (pre ++ [(e.fileName.dropEnd 5).toString])
  return out.qsort fun a b => ".".intercalate a < ".".intercalate b

/-- The core's modules, as their components, sorted: `PILean` and the files below `PILean/`. -/
def coreModules (repo : System.FilePath) : IO (Array (List String)) := do
  let below ← leanFiles (repo / "PILean")
  return #[["PILean"]] ++ below.map ("PILean" :: ·)

/-- The dotted name of a module. -/
def dotted (m : List String) : String := ".".intercalate m

/-- A module name as one Lean identifier, with `«»` around components that need it. -/
def ident (m : List String) : String :=
  ".".intercalate (m.map fun c =>
    if c.all (fun ch => ch.isAlphanum || ch == '_') && (c.front.isAlpha) then c else s!"«{c}»")

/-- The manual module of a core module's page: `PILeanManual.Api.PILean.Color`. -/
def pageModule (m : List String) : List String := ["PILeanManual", "Api"] ++ m

/-- The text of the page of module `m`. -/
def pageText (m : List String) : String :=
  header ++ "import VersoManual\nimport PILeanManual.ApiMeta\nimport " ++ ident m ++ "\n\n" ++
  note ++ "\nopen Verso.Genre Manual\nopen PILeanManual\n\n" ++
  s!"#doc (Manual) \"{dotted m}\" =>\n%%%\ntag := \"api-{dotted m}\"\n" ++
  s!"shortTitle := \"{dotted m}\"\n%%%\n\n" ++ "{apiModule " ++ ident m ++ "}\n"

/-- The group of a module: the first component below `PILean` (`Graph` for
`PILean.Graph.Layered`), or `PILean` for a module directly below it without a folder. -/
def group (all : Array (List String)) (m : List String) : String :=
  match m with
  | ["PILean"] => "PILean"
  | ["PILean", c] => if all.any (fun n => n.length > 2 && n[1]! == c) then c else "PILean"
  | _ :: c :: _ => c
  | _ => "PILean"

/-- The text of the part that includes every page, grouped (see `group`). -/
def indexText (mods : Array (List String)) : String := Id.run do
  let groups := mods.foldl (fun (acc : Array String) m =>
    let g := group mods m
    if acc.contains g then acc else acc.push g) #[]
  let mut s := header ++ "import VersoManual\nimport PILeanManual.ApiMeta\n" ++
    "import PILeanManual.ApiCoverage\n"
  for m in mods do
    s := s ++ "import " ++ ident (pageModule m) ++ "\n"
  s := s ++ "\n" ++ note ++ "\nopen Verso.Genre Manual\nopen PILeanManual\n\n" ++
    "#doc (Manual) \"API Reference\" =>\n%%%\ntag := \"api\"\n%%%\n\n" ++
    "One page for every module of the core, made from the library's docstrings when the\n" ++
    "manual is built: each page opens with the module's documentation and lists its public\n" ++
    "declarations in source order (what counts as public: {ref \"api-coverage\"}[What the Reference Covers]).\n"
  s := s ++ "\nThe modules, by the folder they are in:\n\n"
  for g in groups do
    let refs := (mods.filter (group mods · == g)).toList.map fun m =>
      "{ref \"api-" ++ dotted m ++ "\"}[`" ++ dotted m ++ "`]"
    s := s ++ s!"* *{g}*:\n  " ++ ",\n  ".intercalate refs ++ "\n"
  s := s ++ "\n{include 1 PILeanManual.ApiCoverage}\n"
  for m in mods do
    s := s ++ "\n{include 1 " ++ ident (pageModule m) ++ "}\n"
  return s

/-- The files the generator writes, relative to the manual's folder, with their text. -/
def expected (repo : System.FilePath) : IO (Array (System.FilePath × String)) := do
  let mods ← coreModules repo
  let pages := mods.map fun m =>
    let parts := pageModule m
    ((parts.dropLast.foldl (· / ·) ("." : System.FilePath)) / (parts.getLast! ++ ".lean"),
      pageText m)
  return pages.push (("." : System.FilePath) / "PILeanManual" / "Api.lean", indexText mods)

end PILeanManual.Pages

namespace PILeanManual.Pages

/-- The page files present below `PILeanManual/Api`, relative to the manual's folder. -/
def presentPages : IO (Array System.FilePath) := do
  let pageDir : System.FilePath := "." / "PILeanManual" / "Api"
  if ← pageDir.isDir then
    return (← leanFiles pageDir).map fun p =>
      (p.dropLast.foldl (fun (d : System.FilePath) (c : String) => d / c) pageDir) /
        (p.getLast! ++ ".lean")
  else return #[]

/-- The differences between the page files on disk and `expected ".."`: `missing: PATH`,
`stale: PATH` and `extra: PATH`, one line each. Run from the manual's folder. -/
def stale : IO (Array String) := do
  let files ← expected ".."
  let mut out := #[]
  for (path, text) in files do
    let cur ← if ← path.pathExists then some <$> IO.FS.readFile path else pure none
    if cur != some text then
      out := out.push s!"{if cur.isNone then "missing" else "stale"}: {path}"
  for p in ← presentPages do
    unless files.any (·.1 == p) do out := out.push s!"extra: {p}"
  return out

end PILeanManual.Pages
