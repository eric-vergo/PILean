/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanVerso.Index
import PILeanVerso.Table

/-!
# The generator wrapper

A site's generator renders its figures with `withFigures`, around the generator it already has:

```lean
def main (args : List String) : IO UInt32 :=
  PILeanVerso.withFigures (%doc MyProject.Blueprint) site_figures% args fun args =>
    Informal.PreviewManifest.blueprintMainWithPreviewData (%doc MyProject.Blueprint) args
      (extensionImpls := by exact extension_impls%)
```

`withFigures` finds the figure blocks of the document, renders their figures (and nothing else)
with PILean, keeps the result for the blocks, runs the generator, and then checks that the
figures folder the generator wrote holds exactly the files of this render: a file that differs
from a fresh render or is missing fails the build; a file left from an earlier build is reported.

Its own command-line options are taken out before the generator sees the rest:

* `--figure-repo URL`, `--figure-commit SHA`, `--figure-source-prefix DIR/`: the repository, the
  commit and the folder of the sources in it, recorded in every file and used for the links to
  the source (the commit defaults to `git rev-parse HEAD` when a repository is given);
* `--check-figures DIR`: render the figures and compare them with the folder `DIR` (a site's
  `-verso-data/pilean-figures`, a published copy) as `pilean-build --check` does, without
  building the site: exit status 0 if it holds exactly the render, 1 otherwise;
* `--strict-figures`: also fail when the written folder has a file the render does not make.
-/

namespace PILeanVerso

open Lean Verso Doc Genre Manual PILean.Trust

/-- The figure declarations the blocks of `b` use, appended to `acc`. -/
partial def blockFigures (acc : Array String) (b : Doc.Block Manual) : Array String :=
  match b with
  | .other container contents =>
    let acc := if container.name == ``Block.figure then
        match (fromJson? container.data : Except String FigureData) with
        | .ok d => acc.push d.decl
        | .error _ => acc
      else acc
    contents.foldl blockFigures acc
  | .ul items | .ol _ items => items.foldl (fun a i => i.contents.foldl blockFigures a) acc
  | .dl items => items.foldl (fun a i => i.desc.foldl blockFigures a) acc
  | .blockquote bs | .concat bs => bs.foldl blockFigures acc
  | .para _ | .code _ => acc

/-- The figure declarations a document uses, in document order (repeated as often as used). -/
partial def usedFigures (p : Part Manual) : Array String :=
  p.subParts.foldl (fun acc s => acc ++ usedFigures s) (p.content.foldl blockFigures #[])

/-- What `withFigures` takes from the command line. -/
structure WrapperArgs where
  /-- The options of the site's figures. -/
  options : SiteOptions
  /-- `--check-figures DIR`. -/
  checkDir : Option System.FilePath := none
  /-- `--strict-figures`. -/
  strict : Bool := false
  /-- The arguments left for the generator. -/
  rest : List String := []

/-- Takes `withFigures`'s own options out of `args`, over the defaults `opts`. -/
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
    | a@"--figure-repo" :: [] | a@"--figure-commit" :: [] | a@"--figure-source-prefix" :: []
    | a@"--check-figures" :: [] => throw s!"{a} needs a value"
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

/-- Renders the figures `doc` uses from the table `figures` (`site_figures%`), runs the generator
`generate` on the remaining arguments, and checks the figures folders it wrote (see the module
doc). `options` are the defaults of the command-line options. -/
def withFigures (doc : Part Manual) (figures : Array FigureEntry) (args : List String)
    (generate : List String → IO UInt32) (options : SiteOptions := {}) : IO UInt32 := do
  let w ← match parseWrapperArgs options args with
    | .ok w => pure w
    | .error e => IO.eprintln s!"figures: {escapeControl e}"; return 2
  let opts ← if w.options.repo.isSome && w.options.commit.isNone then
      pure { w.options with commit := ← headCommit? }
    else pure w.options
  let used := usedFigures doc
  let site ← match renderSite figures used opts with
    | .ok s => pure s
    | .error e =>
      for l in e.splitOn "\n" do IO.eprintln s!"figures: {escapeControl l}"
      return 1
  if let some dir := w.checkDir then
    let lines ← site.checkFolder dir
    for l in lines do IO.println (escapeControl l)
    if lines.isEmpty then IO.println s!"ok: {site.files.size} figure files match"
    return if lines.isEmpty then 0 else 1
  siteRef.set (some site)
  let code ← generate w.rest
  siteRef.set none
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
  return if failed then 1 else code

end PILeanVerso
