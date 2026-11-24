/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Trust.Manifest
import PILean.Trust.Files
import PILean.Pdf.Check

/-!
# `pilean-build`

Renders every `FigureEntry` of a project to a directory and writes the manifest, or checks that a
directory holds what a build produces. A project's driver is three lines:

```lean
import MyFigures
import PILean.Trust.Build
def main (args : List String) : IO UInt32 := PILean.Trust.buildMain figures% args
```

## Main definitions

* `BuildOptions`, `renderAll`: the files and the manifest of a build, in memory
* `build`: writes them, or with `check := true` compares them with the directory
* `buildMain`: the command line
  `[--out DIR] [--repo URL] [--commit SHA] [--check] [--require-standing]`
* `unmarkedIllustrations`: the figures `--require-standing` refuses

## Implementation notes

The output directory is created if needed and resolved once (`realPath`); every file is then
written, compared or listed below it without following a symbolic link (`writeInside`,
`locateInside`), so a link planted in the directory cannot make the build write or read
anywhere else. Every string from the directory is printed through `escapeControl`.
-/

namespace PILean.Trust

/-- What a build is given besides the entries and the directory. -/
structure BuildOptions where
  /-- The repository's URL, recorded in every file and in the manifest. -/
  repo : Option String := none
  /-- The commit, recorded the same way. -/
  commit : Option String := none
  /-- Compare with the directory instead of writing to it. -/
  check : Bool := false
  /-- Refuse to build or check when a figure is an illustration that its declaration does not
  mark as one (`Standing.unmarked`): every figure must have a linked theorem
  (`figure_links`) or carry `@[figure illustration]`. -/
  requireStanding : Bool := false

/-- A file of a build: its manifest entry and its bytes. -/
structure BuiltFile where
  /-- The manifest entry. -/
  entry : ManifestEntry
  /-- The bytes of the file, with the source information. -/
  bytes : ByteArray
deriving Inhabited

/-- Renders one output of an entry: the bytes with the source record of the entry (and the
fingerprint of the output's specification) inserted, and the manifest entry. Fails for an SVG
output with text the built-in lettering cannot draw (`Lettering.missing`), since the figure's
PNG, APNG or GIF would show a box for each such character; if the finished file is larger than
`maxOutputBytes`; if its bytes are not of the output's format (`detectedFormat?`), so that
every file of a build is one `pilean-verify` accepts; and, for a PDF, if the finished file fails
the structural check (`Pdf.check`). -/
def renderOutput (e : FigureEntry) (o : Output) (opts : BuildOptions) :
    Except String BuiltFile := do
  let path ← outputPath e.toSourceData o
  if o.format == .svg then
    let lacking := Lettering.missing (Lettering.svgText (String.fromUTF8? o.spec |>.getD ""))
    if !lacking.isEmpty then
      throw s!"{path}: the built-in lettering has no glyph for {String.ofList lacking}, which \
        the raster outputs would draw as boxes"
  let raw ← match o.bytes () with
    | .ok b => pure b
    | .error err => throw s!"{path}: {err}"
  if raw.size > maxOutputBytes then throw s!"{path}: the file is larger than {maxOutputBytes} bytes"
  let src := e.source o opts.repo opts.commit
  let bytes ← (withSource raw src).mapError (s!"{path}: " ++ ·)
  if bytes.size > maxOutputBytes then
    throw s!"{path}: the file with its source record is larger than {maxOutputBytes} bytes"
  if detectedFormat? bytes != some o.format.name then
    throw s!"{path}: the bytes are not a file of the format {o.format.name}"
  if o.format == .pdf then
    if let .error err := Pdf.check bytes then throw s!"{path}: the PDF is malformed: {err}"
  let m : ManifestEntry := {
    path, format := o.format.name, bytes := bytes.size, sha256 := Sha256.hex (Sha256.hash bytes),
    fingerprint := (src.fingerprint.getD ""), module := e.module, decl := e.decl, file := e.file,
    line := e.line, column := e.column, version := src.version, repo := opts.repo,
    commit := opts.commit, darkColours := (o.theme ()).1, darkOpacities := (o.theme ()).2,
    standing := src.standing, theorems := src.theorems }
  return { entry := m, bytes }

/-- The declarations of the entries whose figure is an illustration not marked as one
(`Standing.unmarked`), in the entries' order. -/
def unmarkedIllustrations (entries : Array FigureEntry) : Array String :=
  entries.filterMap fun e => if e.standing.unmarked then some e.decl else none

/-- Every file of a build, sorted by path. With `opts.requireStanding`, fails first, before
anything is rendered, with one message for each figure of `unmarkedIllustrations`. Fails with all
the messages (one per line) if there
are more than `maxEntries` entries or more than `maxManifestFiles` outputs in all (checked
before anything is rendered), a figure cannot be rendered, a file is too large or not of its
format, or two files have the same path. -/
def renderAll (entries : Array FigureEntry) (opts : BuildOptions := {}) :
    IO (Except String (Array BuiltFile)) := do
  if entries.size > maxEntries then
    return .error s!"more than {maxEntries} figures"
  if opts.requireStanding then
    let bad := unmarkedIllustrations entries
    if !bad.isEmpty then
      return .error ("\n".intercalate (bad.toList.map fun d => s!"{d} is an illustration without \
        the marking @[figure illustration]: link a theorem about it with figure_links, or mark \
        it"))
  if entries.foldl (fun n e => n + (e.outputs ()).size) 0 > maxManifestFiles then
    return .error s!"more than {maxManifestFiles} files, more than a manifest may list"
  let mut files : Array BuiltFile := #[]
  let mut errors : Array String := #[]
  for e in entries do
    for o in e.outputs () do
      for w in o.problems () do
        IO.eprintln s!"pilean-build: warning: {escapeControl e.decl}: {escapeControl w}"
      match renderOutput e o opts with
      | .ok f => files := files.push f
      | .error err => errors := errors.push err
  files := files.sortStable fun a b => a.entry.path < b.entry.path
  for i in [1:files.size] do
    if files[i - 1]!.entry.path == files[i]!.entry.path then
      errors := errors.push s!"two outputs have the path {files[i]!.entry.path}"
  if errors.isEmpty then return .ok files else return .error ("\n".intercalate errors.toList)

/-- Whether the file at `rel` below `root` holds exactly `bytes`: it must be a regular file with
no symbolic link on its way, and its size is read first, so a large file of the wrong size is
never read. -/
def sameFile (root : System.FilePath) (rel : String) (bytes : ByteArray) : IO Bool := do
  match ← locateInside root rel with
  | .ok (some p) =>
    match ← readRegular p bytes.size (followLinks := false) with
    | .ok b => return b == bytes
    | .error _ => return false
  | _ => return false

/-- The lines `check` prints for a directory (already resolved): `missing: PATH` for a file of
the build that is not there, `stale: PATH` for one whose bytes differ (the manifest included) or
that is not a regular file reached without links, `extra: PATH` for a file below the directory
that the build does not make (other than `manifest.json`; a symbolic link counts as a file). The
files of the build come in the order of their paths, the manifest last, then the extra files
sorted, or, if the directory cannot be listed completely (`listFiles`), one line
`cannot check: REASON` in their place; the result is empty only if the directory holds exactly
what the build makes. -/
def checkLines (files : Array BuiltFile) (manifest : ByteArray) (outDir : System.FilePath) :
    IO (Array String) := do
  let mut lines : Array String := #[]
  let expected : Array (String × ByteArray) :=
    files.map (fun f => (f.entry.path, f.bytes)) ++ #[(manifestName, manifest)]
  for (path, bytes) in expected do
    match ← locateInside outDir path with
    | .ok none => lines := lines.push s!"missing: {path}"
    | _ => if !(← sameFile outDir path bytes) then lines := lines.push s!"stale: {path}"
  if ← outDir.pathExists then
    match ← listFiles outDir with
    | .error e => lines := lines.push s!"cannot check: {e}"
    | .ok present =>
      let known : Std.HashSet String := expected.foldl (fun s (p, _) => s.insert p) {}
      for r in present do
        if !known.contains r then lines := lines.push s!"extra: {r}"
  return lines

/-- Builds into `outDir` (`opts.check = false`): creates it if needed, resolves it, and writes
every file and `manifest.json` below it with `writeInside`, one line `path` for each. With
`opts.check`: prints the lines of `checkLines`, or `ok` if there are none. The result is 1 if a
figure cannot be rendered or a file cannot be written (a message goes to standard error) or if
`check` printed a line, and 0 otherwise; the messages of a build that fails go to standard error
one per line. -/
def build (entries : Array FigureEntry) (outDir : System.FilePath) (opts : BuildOptions := {}) :
    IO UInt32 := do
  match ← renderAll entries opts with
  | .error msg =>
    for line in msg.splitOn "\n" do
      IO.eprintln s!"pilean-build: {escapeControl line}"
    return 1
  | .ok files =>
    let manifest := (Manifest.render (files.map (·.entry))).toUTF8
    if opts.check then
      let root ← if ← outDir.pathExists then IO.FS.realPath outDir else pure outDir
      let lines ← checkLines files manifest root
      for l in lines do IO.println (escapeControl l)
      if lines.isEmpty then IO.println s!"ok: {files.size} files match"
      return if lines.isEmpty then 0 else 1
    else
      IO.FS.createDirAll outDir
      let root ← IO.FS.realPath outDir
      let outputs := files.map (fun f => (f.entry.path, f.bytes)) ++ #[(manifestName, manifest)]
      for (path, bytes) in outputs do
        match ← writeInside root path bytes with
        | .ok () => IO.println path
        | .error e =>
          IO.eprintln s!"pilean-build: {escapeControl e}"
          return 1
      return 0

/-- The usage text of `pilean-build`. -/
def buildUsage : String :=
  "usage: pilean-build [--out DIR] [--repo URL] [--commit SHA] [--check] [--require-standing]"

/-- Whether the string is 4 to 64 lowercase hexadecimal digits, as a commit is. -/
def isCommit (s : String) : Bool :=
  4 ≤ s.length && s.length ≤ 64 && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- The options of a command line, or a message: `--out DIR` (default `figures`), `--repo URL`
(`http` or `https`, see `safeLink?`), `--commit SHA` (`isCommit`), `--check`,
`--require-standing`. -/
def parseArgs (args : List String) :
    Except String (System.FilePath × BuildOptions) := do
  let mut out : System.FilePath := "figures"
  let mut opts : BuildOptions := {}
  let mut rest := args
  for _ in [0:args.length + 1] do
    match rest with
    | [] => break
    | "--check" :: r => opts := { opts with check := true }; rest := r
    | "--require-standing" :: r => opts := { opts with requireStanding := true }; rest := r
    | "--out" :: d :: r => out := d; rest := r
    | "--repo" :: u :: r =>
      if (safeLink? u).isNone then throw s!"the repository {u} is not an http or https link"
      opts := { opts with repo := some u }; rest := r
    | "--commit" :: c :: r =>
      if !isCommit c then throw s!"the commit {c} is not 4 to 64 lowercase hexadecimal digits"
      opts := { opts with commit := some c }; rest := r
    | a :: _ => throw s!"unexpected {a}"
  return (out, opts)

/-- The `main` of a project's driver: parses the command line and runs `build`; 2 with the usage
on a wrong command line. -/
def buildMain (entries : Array FigureEntry) (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error msg =>
    IO.eprintln s!"pilean-build: {escapeControl msg}"
    IO.eprintln buildUsage
    return 2
  | .ok (out, opts) =>
    try build entries out opts
    catch e =>
      IO.eprintln s!"pilean-build: {escapeControl (toString e)}"
      return 1

end PILean.Trust
