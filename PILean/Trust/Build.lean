/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Trust.Manifest

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
* `buildMain`: the command line `[--out DIR] [--repo URL] [--commit SHA] [--check]`
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

/-- A file of a build: its manifest entry and its bytes. -/
structure BuiltFile where
  /-- The manifest entry. -/
  entry : ManifestEntry
  /-- The bytes of the file, with the source information. -/
  bytes : ByteArray
deriving Inhabited

/-- Renders one output of an entry: the bytes with the source record of the entry (and the
fingerprint of the output's specification) inserted, and the manifest entry. -/
def renderOutput (e : FigureEntry) (o : Output) (opts : BuildOptions) :
    Except String BuiltFile := do
  let path ← outputPath e.toSourceData o
  let raw ← match o.bytes () with
    | .ok b => pure b
    | .error err => throw s!"{path}: {err}"
  if raw.size > maxOutputBytes then throw s!"{path}: the file is larger than {maxOutputBytes} bytes"
  let src := e.source o opts.repo opts.commit
  let bytes ← (withSource raw src).mapError (s!"{path}: " ++ ·)
  let m : ManifestEntry := {
    path, format := o.format.name, bytes := bytes.size, sha256 := Sha256.hex (Sha256.hash bytes),
    fingerprint := (src.fingerprint.getD ""), module := e.module, decl := e.decl, file := e.file,
    line := e.line, column := e.column, version := src.version, repo := opts.repo,
    commit := opts.commit }
  return { entry := m, bytes }

/-- Every file of a build, sorted by path. Fails with all the messages (one per line) if there
are more than `maxEntries` entries, a figure cannot be rendered, a file is too large, or two
files have the same path. -/
def renderAll (entries : Array FigureEntry) (opts : BuildOptions := {}) :
    IO (Except String (Array BuiltFile)) := do
  if entries.size > maxEntries then
    return .error s!"more than {maxEntries} figures"
  let mut files : Array BuiltFile := #[]
  let mut errors : Array String := #[]
  for e in entries do
    for o in e.outputs () do
      match renderOutput e o opts with
      | .ok f => files := files.push f
      | .error err => errors := errors.push err
  files := files.qsort fun a b => a.entry.path < b.entry.path
  for i in [1:files.size] do
    if files[i - 1]!.entry.path == files[i]!.entry.path then
      errors := errors.push s!"two outputs have the path {files[i]!.entry.path}"
  if errors.isEmpty then return .ok files else return .error ("\n".intercalate errors.toList)

/-- Every path below `dir` that is not a directory, relative to `dir` with `/`; a symbolic link
counts as a file and is not followed. At most 100000 files and 32 levels are visited. -/
def listFiles (dir : System.FilePath) : IO (Array String) := do
  let mut out : Array String := #[]
  let mut todo : Array (System.FilePath × String × Nat) := #[(dir, "", 0)]
  for _ in [0:100000] do
    let some (d, rel, depth) := todo.back? | break
    todo := todo.pop
    if depth > 32 then continue
    for ent in (← d.readDir) do
      let r := if rel.isEmpty then ent.fileName else rel ++ "/" ++ ent.fileName
      if (← ent.path.symlinkMetadata).type == .dir then todo := todo.push (ent.path, r, depth + 1)
      else out := out.push r
  return out.qsort (· < ·)

/-- Whether the file `p` holds exactly `bytes`: its size is read first, so a large file of the
wrong size is never read. -/
def sameFile (p : System.FilePath) (bytes : ByteArray) : IO Bool := do
  let md ← p.symlinkMetadata
  if md.type != .file || md.byteSize.toNat != bytes.size then return false
  return (← IO.FS.readBinFile p) == bytes

/-- The lines `check` prints for a directory: `missing: PATH` for a file of the build that is not
there, `stale: PATH` for one whose bytes differ (the manifest included), `extra: PATH` for a file
below the directory that the build does not make (other than `manifest.json`); the files of the build come in the order of their paths, the
manifest last, then the extra files sorted; empty if the directory holds exactly what the build makes. -/
def checkLines (files : Array BuiltFile) (manifest : ByteArray) (outDir : System.FilePath) :
    IO (Array String) := do
  let mut lines : Array String := #[]
  let expected : Array (String × ByteArray) :=
    files.map (fun f => (f.entry.path, f.bytes)) ++ #[(manifestName, manifest)]
  for (path, bytes) in expected do
    let p := outDir / path
    if !(← p.pathExists) then lines := lines.push s!"missing: {path}"
    else if !(← sameFile p bytes) then lines := lines.push s!"stale: {path}"
  if ← outDir.pathExists then
    let known : Std.HashSet String := expected.foldl (fun s (p, _) => s.insert p) {}
    for r in ← listFiles outDir do
      if !known.contains r then lines := lines.push s!"extra: {r}"
  return lines

/-- Builds into `outDir` (`opts.check = false`): writes every file and `manifest.json`, one line
`path` for each. With `opts.check`: prints the lines of `checkLines`, or `ok` if there are none.
The result is 1 if a figure cannot be rendered (a message goes to standard error) or if `check`
printed a line, and 0 otherwise. -/
def build (entries : Array FigureEntry) (outDir : System.FilePath) (opts : BuildOptions := {}) :
    IO UInt32 := do
  match ← renderAll entries opts with
  | .error msg =>
    IO.eprintln s!"pilean-build: {msg}"
    return 1
  | .ok files =>
    let manifest := (Manifest.render (files.map (·.entry))).toUTF8
    if opts.check then
      let lines ← checkLines files manifest outDir
      for l in lines do IO.println l
      if lines.isEmpty then IO.println s!"ok: {files.size} files match"
      return if lines.isEmpty then 0 else 1
    else
      for f in files do
        let p := outDir / f.entry.path
        if let some parent := p.parent then IO.FS.createDirAll parent
        IO.FS.writeBinFile p f.bytes
        IO.println f.entry.path
      IO.FS.createDirAll outDir
      IO.FS.writeBinFile (outDir / manifestName) manifest
      IO.println manifestName
      return 0

/-- The usage text of `pilean-build`. -/
def buildUsage : String :=
  "usage: pilean-build [--out DIR] [--repo URL] [--commit SHA] [--check]"

/-- Whether the string is 4 to 64 lowercase hexadecimal digits, as a commit is. -/
def isCommit (s : String) : Bool :=
  4 ≤ s.length && s.length ≤ 64 && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- The options of a command line, or a message: `--out DIR` (default `figures`), `--repo URL`
(`http` or `https`, see `safeLink?`), `--commit SHA` (`isCommit`), `--check`. -/
def parseArgs (args : List String) :
    Except String (System.FilePath × BuildOptions) := do
  let mut out : System.FilePath := "figures"
  let mut opts : BuildOptions := {}
  let mut rest := args
  for _ in [0:args.length + 1] do
    match rest with
    | [] => break
    | "--check" :: r => opts := { opts with check := true }; rest := r
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
    IO.eprintln s!"pilean-build: {msg}"
    IO.eprintln buildUsage
    return 2
  | .ok (out, opts) =>
    try build entries out opts
    catch e =>
      IO.eprintln s!"pilean-build: {e}"
      return 1

end PILean.Trust
