/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Trust.Manifest
import PILean.Trust.Files

/-!
# `pilean-verify`

Checks a directory written by `pilean-build` against its `manifest.json`, which is untrusted
input, as is everything else in the directory. The directory is resolved once (`realPath`) and
everything below it is reached without following a symbolic link (`locateInside`): the manifest
must be a regular file there, read with a size cap (`readRegular`) and the bounded reader of
`PILean.Trust.Json`, and a path with `..`, an absolute path, a backslash or any other unsafe
character makes the whole manifest invalid before any file is touched. Each listed file must be
a regular file inside the directory, every directory on its way a real directory, with the size
and the SHA-256 of the manifest, its bytes of the manifest's format (`detectedFormat?`), and the
source record inside the file (`Source.read?`) must agree with the manifest's fields and
fingerprint. A file below the directory that the manifest does not list is reported as extra.
The directory must be listed completely (`listFiles` has a bound on depth and on entries): if it
cannot be, the answer is an error, never `ok`. Every string from the directory is printed
through `escapeControl`.

An answer of `ok` for every file says that the files below the directory are exactly those the
manifest lists (directories that hold no file are not compared) and that each agrees with its
entry in the fields above.
It does not say where they came from: someone who can write both the files and the manifest can
make a directory that passes. The source record in a file is a statement by whoever wrote the
file, and nothing here is signed.

The check does not render anything; `pilean-build --check` is the check that a file is what the
build produces now.
-/

namespace PILean.Trust

/-- The verdict on one file. -/
inductive Verdict where
  /-- The file and its source record agree with the manifest. -/
  | ok
  /-- No file has the path the manifest gives (spelled exactly as there). -/
  | missing
  /-- The file's size or hash differs. -/
  | changed
  /-- The file, or a directory on its way, is a symbolic link or not a regular file. -/
  | notRegular
  /-- The file's bytes are not of the format the manifest gives (`detectedFormat?`). -/
  | formatDiffers
  /-- The file has a source record but it differs from the manifest. -/
  | sourceDiffers
  /-- The file has no readable source record. -/
  | noSource
  /-- A file below the directory that the manifest does not list. -/
  | extra
deriving BEq, Repr

/-- The word a verdict is printed as. -/
def Verdict.text : Verdict → String
  | .ok => "ok"
  | .missing => "missing"
  | .changed => "changed"
  | .notRegular => "not a regular file"
  | .formatDiffers => "format differs"
  | .sourceDiffers => "source differs"
  | .noSource => "no source"
  | .extra => "extra"

/-- Whether a source record is the one the manifest entry describes. -/
def ManifestEntry.matches (m : ManifestEntry) (s : Source) : Bool :=
  s.module == m.module && s.decl == m.decl && s.file == m.file && s.line == m.line &&
    s.column == m.column && s.version == m.version && s.repo == m.repo && s.commit == m.commit &&
    s.fingerprint == some m.fingerprint && s.standing == m.standing && s.theorems == m.theorems

/-- What a line of `pilean-verify` adds after the path of a file that agrees with its manifest:
the standing the file records, as recorded (` [recorded: linked to T₁ T₂]`,
` [recorded: illustration]`), or nothing for a file that records none. It repeats what the file
and the manifest say; `pilean-verify` checks no theorem. -/
def recordedStanding (m : ManifestEntry) : String :=
  match m.standing, m.theorems with
  | some "linked", some ts => s!" [recorded: linked to {ts}]"
  | some w, _ => s!" [recorded: {w}]"
  | none, _ => ""

/-- The verdict on one listed file of the directory `root` (already resolved). -/
def verifyFile (root : System.FilePath) (m : ManifestEntry) : IO Verdict := do
  match ← locateInside root m.path with
  | .error _ => return .notRegular
  | .ok none => return .missing
  | .ok (some p) =>
    if m.bytes > maxOutputBytes then return .changed
    match ← readRegular p m.bytes (followLinks := false) with
    | .error _ =>
      let md ← p.symlinkMetadata
      return if md.type == .file then .changed else .notRegular
    | .ok bytes =>
      if bytes.size != m.bytes || Sha256.hex (Sha256.hash bytes) != m.sha256 then
        return .changed
      if detectedFormat? bytes != some m.format then return .formatDiffers
      match Source.read? bytes with
      | .error _ => return .noSource
      | .ok s => return if m.matches s then .ok else .sourceDiffers

/-- Verifies the directory: the verdict on every file of its manifest, in the manifest's order
(`missing` also for a file found only under another spelling of its name, as a file system that
ignores case finds it), then `extra` for every other file below the directory (other than the
manifest itself; a symbolic link counts as a file and is not followed), sorted.
Fails with a message if the directory cannot be resolved, if the manifest cannot be read (it
must be a regular file, not a link, of at most `maxJsonInput` bytes) or is invalid, or if the
directory cannot be listed completely (`listFiles`): a folder whose every file was not seen is
never reported as agreeing with its manifest. Each verdict comes with the manifest entry of its
file (none for an extra file). -/
def verifyDirEntries (dir : System.FilePath) :
    IO (Except String (Array (String × Verdict × Option ManifestEntry))) := do
  let root ← try pure (some (← IO.FS.realPath dir)) catch _ => pure none
  let some root := root | return .error s!"cannot read the directory {dir}"
  let mpath := root / manifestName
  match ← readRegular mpath maxJsonInput (followLinks := false) with
  | .error e => return .error e
  | .ok text =>
  match Manifest.parse text with
  | .error e => return .error s!"{mpath}: {e}"
  | .ok entries =>
    let mut out := #[]
    for m in entries do
      out := out.push (m.path, ← verifyFile root m, some m)
    match ← listFiles root with
    | .error e => return .error s!"cannot verify {dir}: {e}"
    | .ok present =>
    -- a file is checked under the name the manifest gives it: on a file system that ignores
    -- case, `locateInside` also finds it under another spelling, which the listing shows
    let onDisk : Std.HashSet String := present.foldl (·.insert ·) {}
    out := out.map fun (p, v, m) =>
      if v == .ok && !onDisk.contains p then (p, .missing, m) else (p, v, m)
    let listed : Std.HashSet String :=
      entries.foldl (fun s m => s.insert m.path) (({} : Std.HashSet String).insert manifestName)
    for r in present do
      if !listed.contains r then out := out.push (r, .extra, none)
    return .ok out

/-- The verdicts of `verifyDirEntries`, without the manifest entries. -/
def verifyDir (dir : System.FilePath) : IO (Except String (Array (String × Verdict))) := do
  return (← verifyDirEntries dir).map (·.map fun (p, v, _) => (p, v))

/-- The `main` of `pilean-verify DIR`: one line `verdict: path` for each file, an `ok` line followed
by the standing the file records (`recordedStanding`); 0 if every file is
`ok`, 1 if not, or if the manifest is invalid or the directory cannot be listed completely (a
message goes to standard error and no verdict is printed), 2 on a wrong command line. -/
def verifyMain (args : List String) : IO UInt32 := do
  let [dir] := args | do
    IO.eprintln "usage: pilean-verify DIR"
    return 2
  try
    match ← verifyDirEntries dir with
    | .error e =>
      IO.eprintln s!"pilean-verify: {escapeControl e}"
      return 1
    | .ok vs =>
      for (p, v, m) in vs do
        let tail := match v, m with
          | .ok, some m => escapeControl (recordedStanding m)
          | _, _ => ""
        IO.println s!"{v.text}: {escapeControl p}{tail}"
      return if vs.all (·.2.1 == .ok) then 0 else 1
  catch e =>
    IO.eprintln s!"pilean-verify: {escapeControl (toString e)}"
    return 1

end PILean.Trust
