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
and the SHA-256 of the manifest, and the source record inside the file (`Source.read?`) must
agree with the manifest's fields and fingerprint. A file below the directory that the manifest
does not list is reported as extra. Every string from the directory is printed through
`escapeControl`.

An answer of `ok` for every file says that the directory and its manifest agree with each other.
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
  /-- The file does not exist. -/
  | missing
  /-- The file's size or hash differs. -/
  | changed
  /-- The file, or a directory on its way, is a symbolic link or not a regular file. -/
  | notRegular
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
  | .sourceDiffers => "source differs"
  | .noSource => "no source"
  | .extra => "extra"

/-- Whether a source record is the one the manifest entry describes. -/
def ManifestEntry.matches (m : ManifestEntry) (s : Source) : Bool :=
  s.module == m.module && s.decl == m.decl && s.file == m.file && s.line == m.line &&
    s.column == m.column && s.version == m.version && s.repo == m.repo && s.commit == m.commit &&
    s.fingerprint == some m.fingerprint

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
      match Source.read? bytes with
      | .error _ => return .noSource
      | .ok s => return if m.matches s then .ok else .sourceDiffers

/-- Verifies the directory: the verdict on every file of its manifest, in the manifest's order,
then `extra` for every other file below the directory (other than the manifest itself; a
symbolic link counts as a file and is not followed), sorted;
fails with a message if the directory cannot be resolved or the manifest cannot be read (it
must be a regular file, not a link, of at most `maxJsonInput` bytes) or is invalid. -/
def verifyDir (dir : System.FilePath) : IO (Except String (Array (String × Verdict))) := do
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
      out := out.push (m.path, ← verifyFile root m)
    let listed : Std.HashSet String :=
      entries.foldl (fun s m => s.insert m.path) (({} : Std.HashSet String).insert manifestName)
    for r in ← listFiles root do
      if !listed.contains r then out := out.push (r, .extra)
    return .ok out

/-- The `main` of `pilean-verify DIR`: one line `verdict: path` for each file; 0 if every file is
`ok`, 1 if not or if the manifest is invalid (a message goes to standard error), 2 on a wrong
command line. -/
def verifyMain (args : List String) : IO UInt32 := do
  let [dir] := args | do
    IO.eprintln "usage: pilean-verify DIR"
    return 2
  try
    match ← verifyDir dir with
    | .error e =>
      IO.eprintln s!"pilean-verify: {escapeControl e}"
      return 1
    | .ok vs =>
      for (p, v) in vs do IO.println s!"{v.text}: {escapeControl p}"
      return if vs.all (·.2 == .ok) then 0 else 1
  catch e =>
    IO.eprintln s!"pilean-verify: {escapeControl (toString e)}"
    return 1

end PILean.Trust
