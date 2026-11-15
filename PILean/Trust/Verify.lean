/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Trust.Manifest

/-!
# `pilean-verify`

Checks a directory written by `pilean-build` against its `manifest.json`, which is untrusted
input: it is read with a size cap and the bounded reader of `PILean.Trust.Json`, and a path with
`..`, an absolute path, a backslash or any other unsafe character makes the whole manifest
invalid before any file is touched. Each listed file must be a regular file inside the
directory, with the size and the SHA-256 of the manifest, and the source record inside the file
(`Source.read?`) must agree with the manifest's fields and fingerprint.

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
  /-- The file is not a regular file, or its size or hash differs. -/
  | changed
  /-- The file has a source record but it differs from the manifest. -/
  | sourceDiffers
  /-- The file has no readable source record. -/
  | noSource
deriving BEq, Repr

/-- The word a verdict is printed as. -/
def Verdict.text : Verdict → String
  | .ok => "ok"
  | .missing => "missing"
  | .changed => "changed"
  | .sourceDiffers => "source differs"
  | .noSource => "no source"

/-- Whether a source record is the one the manifest entry describes. -/
def ManifestEntry.matches (m : ManifestEntry) (s : Source) : Bool :=
  s.module == m.module && s.decl == m.decl && s.file == m.file && s.line == m.line &&
    s.column == m.column && s.version == m.version && s.repo == m.repo && s.commit == m.commit &&
    s.fingerprint == some m.fingerprint

/-- The verdict on one listed file of the directory. -/
def verifyFile (dir : System.FilePath) (m : ManifestEntry) : IO Verdict := do
  let p := dir / m.path
  if !(← p.pathExists) then return .missing
  let md ← p.symlinkMetadata
  if md.type != .file || md.byteSize.toNat != m.bytes || m.bytes > maxOutputBytes then
    return .changed
  let bytes ← IO.FS.readBinFile p
  if Sha256.hex (Sha256.hash bytes) != m.sha256 then return .changed
  match Source.read? bytes with
  | .error _ => return .noSource
  | .ok s => return if m.matches s then .ok else .sourceDiffers

/-- Verifies the directory: the verdict on every file of its manifest, in the manifest's order;
fails with a message if the manifest cannot be read or is invalid. -/
def verifyDir (dir : System.FilePath) : IO (Except String (Array (String × Verdict))) := do
  let mpath := dir / manifestName
  let md ← try pure (some (← mpath.metadata)) catch _ => pure none
  let some md := md | return .error s!"cannot read {mpath}"
  if md.byteSize.toNat > maxJsonInput then return .error s!"{mpath} is too large"
  match Manifest.parse (← IO.FS.readBinFile mpath) with
  | .error e => return .error s!"{mpath}: {e}"
  | .ok entries =>
    let mut out := #[]
    for m in entries do
      out := out.push (m.path, ← verifyFile dir m)
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
      IO.eprintln s!"pilean-verify: {e}"
      return 1
    | .ok vs =>
      for (p, v) in vs do IO.println s!"{v.text}: {p}"
      return if vs.all (·.2 == .ok) then 0 else 1
  catch e =>
    IO.eprintln s!"pilean-verify: {e}"
    return 1

end PILean.Trust
