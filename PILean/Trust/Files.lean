/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Trust.Provenance
import PILean.Sort

/-!
# Reading and writing files of untrusted folders

The command-line tools read files they are given and files listed in a manifest, and write a
build into a folder that may already hold files. These are the only ways they touch files.

## Main definitions

* `readRegular`: a regular file, with a size cap checked before and during the read.
* `locateInside`: a path below a folder whose every component exists and is a real directory
  or, the last, a regular file (no symbolic link is followed).
* `writeInside`: writes a file below a folder under the same rule, creating directories.
* `listFiles`: the files below a folder, without following a symbolic link; a folder too deep or
  too large for its bounds is an error, never a partial listing.

## Implementation notes

* The type of a file is checked before it is opened, so a FIFO, a device or a socket is never
  opened (opening a FIFO for reading waits for a writer; a device can be read without end). The
  read stops with an error as soon as more than the cap has arrived, so a file that grows while
  it is read cannot make it larger.
* The checks are made with `lstat` (`System.FilePath.symlinkMetadata`) before each open; Lean's
  file API has no `fstat` on an open handle and no flag that refuses links when opening. A
  folder whose entries another process replaces between the check and the open is outside what
  these functions defend against; the folders they are made for belong to the user running the
  tool.
-/

namespace PILean.Trust

/-- The size of one read. -/
def readChunk : Nat := 65536

/-- The bytes of the regular file `p`, at most `cap` of them. Fails with a message if `p` does
not exist, is not a regular file (with `followLinks := false` a symbolic link also fails, and
with `true` the file it names must be regular), is larger than `cap` bytes, or grows past `cap`
while it is read. The file is opened only after its type and size have been checked. -/
def readRegular (p : System.FilePath) (cap : Nat) (followLinks : Bool := true) :
    IO (Except String ByteArray) := do
  let md ← try
      pure (some (← if followLinks then p.metadata else p.symlinkMetadata))
    catch _ => pure none
  let some md := md | return .error s!"cannot read {p}"
  if md.type != .file then return .error s!"{p} is not a regular file"
  let size := md.byteSize.toNat
  if size > cap then return .error s!"{p} is larger than {cap} bytes"
  let h ← try pure (some (← IO.FS.Handle.mk p .read)) catch _ => pure none
  let some h := h | return .error s!"cannot read {p}"
  let mut out := ByteArray.emptyWithCapacity size
  for _ in [0:cap / readChunk + 2] do
    let b ← h.read readChunk.toUSize
    if b.isEmpty then return .ok out
    if out.size + b.size > cap then return .error s!"{p} is larger than {cap} bytes"
    out := out ++ b
  return .error s!"{p} is larger than {cap} bytes"

/-- The components of a relative path written with `/`. -/
def relComponents (rel : String) : List String := (rel.splitOn "/").filter (!·.isEmpty)

/-- Where the relative path `rel` (components separated by `/`, none of them `.` or `..`) is
below the folder `root`: `.ok (some p)` if every component but the last is a directory and the
last a regular file, none of them a symbolic link; `.ok none` if a component does not exist;
`.error` with the first component that is something else. -/
def locateInside (root : System.FilePath) (rel : String) :
    IO (Except String (Option System.FilePath)) := do
  let parts := relComponents rel
  if parts.isEmpty || parts.any (fun c => c == "." || c == "..") then
    return .error s!"{rel} is not a relative path inside the folder"
  let mut cur := root
  let mut i := 0
  for c in parts do
    i := i + 1
    cur := cur / c
    let md ← try pure (some (← cur.symlinkMetadata)) catch _ => pure none
    let some md := md | return .ok none
    let want := if i == parts.length then IO.FS.FileType.file else .dir
    if md.type != want then
      return .error s!"{cur} is not a {if want == .dir then "directory" else "regular file"} \
        (symbolic links are not followed)"
  return .ok (some cur)

/-- Writes `bytes` to the relative path `rel` below `root`, creating the directories on the
way. Fails with a message, writing nothing, if a component that exists is not a directory (or,
the last, not a regular file), a symbolic link included. -/
def writeInside (root : System.FilePath) (rel : String) (bytes : ByteArray) :
    IO (Except String Unit) := do
  let parts := relComponents rel
  if parts.isEmpty || parts.any (fun c => c == "." || c == "..") then
    return .error s!"{rel} is not a relative path inside the folder"
  let mut cur := root
  let mut i := 0
  for c in parts do
    i := i + 1
    cur := cur / c
    let last := i == parts.length
    let md ← try pure (some (← cur.symlinkMetadata)) catch _ => pure none
    match md with
    | none => if !last then IO.FS.createDir cur
    | some md =>
      let want := if last then IO.FS.FileType.file else .dir
      if md.type != want then
        return .error s!"{cur} is not a {if last then "regular file" else "directory"} \
          (symbolic links are not followed)"
  IO.FS.writeBinFile cur bytes
  return .ok ()

/-- The most levels of directories below a folder that `listFiles` descends into. -/
def maxListDepth : Nat := 32

/-- The most directory entries (files and directories together) that `listFiles` reads. -/
def maxListEntries : Nat := 100000

/-- Every path below `dir` that is not a directory, relative to `dir` with `/`, sorted; a
symbolic link counts as a file and is not followed. The listing is complete or it is an error:
it fails with a message, and lists nothing, if a directory lies more than `maxDepth` levels
below `dir` or the folder has more than `maxEntries` entries in all (files and directories,
every level counted), so a caller never takes a partial listing for the whole folder. -/
def listFiles (dir : System.FilePath) (maxDepth : Nat := maxListDepth)
    (maxEntries : Nat := maxListEntries) : IO (Except String (Array String)) := do
  let mut out : Array String := #[]
  let mut todo : Array (System.FilePath × String × Nat) := #[(dir, "", 0)]
  let mut seen := 0
  -- every directory but `dir` was counted as an entry before it was queued
  for _ in [0:maxEntries + 2] do
    let some (d, rel, depth) := todo.back? | break
    todo := todo.pop
    for ent in (← d.readDir) do
      seen := seen + 1
      if seen > maxEntries then
        return .error s!"the folder has more than {maxEntries} entries, so it cannot be \
          listed completely"
      let r := if rel.isEmpty then ent.fileName else rel ++ "/" ++ ent.fileName
      if (← ent.path.symlinkMetadata).type == .dir then
        if depth + 1 > maxDepth then
          return .error s!"the folder has directories more than {maxDepth} levels deep, so \
            it cannot be listed completely"
        todo := todo.push (ent.path, r, depth + 1)
      else out := out.push r
  if !todo.isEmpty then return .error "the folder cannot be listed completely"
  return .ok (out.sortStable (· < ·))

end PILean.Trust
