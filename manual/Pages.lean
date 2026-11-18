/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanManual.PageFiles

/-!
# `pilean-manual-pages`

Writes the page files of the API reference (`PILeanManual.Pages`).

* `lake exe pilean-manual-pages`: writes the files and removes the page files of modules that no
  longer exist.
* `lake exe pilean-manual-pages --check`: writes nothing; exit status 1 when a file is missing,
  different or left over (`lake test` makes the same check).

Run from the manual's folder (Lake runs executables there).
-/

open PILeanManual.Pages in
/-- Writes or checks the API reference's page files (see the module docstring). -/
def main (args : List String) : IO UInt32 := do
  let check ← match args with
    | [] => pure false
    | ["--check"] => pure true
    | _ => IO.eprintln "usage: pilean-manual-pages [--check]"; return 2
  if check then
    let bad ← stale
    for l in bad do IO.println l
    if bad.isEmpty then IO.println "ok: the page files are current"
    return if bad.isEmpty then 0 else 1
  let files ← expected ".."
  for (path, text) in files do
    let cur ← if ← path.pathExists then some <$> IO.FS.readFile path else pure none
    if cur != some text then
      if let some d := path.parent then IO.FS.createDirAll d
      IO.FS.writeFile path text
  for p in ← presentPages do
    unless files.any (·.1 == p) do IO.FS.removeFile p
  IO.println s!"wrote {files.size} page files"
  return 0
