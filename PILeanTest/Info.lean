/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean

/-!
# `pilean-info`

`lake exe pilean-info FILE` prints the source information of an SVG, PNG, APNG or GIF file written
with `PILean.Trust.withSource`, one `key: value` line a field. Values are shown with control
characters escaped. Exit status 0 on success, 1 if the file cannot be read or has no source
information (a message goes to standard error), 2 on a wrong command line.
-/

open PILean.Trust

/-- Prints the fields of the source of the file named by the one argument. -/
def main (args : List String) : IO UInt32 := do
  let [file] := args | do
    IO.eprintln "usage: pilean-info FILE"
    return 2
  let size ← try pure (some (← System.FilePath.metadata file).byteSize.toNat) catch _ => pure none
  let some n := size | do
    IO.eprintln s!"pilean-info: cannot read {file}"
    return 1
  if n > maxInput then
    IO.eprintln s!"pilean-info: {file} is larger than {maxInput} bytes"
    return 1
  let bytes ← try pure (some (← IO.FS.readBinFile file)) catch _ => pure none
  let some bytes := bytes | do
    IO.eprintln s!"pilean-info: cannot read {file}"
    return 1
  match infoLines bytes with
  | .ok lines =>
    for l in lines do IO.println l
    return 0
  | .error e =>
    IO.eprintln s!"pilean-info: {file}: {e}"
    return 1
