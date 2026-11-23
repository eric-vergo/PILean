/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean

/-!
# `pilean-info`

`lake exe pilean-info FILE` prints the source information of an SVG, PNG, APNG, GIF or PDF file written
with `PILean.Trust.withSource`, one `key: value` line a field. Values are shown with control
characters escaped (`escapeControl`; the messages too). The file must be a regular file (a
symbolic link to one is followed) of at most `maxInput` bytes, checked before it is opened, so a
FIFO or a device is refused rather than read. Exit status 0 on success, 1 if the file cannot be
read or has no source information (a message goes to standard error), 2 on a wrong command line.
-/

open PILean.Trust

/-- Prints the fields of the source of the file named by the one argument. -/
def main (args : List String) : IO UInt32 := do
  let [file] := args | do
    IO.eprintln "usage: pilean-info FILE"
    return 2
  match ← readRegular file maxInput with
  | .error e =>
    IO.eprintln s!"pilean-info: {escapeControl e}"
    return 1
  | .ok bytes =>
  match infoLines bytes with
  | .ok lines =>
    for l in lines do IO.println l
    return 0
  | .error e =>
    IO.eprintln s!"pilean-info: {escapeControl file}: {escapeControl e}"
    return 1
