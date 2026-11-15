/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanLeAnTeX

/-!
# `pilean-leantex-gallery`

Writes every file of `PILeanLeAnTeX.Examples.files` into `examples/`, run from this folder.
-/

/-- Writes the gallery. -/
def main : IO UInt32 := do
  let .ok e ← PILeanLeAnTeX.load
    | IO.eprintln "the New Computer Modern fonts are missing (run `lake build` first)"; return 1
  IO.FS.createDirAll "examples"
  for (name, bytes) in PILeanLeAnTeX.Examples.files e do
    match bytes with
    | .ok b => IO.FS.writeBinFile ("examples" / name) b; IO.println s!"examples/{name}"
    | .error m => IO.eprintln s!"{name}: {m}"; return 1
  return 0
