/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanMathlibTest.Files

/-!
# `pilean-mathlib-gallery`

Writes every file of `PILeanMathlibTest.files` into `examples/`, run from this folder.
-/

/-- Writes the gallery. -/
def main : IO UInt32 := do
  IO.FS.createDirAll "examples"
  for (name, bytes) in PILeanMathlibTest.files do
    match bytes with
    | .ok b => IO.FS.writeBinFile ("examples" / name) b; IO.println s!"examples/{name}"
    | .error m => IO.eprintln s!"{name}: {m}"; return 1
  IO.println s!"pixels per unit of the ordinate: {PILeanMathlibTest.pixelsPerUnit}"
  return 0
