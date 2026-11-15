/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanTest.Color
import PILeanTest.Units
import PILeanTest.Examples
import PILeanTest.Png

/-!
# The test driver

`lake test` runs the named checks (`PILeanTest.Color`, `PILeanTest.Units`, `PILeanTest.Png`) and
compares every gallery figure's SVG with its file in `examples/` (the goldens), byte for byte; it
also renders each figure twice to check that the output is deterministic.
`lake exe pilean-test --update` rewrites the goldens (as `lake exe pilean-gallery` does).
`lake exe pilean-test --png-out DIR` writes the PNG writer's files to `DIR` for
`tools/png-check.py`.
-/

open PILeanTest

/-- Runs the checks; exit status 1 if any fails. -/
def main (args : List String) : IO UInt32 := do
  let mut failed := 0
  match args with
  | ["--png-out", dir] => Png.writeScratch dir; return 0
  | "--png-out" :: _ => IO.eprintln "usage: --png-out DIR"; return 1
  | _ => pure ()
  let checks := Color.checks ++ Units.checks ++ Png.checks ++ (← Png.ioChecks)
  for (name, ok) in checks do
    if !ok then IO.eprintln s!"FAIL {name}"; failed := failed + 1
  IO.println s!"checks: {checks.size - failed} of {checks.size} hold"
  for (name, fig) in Examples.gallery do
    let svg := fig.toSvg
    let path : System.FilePath := "examples" / name
    if args == ["--update"] then
      IO.FS.writeFile path svg
      IO.println s!"wrote {path}"
    else
      if svg != fig.toSvg then IO.eprintln s!"FAIL {name}: not deterministic"; failed := failed + 1
      let golden ← if ← path.pathExists then IO.FS.readFile path else pure ""
      if golden != svg then
        IO.eprintln s!"FAIL {name}: differs from {path} (`lake exe pilean-test --update` after \
          checking the change)"
        failed := failed + 1
      else IO.println s!"golden {path}: same"
  return if failed == 0 then 0 else 1
