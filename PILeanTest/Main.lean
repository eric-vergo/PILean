/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanTest.Color
import PILeanTest.Units
import PILeanTest.Examples
import PILeanTest.Raster
import PILeanTest.Png
import PILeanTest.Image
import PILeanTest.Anim
import PILeanTest.Plots
import PILeanTest.Lettering
import PILeanTest.Graphs

/-!
# The test driver

`lake test` runs the named checks (`PILeanTest.Color`, `PILeanTest.Units`, `PILeanTest.Png`,
`PILeanTest.Image`, `PILeanTest.Raster`, `PILeanTest.Anim`, `PILeanTest.Plots`,
`PILeanTest.Graphs`) and compares
every gallery figure's SVG and PNG, every gallery graph's SVG and PNG, and every gallery
animation's SVG, APNG, GIF and poster, with
its files in `examples/` (the goldens), byte for byte; it also renders each figure twice to check
that the output is deterministic. `lake exe pilean-test --update` rewrites
the goldens (as `lake exe pilean-gallery` does); `--compare-out DIR` writes the files of
`tools/compare-render.py`; `--bench` times a 2000 × 1200 plot; `--graph-bench` times the graph
layout and its output on module graphs of 100, 800 and 3000 nodes;
`--graph-compare-out DIR` writes the files of `tools/graph-compare.py`.
`lake exe pilean-test --png-out DIR` writes the PNG writer's files to `DIR` for
`tools/png-check.py`.
`lake exe pilean-test --anim-out DIR` writes sample GIF and APNG files to `DIR` for other software
to check.
-/

open PILeanTest

/-- Runs the checks; exit status 1 if any fails. -/
def main (args : List String) : IO UInt32 := do
  let mut failed := 0
  match args with
  | ["--png-out", dir] => Png.writeScratch dir; return 0
  | "--png-out" :: _ => IO.eprintln "usage: --png-out DIR"; return 1
  | ["--anim-out", dir] => AnimFiles.writeSamples dir; return 0
  | "--anim-out" :: _ => IO.eprintln "usage: --anim-out DIR"; return 1
  | ["--compare-out", dir] => Raster.writeCompare dir; return 0
  | ["--bench"] => Raster.bench; return 0
  | ["--graph-bench"] => Graphs.bench; return 0
  | ["--graph-compare-out", dir] => Graphs.writeCompare dir; return 0
  | "--graph-compare-out" :: _ => IO.eprintln "usage: --graph-compare-out DIR"; return 1
  | _ => pure ()
  let checks := Color.checks ++ Units.checks ++ Png.checks ++ (← Png.ioChecks) ++
    Image.checks ++ (← Image.perfChecks) ++ Raster.checks ++ (← Raster.ioChecks) ++
    Anim.checks ++ (← Anim.ioChecks) ++ Plots.checks ++ Lettering.checks ++
    Graphs.checks
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
    -- the PNG drawn from the same nodes
    let pngPath := path.withExtension "png"
    let png := (fig.toPng).getD ByteArray.empty
    if args == ["--update"] then
      IO.FS.writeBinFile pngPath png
      IO.println s!"wrote {pngPath}"
    else
      let golden ← if ← pngPath.pathExists then IO.FS.readBinFile pngPath else pure .empty
      if golden.data != png.data then
        IO.eprintln s!"FAIL {pngPath}: differs (`lake exe pilean-test --update` after checking \
          the change)"
        failed := failed + 1
      else IO.println s!"golden {pngPath}: same"
  for (stem, entry, st) in Examples.graphs do
    let svg := entry.svg st
    let outs : Array (String × ByteArray) :=
      #[(s!"{stem}.svg", svg.toUTF8), (s!"{stem}.png", entry.png st)]
    if svg != entry.svg st then
      IO.eprintln s!"FAIL {stem}: not deterministic"; failed := failed + 1
    for (file, bytes) in outs do
      let path : System.FilePath := "examples" / file
      if args == ["--update"] then
        IO.FS.writeBinFile path bytes
        IO.println s!"wrote {path}"
      else
        let golden ← if ← path.pathExists then IO.FS.readBinFile path else pure .empty
        if golden.data != bytes.data then
          IO.eprintln s!"FAIL {path}: differs (`lake exe pilean-test --update` after checking \
            the change)"
          failed := failed + 1
        else IO.println s!"golden {path}: same"
  for (name, a) in Examples.animations do
    let outs : Array (String × ByteArray) := #[(s!"{name}.svg", a.toSvg.toUTF8),
      (s!"{name}.png", a.toApng.toOption.getD .empty), (s!"{name}.gif", a.toGif.toOption.getD .empty),
      (s!"{name}-poster.png", a.posterPng.toOption.getD .empty)]
    for (file, bytes) in outs do
      let path : System.FilePath := "examples" / file
      if args == ["--update"] then
        IO.FS.writeBinFile path bytes
        IO.println s!"wrote {path}"
      else
        let golden ← if ← path.pathExists then IO.FS.readBinFile path else pure .empty
        if golden.data != bytes.data then
          IO.eprintln s!"FAIL {path}: differs (`lake exe pilean-test --update` after checking \
            the change)"
          failed := failed + 1
        else IO.println s!"golden {path}: same"
  return if failed == 0 then 0 else 1
