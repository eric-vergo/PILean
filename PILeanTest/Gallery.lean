/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanTest.Examples
import PILeanTest.Diagrams
import PILeanTest.AlgebraDiagrams
import PILeanTest.NumberDiagrams

/-!
# The gallery writer

`lake exe pilean-gallery` writes every figure of `PILeanTest.Examples.gallery` to `examples/`,
as SVG and as PNG, every plane figure of `PILeanTest.Examples.planes` and of
`PILeanTest.Diagrams.gallery`, `PILeanTest.AlgebraDiagrams.gallery` and
`PILeanTest.NumberDiagrams.gallery` and every graph of
`PILeanTest.Examples.graphs` the same way, and every
animation of `PILeanTest.Examples.animations` as an animated SVG
(`NAME.svg`), an animated PNG (`NAME.png`), a GIF (`NAME.gif`) and its poster frame
(`NAME-poster.png`), and every raster picture of `PILeanTest.Examples.rasters` as PNG.
-/

open PILeanTest.Examples PILean.Plot

/-- Writes the gallery into `examples/`, run from the repository root. -/
def main : IO Unit := do
  IO.FS.createDirAll "examples"
  for (name, fig) in gallery do
    IO.FS.writeFile ("examples" / name) fig.toSvg
    IO.println s!"examples/{name}"
    if let some png := fig.toPng then
      let pngName := (System.FilePath.mk name).withExtension "png"
      IO.FS.writeBinFile ("examples" / pngName) png
      IO.println s!"examples/{pngName}"
  for (name, fig) in planes ++ PILeanTest.Diagrams.gallery ++ PILeanTest.AlgebraDiagrams.gallery ++
      PILeanTest.NumberDiagrams.gallery do
    IO.FS.writeFile ("examples" / name) fig.toSvg
    let pngName := (System.FilePath.mk name).withExtension "png"
    IO.FS.writeBinFile ("examples" / pngName) (fig.toPng.getD .empty)
    IO.println s!"examples/{name}, .png"
  for (stem, entry, st) in graphs do
    IO.FS.writeFile ("examples" / s!"{stem}.svg") (entry.svg st)
    IO.FS.writeBinFile ("examples" / s!"{stem}.png") (entry.png st)
    IO.println s!"examples/{stem}.svg, .png"
  for (name, a) in animations do
    IO.FS.writeFile ("examples" / s!"{name}.svg") a.toSvg
    if let .ok b := a.toApng then IO.FS.writeBinFile ("examples" / s!"{name}.png") b
    if let .ok b := a.toGif then IO.FS.writeBinFile ("examples" / s!"{name}.gif") b
    if let .ok b := a.posterPng then IO.FS.writeBinFile ("examples" / s!"{name}-poster.png") b
    IO.println s!"examples/{name}.svg, .png, .gif, -poster.png"
  for (name, im) in rasters do
    if let .ok b := im.writePng then IO.FS.writeBinFile ("examples" / name) b
    IO.println s!"examples/{name}"
