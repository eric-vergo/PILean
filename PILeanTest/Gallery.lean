/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanTest.Examples
import PILean.Plot.Raster

/-!
# The gallery writer

`lake exe pilean-gallery` writes every figure of `PILeanTest.Examples.gallery` to `examples/`,
as SVG and as PNG.
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
