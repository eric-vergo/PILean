import GalleryLib.Mobius.Render

/-!
# Gallery entry point

Writes `Gallery/out/mobius.gif` (the swirl loop, then the finale) and
`Gallery/out/mobius.png` (the hero still: the `t = 1/2` frame, full art, no
caption bar) — implemented by the render work package
(`GalleryLib.Mobius.Render`).
-/

open PILean
open Gallery.Mobius

/-- Output directory, relative to the `gallery` executable's working
directory (`Gallery/`, when run via `lake exe gallery`). -/
def outDir : System.FilePath := System.FilePath.mk "out"

def main : IO Unit := do
  IO.FS.createDirAll outDir
  Gif.saveGif (outDir / "mobius.gif") allFrames
  heroImage.save (outDir / "mobius.png")
  IO.println
    s!"mobius: {allFrames.size} frames, byte-witness={byteWitness} (normalized_composition)"
