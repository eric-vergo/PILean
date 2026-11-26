/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Trust.Figure
import PILean.Trust.Motion
import PILean.Trust.Provenance
import PILean.Trust.Sha256

/-!
# The identity of the renderer

`rendererId` names the code that turns a figure into bytes: the SHA-256 of the source text of
every PILean module this module imports, directly or not (the plots, plane figures, graphs,
animations, the motions of plane figures and their outputs, the SVG writer, the rasteriser, the
lettering, the PNG, APNG, GIF and PDF writers and the source records), and of the Lean version
the library is compiled with. The texts are read when this module is compiled (`include_str`), so
the identity changes with any change to that code, comments included, and nobody has to remember
to change it: Lake recompiles this module whenever one of those files changes, because they are
its imports.

## Main definitions

* `rendererSources`: the modules and their source text.
* `rendererInput`, `rendererId`: the hashed bytes and the identity.

## Implementation notes

The list of modules is written out here, because finding the imported modules while compiling
needs the `Lean` package at run time; the tests check that the list is exactly the modules this
file imports, directly or not (parsing the `import` lines of the sources), and that each text is
the file's current content. The bytes hashed are the header `PILean renderer 1`, a line feed,
`Lean.versionString` and a line feed, then for each module in the order of its name: the name,
a line feed, the length of the text in bytes, a line feed and the text.
-/

namespace PILean.Trust

/-- The `PILean` modules this module imports, directly or not, sorted by name, each with its
source text as it was when the library was compiled. -/
def rendererSources : Array (String × String) :=
  #[("PILean.Anim.Animation", include_str "../Anim/Animation.lean"),
    ("PILean.Anim.Apng", include_str "../Anim/Apng.lean"),
    ("PILean.Anim.Frames", include_str "../Anim/Frames.lean"),
    ("PILean.Anim.Gif", include_str "../Anim/Gif.lean"),
    ("PILean.Anim.Lzw", include_str "../Anim/Lzw.lean"),
    ("PILean.Anim.Quantize", include_str "../Anim/Quantize.lean"),
    ("PILean.Anim.Smil", include_str "../Anim/Smil.lean"),
    ("PILean.Anim.Timeline", include_str "../Anim/Timeline.lean"),
    ("PILean.Canvas", include_str "../Canvas.lean"),
    ("PILean.CheckLevel", include_str "../CheckLevel.lean"),
    ("PILean.Color", include_str "../Color.lean"),
    ("PILean.Diagram.Basic", include_str "../Diagram/Basic.lean"),
    ("PILean.Exact", include_str "../Exact.lean"),
    ("PILean.Exact.Plane", include_str "../Exact/Plane.lean"),
    ("PILean.Explorer", include_str "../Explorer.lean"),
    ("PILean.Geometry", include_str "../Geometry.lean"),
    ("PILean.Graph.Bundle", include_str "../Graph/Bundle.lean"),
    ("PILean.Graph.Channel", include_str "../Graph/Channel.lean"),
    ("PILean.Graph.Compound", include_str "../Graph/Compound.lean"),
    ("PILean.Graph.Coordinates", include_str "../Graph/Coordinates.lean"),
    ("PILean.Graph.Draw", include_str "../Graph/Draw.lean"),
    ("PILean.Graph.Layered", include_str "../Graph/Layered.lean"),
    ("PILean.Graph.Layering", include_str "../Graph/Layering.lean"),
    ("PILean.Graph.Layout", include_str "../Graph/Layout.lean"),
    ("PILean.Graph.Model", include_str "../Graph/Model.lean"),
    ("PILean.Graph.Nested", include_str "../Graph/Nested.lean"),
    ("PILean.Graph.Ordering", include_str "../Graph/Ordering.lean"),
    ("PILean.Graph.Route", include_str "../Graph/Route.lean"),
    ("PILean.Graph.Simplex", include_str "../Graph/Simplex.lean"),
    ("PILean.Image.Basic", include_str "../Image/Basic.lean"),
    ("PILean.Path", include_str "../Path.lean"),
    ("PILean.Pdf.Figures", include_str "../Pdf/Figures.lean"),
    ("PILean.Pdf.Object", include_str "../Pdf/Object.lean"),
    ("PILean.Pdf.Read", include_str "../Pdf/Read.lean"),
    ("PILean.Pdf.Write", include_str "../Pdf/Write.lean"),
    ("PILean.Plane", include_str "../Plane.lean"),
    ("PILean.Plane.Basic", include_str "../Plane/Basic.lean"),
    ("PILean.Plane.Check", include_str "../Plane/Check.lean"),
    ("PILean.Plane.Draw", include_str "../Plane/Draw.lean"),
    ("PILean.Plane.Frame", include_str "../Plane/Frame.lean"),
    ("PILean.Plane.Graph", include_str "../Plane/Graph.lean"),
    ("PILean.Plane.Motion", include_str "../Plane/Motion.lean"),
    ("PILean.Plane.MotionOutput", include_str "../Plane/MotionOutput.lean"),
    ("PILean.Plane.MotionPanels", include_str "../Plane/MotionPanels.lean"),
    ("PILean.Plane.MotionPlan", include_str "../Plane/MotionPlan.lean"),
    ("PILean.Plane.Render", include_str "../Plane/Render.lean"),
    ("PILean.Plot.Check", include_str "../Plot/Check.lean"),
    ("PILean.Plot.Figure", include_str "../Plot/Figure.lean"),
    ("PILean.Plot.Sample", include_str "../Plot/Sample.lean"),
    ("PILean.Plot.Scale", include_str "../Plot/Scale.lean"),
    ("PILean.Plot.Ticks", include_str "../Plot/Ticks.lean"),
    ("PILean.Png", include_str "../Png.lean"),
    ("PILean.Png.Checksum", include_str "../Png/Checksum.lean"),
    ("PILean.Png.Deflate", include_str "../Png/Deflate.lean"),
    ("PILean.Png.Inflate", include_str "../Png/Inflate.lean"),
    ("PILean.Png.Proofs", include_str "../Png/Proofs.lean"),
    ("PILean.Png.Read", include_str "../Png/Read.lean"),
    ("PILean.Png.Tables", include_str "../Png/Tables.lean"),
    ("PILean.Png.Types", include_str "../Png/Types.lean"),
    ("PILean.Png.Write", include_str "../Png/Write.lean"),
    ("PILean.Raster.Canvas", include_str "../Raster/Canvas.lean"),
    ("PILean.Raster.Coverage", include_str "../Raster/Coverage.lean"),
    ("PILean.Raster.DomainColouring", include_str "../Raster/DomainColouring.lean"),
    ("PILean.Raster.Draw", include_str "../Raster/Draw.lean"),
    ("PILean.Raster.SrgbTables", include_str "../Raster/SrgbTables.lean"),
    ("PILean.Raster.Stroke", include_str "../Raster/Stroke.lean"),
    ("PILean.Raster.SvgRender", include_str "../Raster/SvgRender.lean"),
    ("PILean.Sort", include_str "../Sort.lean"),
    ("PILean.Style", include_str "../Style.lean"),
    ("PILean.Svg", include_str "../Svg.lean"),
    ("PILean.Text.Engine", include_str "../Text/Engine.lean"),
    ("PILean.Text.Lettering", include_str "../Text/Lettering.lean"),
    ("PILean.Text.LetteringArrows", include_str "../Text/LetteringArrows.lean"),
    ("PILean.Text.LetteringCompose", include_str "../Text/LetteringCompose.lean"),
    ("PILean.Text.LetteringGlyphs", include_str "../Text/LetteringGlyphs.lean"),
    ("PILean.Text.LetteringGreek", include_str "../Text/LetteringGreek.lean"),
    ("PILean.Text.LetteringLatin", include_str "../Text/LetteringLatin.lean"),
    ("PILean.Text.LetteringLower", include_str "../Text/LetteringLower.lean"),
    ("PILean.Text.LetteringMath", include_str "../Text/LetteringMath.lean"),
    ("PILean.Text.LetteringScripts", include_str "../Text/LetteringScripts.lean"),
    ("PILean.Text.LetteringSymbols", include_str "../Text/LetteringSymbols.lean"),
    ("PILean.Text.LetteringTypo", include_str "../Text/LetteringTypo.lean"),
    ("PILean.Trust.Figure", include_str "../Trust/Figure.lean"),
    ("PILean.Trust.Motion", include_str "../Trust/Motion.lean"),
    ("PILean.Trust.Provenance", include_str "../Trust/Provenance.lean"),
    ("PILean.Trust.Sha256", include_str "../Trust/Sha256.lean"),
    ("PILean.Version", include_str "../Version.lean")]

/-- The bytes `rendererId` is the SHA-256 of, for the given modules and texts and the Lean
version `toolchain` (see the module documentation). -/
def rendererInput (sources : Array (String × String))
    (toolchain : String := Lean.versionString) : ByteArray :=
  sources.foldl (init := ("PILean renderer 1\n" ++ toolchain ++ "\n").toUTF8) fun acc (m, t) =>
    acc ++ s!"{m}\n{t.utf8ByteSize}\n".toUTF8 ++ t.toUTF8

/-- The identity of the renderer: 64 lowercase hexadecimal digits (see the module
documentation). -/
def rendererId : String := Sha256.hex (Sha256.hash (rendererInput rendererSources))

/-- The renderer of an output drawn with the text engine whose identity is `engine`
(`TextEngine.id`): `rendererId` for the built-in lettering (an empty identity), else the SHA-256
of `rendererId`, a line feed and the engine's identity, so that the fingerprint covers the
engine's code and data as well as PILean's. -/
def rendererWith (engine : String) : String :=
  if engine.isEmpty then rendererId
  else Sha256.hex (Sha256.hash (rendererId ++ "\n" ++ engine).toUTF8)

end PILean.Trust
