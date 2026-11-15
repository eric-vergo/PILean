/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Trust.Figure
import PILean.Trust.Provenance
import PILean.Trust.Sha256

/-!
# The identity of the renderer

`rendererId` names the code that turns a figure into bytes: the SHA-256 of the source text of
every PILean module this module imports, directly or not (the plots, graphs, animations, the SVG
writer, the rasteriser, the lettering, the PNG, APNG and GIF writers and the source records),
and of the Lean version the library is compiled with. The texts are read when this module is
compiled (`include_str`), so the identity changes with any change to that code, comments
included, and nobody has to remember to change it: Lake recompiles this module whenever one of
those files changes, because they are its imports.

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
    ("PILean.Canvas", include_str "../Canvas.lean"),
    ("PILean.Color", include_str "../Color.lean"),
    ("PILean.Exact", include_str "../Exact.lean"),
    ("PILean.Geometry", include_str "../Geometry.lean"),
    ("PILean.Graph.Coordinates", include_str "../Graph/Coordinates.lean"),
    ("PILean.Graph.Draw", include_str "../Graph/Draw.lean"),
    ("PILean.Graph.Layered", include_str "../Graph/Layered.lean"),
    ("PILean.Graph.Layering", include_str "../Graph/Layering.lean"),
    ("PILean.Graph.Layout", include_str "../Graph/Layout.lean"),
    ("PILean.Graph.Model", include_str "../Graph/Model.lean"),
    ("PILean.Graph.Ordering", include_str "../Graph/Ordering.lean"),
    ("PILean.Graph.Simplex", include_str "../Graph/Simplex.lean"),
    ("PILean.Image.Basic", include_str "../Image/Basic.lean"),
    ("PILean.Path", include_str "../Path.lean"),
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
    ("PILean.Raster.Draw", include_str "../Raster/Draw.lean"),
    ("PILean.Raster.SrgbTables", include_str "../Raster/SrgbTables.lean"),
    ("PILean.Raster.Stroke", include_str "../Raster/Stroke.lean"),
    ("PILean.Raster.SvgRender", include_str "../Raster/SvgRender.lean"),
    ("PILean.Style", include_str "../Style.lean"),
    ("PILean.Svg", include_str "../Svg.lean"),
    ("PILean.Text.Engine", include_str "../Text/Engine.lean"),
    ("PILean.Text.Lettering", include_str "../Text/Lettering.lean"),
    ("PILean.Text.LetteringGlyphs", include_str "../Text/LetteringGlyphs.lean"),
    ("PILean.Text.LetteringLower", include_str "../Text/LetteringLower.lean"),
    ("PILean.Text.LetteringSymbols", include_str "../Text/LetteringSymbols.lean"),
    ("PILean.Trust.Figure", include_str "../Trust/Figure.lean"),
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

end PILean.Trust
