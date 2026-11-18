/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILeanVersoManual.Themes

/-!
# Pictures that are neither plots, graphs nor animations

PILean renders plots, graphs and animations to files out of the box (`PILean.Trust.ToOutputs`).
The guide also shows drawings made directly on the vector canvas and images made with the
rasteriser, and graph layouts other than the layered one; these types make them figures of the
manual:

* `Drawing`: a canvas drawing as a function of a `Style`, written as SVG in the light style and,
  for the site, in the dark style too (the suffix `-dark`).
* `LaidOut`: a graph layout as a function of a `Style` (for the layouts other than the layered
  one, which `PILean.Trust.GraphFigure` covers), written as SVG in the light and the dark style.
* `Picture`: an `Image`, written as PNG; it is shown the same in both themes.

The *specification* of an output (what the fingerprint covers, see `docs/TRUST.md`) is, as for
PILean's own types, the SVG document of a drawing; for a picture, which has no SVG, it is the PNG
file itself.
-/

namespace PILeanManual

open PILean PILean.Trust

/-- A drawing on the vector canvas, `width × height` pixels, drawn from a style. -/
structure Drawing where
  /-- The width in pixels. -/
  width : Nat
  /-- The height in pixels. -/
  height : Nat
  /-- The drawing in a style; it paints its own background. -/
  draw : Style → Canvas.Shape

/-- The SVG of a drawing in a style, text as SVG text in the style's font family. -/
def Drawing.svg (d : Drawing) (st : Style) : String :=
  (d.draw st).toSvg d.width.toFloat d.height.toFloat st.fontFamily

/-- The SVG output of a drawing in a style, with the file name suffix `name`. -/
def Drawing.output (d : Drawing) (st : Style) (name : String) : Output :=
  let svg := (d.svg st).toUTF8
  { name, format := .svg, bytes := fun _ => .ok svg, spec := svg }

/-- A drawing is written as SVG in the light style. -/
instance : ToOutputs Drawing where
  outputs d := #[d.output Style.light ""]

/-- On the site, a drawing is written in the light and the dark style. -/
instance : PILeanVerso.SiteOutputs Drawing where
  siteOutputs d := #[d.output Style.light "", d.output Style.dark "-dark"]

/-- A graph layout in a style, written as SVG with `Graph.Layout.toSvg`. -/
structure LaidOut where
  /-- The layout in a style (the style measures the labels). -/
  layout : Style → Graph.Layout

/-- The SVG output of a layout in a style, with the file name suffix `name`. -/
def LaidOut.output (l : LaidOut) (st : Style) (name : String) : Output :=
  let svg := ((l.layout st).toSvg st).toUTF8
  { name, format := .svg, bytes := fun _ => .ok svg, spec := svg }

/-- A layout is written as SVG in the light style. -/
instance : ToOutputs LaidOut where
  outputs l := #[l.output Style.light ""]

/-- On the site, a layout is written in the light and the dark style. -/
instance : PILeanVerso.SiteOutputs LaidOut where
  siteOutputs l := #[l.output Style.light "", l.output Style.dark "-dark"]

/-- An image made with the rasteriser. -/
structure Picture where
  /-- The image. -/
  image : Image

/-- A picture is written as PNG; its specification is the PNG file. -/
instance : ToOutputs Picture where
  outputs p :=
    let png := p.image.writePng
    #[{ name := "", format := .png, bytes := fun _ => png.mapError (·.toString),
        spec := png.toOption.getD .empty }]

end PILeanManual
