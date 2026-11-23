/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plane.Check

/-!
# Plane figures: output

A figure is written from the drawing of `Figure.autoPlaced` (its automatic labels placed; the
figure itself when it has none, `Figure.autoPlaced_of_noAuto`): as SVG (`Figure.toSvg`) and as an
image (`Figure.toImage`, `Figure.toPng`) from the same SVG nodes. `Figure.checkMessages` gives the
layout problems (`PILean.Plane.Check`) the figure's `checks` level asks for.

* **One colour space for both outputs.** The image of a plane figure is composited in sRGB
  (`Raster.Space.srgb`): a translucent tint over the page, or over another tint, gets the colour a
  browser gives the SVG's `fill-opacity`, so the PNG and the SVG agree (the contrast checks use
  the same mixing, `srgbOver`). Plots and graphs keep the rasteriser's linear light.
* **Text as shapes by default** (`Figure.textAsShapes`): the SVG draws labels with the style's text
  engine, the lettering the layout measured, so every viewer shows the same picture.
* **A narrow rendition** (`Figure.narrowWidth`, `Figure.narrow`): the same figure fitted to a
  second, narrower page, labels and markers at their full pixel size, for small screens.

## Main definitions

* `Figure.toSvg`, `Figure.toImage`, `Figure.toPng`, `Figure.svgNodes`, `Figure.narrow`,
  `Figure.checkMessages`.
-/

namespace PILean.Plane

namespace Figure

/-- The SVG nodes of the figure (its `auto` labels placed), text as SVG text in the style's family
(or as shapes when `outlines`, or when the style's text engine is not plain text). -/
def svgNodes (fig : Figure) (outlines : Option Bool := none) : Array Svg.Node :=
  fig.autoPlaced.draw.render
    (.forSvg fig.style.text fig.style.fontFamily (outlines.getD fig.textAsShapes))

/-- The figure as an SVG document (see `svgNodes`; text as shapes unless `textAsShapes` is off or
`outlines := false` is passed). -/
def toSvg (fig : Figure) (outlines : Option Bool := none) : String :=
  let f := fig.autoPlaced.frame
  Svg.document f.width.round f.height.round (fig.svgNodes outlines)

/-- The figure as an RGB image of its size in pixels, text drawn by the style's text engine,
composited in sRGB as browsers composite the SVG. -/
def toImage (fig : Figure) : Image :=
  let g := fig.autoPlaced
  let (w, h) := g.pixelSize
  (Raster.Svg.rasterize w h (g.draw.render (.shapes fig.style.text)) fig.style.background
    (space := .srgb)).toImage .rgb

/-- The figure as PNG bytes (deterministic); `none` for a figure of no pixels. -/
def toPng (fig : Figure) (md : Png.Metadata := {}) : Option ByteArray :=
  match fig.toImage.writePng md with
  | .ok b => some b
  | .error _ => none

/-- The narrow rendition: the figure at its `narrowWidth` (height fitted again), if it has one. -/
def narrow (fig : Figure) : Option Figure :=
  fig.narrowWidth.map fun w => { fig with width := w, height := none, narrowWidth := none }

/-- The messages of the figure's layout problems, unless its `checks` level is `ignore`. -/
def checkMessages (fig : Figure) (o : CheckOptions := {}) : Array String :=
  if fig.checks == .ignore then #[] else (fig.problems o).map (·.message)

end Figure

end PILean.Plane
