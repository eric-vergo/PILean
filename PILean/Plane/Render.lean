/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plane.Check

/-!
# Plane figures: output

A figure is written from the drawing of `Figure.autoPlaced` (its `auto` labels given a side; the
figure itself when it has none, `Figure.autoPlaced_of_noAuto`): as SVG (`Figure.toSvg`) and as an
image (`Figure.toImage`, `Figure.toPng`) from the same SVG nodes. `Figure.checkMessages` gives the
layout problems (`PILean.Plane.Check`) the figure's `checks` level asks for.

## Main definitions

* `Figure.toSvg`, `Figure.toImage`, `Figure.toPng`, `Figure.svgNodes`, `Figure.checkMessages`.
-/

namespace PILean.Plane

namespace Figure

/-- The SVG nodes of the figure (its `auto` labels placed), text as SVG text in the style's family
(or as shapes when `outlines`, or when the style's text engine is not plain text). -/
def svgNodes (fig : Figure) (outlines : Bool := false) : Array Svg.Node :=
  fig.autoPlaced.draw.render (.forSvg fig.style.text fig.style.fontFamily outlines)

/-- The figure as an SVG document (see `svgNodes`). -/
def toSvg (fig : Figure) (outlines : Bool := false) : String :=
  let f := fig.autoPlaced.frame
  Svg.document f.width.round f.height.round (fig.svgNodes outlines)

/-- The figure as an RGB image of its size in pixels, text drawn by the style's text engine. -/
def toImage (fig : Figure) : Image :=
  let g := fig.autoPlaced
  let (w, h) := g.pixelSize
  (Raster.Svg.rasterize w h (g.draw.render (.shapes fig.style.text)) fig.style.background
    ).toImage .rgb

/-- The figure as PNG bytes (deterministic); `none` for a figure of no pixels. -/
def toPng (fig : Figure) (md : Png.Metadata := {}) : Option ByteArray :=
  match fig.toImage.writePng md with
  | .ok b => some b
  | .error _ => none

/-- The messages of the figure's layout problems, unless its `checks` level is `ignore`. -/
def checkMessages (fig : Figure) (o : CheckOptions := {}) : Array String :=
  if fig.checks == .ignore then #[] else (fig.problems o).map (·.message)

end Figure

end PILean.Plane
