/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plot.Figure
import PILean.Raster.SvgRender

/-!
# Figures as images

A figure drawn by the rasteriser from the same SVG nodes its SVG is written from
(`Figure.render`), so that the PNG and the SVG show the same picture. Text is not drawn yet
(PILean has no text layer); the PNG has the figure's lines, marks, grid, axes, ticks and legend
plate without their labels.

## Main definitions

* `Figure.toImage`: the figure as an RGB image of its size in pixels.
* `Figure.toPng`: the figure as PNG bytes.
-/

namespace PILean.Plot

open PILean.Raster

/-- The figure as an RGB image, `width × height` pixels (rounded). -/
def Figure.toImage (fig : Figure) : Image :=
  let w := fig.width.round.toUInt64.toNat
  let h := fig.height.round.toUInt64.toNat
  (Svg.rasterize w h fig.render ⟨255, 255, 255, 255⟩).toImage .rgb

/-- The figure as PNG bytes (deterministic); `none` for a figure of no pixels. -/
def Figure.toPng (fig : Figure) (md : Png.Metadata := {}) : Option ByteArray :=
  match fig.toImage.writePng md with
  | .ok b => some b
  | .error _ => none

end PILean.Plot
