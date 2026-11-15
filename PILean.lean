/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Color
import PILean.Geometry
import PILean.Path
import PILean.Svg
import PILean.Png
import PILean.Anim
import PILean.Image.Basic
import PILean.Image.Ops
import PILean.Image.Proofs
import PILean.Plot.Ticks
import PILean.Plot.Figure
import PILean.Raster.Coverage
import PILean.Raster.Canvas
import PILean.Raster.Stroke
import PILean.Raster.Draw
import PILean.Raster.SvgRender
import PILean.Raster.Proofs
import PILean.Plot.Raster

/-!
# PILean

A pure-Lean image library: colours, geometry, paths, images, a rasteriser with paints and
compositing, PNG and SVG output, and plots. See `README.md` and `docs/DESIGN.md`.
-/
