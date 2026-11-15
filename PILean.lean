/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Color
import PILean.Geometry
import PILean.Path
import PILean.Sort
import PILean.Svg
import PILean.Svg.Inert
import PILean.Png
import PILean.Anim
import PILean.Text.Engine
import PILean.Style
import PILean.Canvas
import PILean.Image.Basic
import PILean.Image.Ops
import PILean.Image.Proofs
import PILean.Exact
import PILean.Plot.Ticks
import PILean.Plot.Scale
import PILean.Plot.Sample
import PILean.Plot.Figure
import PILean.Plot.Proofs
import PILean.Plot.Exact
import PILean.Graph.Model
import PILean.Graph.Layout
import PILean.Graph.Layering
import PILean.Graph.Ordering
import PILean.Graph.Coordinates
import PILean.Graph.Layered
import PILean.Graph.Simple
import PILean.Graph.Draw
import PILean.Graph.Proofs
import PILean.Graph.Spec
import PILean.Raster.Coverage
import PILean.Raster.Canvas
import PILean.Raster.Stroke
import PILean.Raster.Draw
import PILean.Raster.SvgRender
import PILean.Raster.Proofs
import PILean.Trust.Sha256
import PILean.Trust.Sha256Proofs
import PILean.Trust.Provenance
import PILean.Trust.Figure
import PILean.Trust.Fingerprint
import PILean.Trust.Json
import PILean.Trust.Manifest
import PILean.Trust.Build
import PILean.Trust.Files
import PILean.Trust.Verify
import PILean.Version

/-!
# PILean

A pure-Lean image library: colours, geometry, paths, images, a rasteriser with paints and
compositing, PNG and SVG output, and plots. See `README.md` and `docs/DESIGN.md`.
-/
