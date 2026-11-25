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
import PILean.Pdf.Object
import PILean.Pdf.Write
import PILean.Pdf.Read
import PILean.Pdf.Check
import PILean.Pdf.Figures
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
import PILean.CheckLevel
import PILean.Plot.Figure
import PILean.Plot.Check
import PILean.Plot.Proofs
import PILean.Plot.Exact
import PILean.Plane.Basic
import PILean.Plane.Frame
import PILean.Plane.Draw
import PILean.Plane.Check
import PILean.Plane.Render
import PILean.Plane
import PILean.Exact.Plane
import PILean.Exact.Algebraic
import PILean.Exact.Spec
import PILean.Explorer
import PILean.Plane.Graph
import PILean.Plane.Motion
import PILean.Plane.MotionPlan
import PILean.Diagram.Basic
import PILean.Diagram.Graph
import PILean.Diagram.Hasse
import PILean.Diagram.Young
import PILean.Diagram.Perm
import PILean.Diagram.Path
import PILean.Diagram.Tree
import PILean.Diagram.SetSystem
import PILean.Diagram.CommDiagram
import PILean.Diagram.Group
import PILean.Diagram.Quiver
import PILean.Diagram.Sequence
import PILean.Diagram.Lattice
import PILean.Diagram.ZeroPole
import PILean.Raster.DomainColouring
import PILean.Graph.Fixed
import PILean.Graph.Model
import PILean.Graph.Layout
import PILean.Graph.Layering
import PILean.Graph.Ordering
import PILean.Graph.Compound
import PILean.Graph.Coordinates
import PILean.Graph.Route
import PILean.Graph.Nested
import PILean.Graph.Channel
import PILean.Graph.Bundle
import PILean.Graph.Layered
import PILean.Graph.Pack
import PILean.Graph.Web
import PILean.Graph.Simple
import PILean.Graph.Draw
import PILean.Graph.Check
import PILean.Graph.Dot
import PILean.Graph.Proofs
import PILean.Graph.Spec
import PILean.Raster.Coverage
import PILean.Raster.Canvas
import PILean.Raster.Stroke
import PILean.Raster.Draw
import PILean.Raster.Blur
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
compositing, PNG and SVG output, plots, plane figures, graphs, and diagrams of combinatorial
objects and orders drawn from their data (`PILean.Diagram`). See `README.md` and
`docs/DESIGN.md`.
-/
