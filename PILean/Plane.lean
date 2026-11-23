/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plane.Basic
import PILean.Plane.Frame
import PILean.Plane.Draw

/-!
# Plane figures

Figures of plane geometry: points, segments, lines and rays clipped to the frame, arrows,
circles, closed disks, arcs, sectors, polygons, angle marks and labels attached to points, in
world coordinates with `y` upwards, fitted into a page with one scale for both axes, and drawn on
the vector canvas (SVG and PNG from one drawing). Strokes, markers, arrowheads and labels keep
their sizes in pixels at every scale; colours are roles of `Style.plane`, so `Style.dark` gives
the dark twin of any figure in the default colours.

* `PILean.Plane.Basic`: the elements (`Geom`), their looks (`Look`, `Tone`), items with metadata
  (`Item`), the builders and the modifiers.
* `PILean.Plane.Frame`: the map from world to page (`Frame`) and its fitting (`Frame.fit`),
  clipping (`clipLine`).
* `PILean.Plane.Draw`: the drawing (`drawGeom`, `drawItem`) and the figure (`Figure`).

Exact points (rationals, or any type with certified rational enclosures) are in
`PILean.Exact.Plane`.
-/
