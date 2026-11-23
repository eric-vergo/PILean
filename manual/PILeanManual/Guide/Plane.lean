/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILean
import PILean.Trust.Attr
import PILeanVersoManual
import PILeanManual.Meta
import PILeanManual.Pictures

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open PILeanVerso.Manual
open PILeanManual

#doc (Manual) "Plane Figures" =>
%%%
tag := "plane"
%%%

```lean -show
namespace PILeanManual.PlaneGuide
open PILean PILean.Plane
```

# Elements in World Coordinates
%%%
tag := "plane-model"
%%%

{api}`PILean.Plane` draws figures of plane geometry. Items are given in *world coordinates*:
`x` to the right, `y` upwards, angles in radians counterclockwise, as in mathematics. A
{name}`PILean.Plane.Figure` fits them into a page of a given width with one scale for both axes
(circles stay round, angles true), and draws them on the vector canvas, so its SVG and its PNG
are one picture. Strokes, markers, arrowheads, label sizes and offsets are in pixels at every
scale.

The builders make items: {name}`PILean.Plane.point`, {name}`PILean.Plane.segment`,
{name}`PILean.Plane.line` and {name}`PILean.Plane.ray` (clipped to the frame),
{name}`PILean.Plane.arrow`, {name}`PILean.Plane.circle`, {name}`PILean.Plane.disk` (a tinted fill
with its boundary), {name}`PILean.Plane.arc`, {name}`PILean.Plane.sector`,
{name}`PILean.Plane.polygon`, {name}`PILean.Plane.regularPolygon`, {name}`PILean.Plane.polyline`,
{name}`PILean.Plane.angleMark` (an arc with an arrowhead; a decreasing angle marks a clockwise
turn) and {name}`PILean.Plane.label`, attached to a point with a placement and an offset, so that
it follows its point. Modifiers change one aspect each: a colour role
({name}`PILean.Plane.Item.accent`, {name}`PILean.Plane.Item.faint`), a width, a dash pattern, a
tint, an arrowhead, a size, and metadata.

```lean
/-- Two closed disks about `±1`, the chord where their boundaries meet, and a clockwise turn of
72° about the left centre. -/
@[figure]
def twoDisks : Plane.Figure where
  width := 480
  items :=
    let r := 1.9
    let e : Point := ⟨0, Float.sqrt (r * r - 1)⟩
    #[disk ⟨-1, 0⟩ r |>.accent 0 |>.named "the left disk",
      disk ⟨1, 0⟩ r |>.accent 1 |>.named "the right disk",
      segment e ⟨e.x, -e.y⟩ |>.width 3,
      angleMark ⟨-1, 0⟩ (deg 20) (deg 20 - deg 72) (some 44) |>.faint,
      point ⟨-1, 0⟩, point ⟨1, 0⟩, point e |>.accent 2, point ⟨e.x, -e.y⟩ |>.accent 2,
      label "−1" ⟨-1, 0⟩ .left, label "+1" ⟨1, 0⟩ .right,
      label "E" e .above |>.accent 2, label "−E" ⟨e.x, -e.y⟩ .below |>.accent 2]
```

:::figure PILeanManual.PlaneGuide.twoDisks (alt := "Two overlapping tinted disks, blue on the left and orange on the right, with the vertical chord joining the two points where their circles cross, labelled E above and −E below, the centres labelled −1 and +1, and a grey curved arrow turning clockwise about the left centre.")
:::

# Frames and Fitting
%%%
tag := "plane-frame"
%%%

A {name}`PILean.Plane.Frame` maps a world point to the page:
{name}`PILean.Plane.Frame.toScreen` is `(ox + s x, oy - s y)`. The figure's frame
({name}`PILean.Plane.Figure.frame`) is the largest scale at which every item fits inside the
padding: each item has *reaches*, world points with the pixel extent of what is drawn at them (a
marker, half a stroke, a label's box), and {name}`PILean.Plane.Frame.fit` finds that scale, centres
the drawing and makes the page as tall as it needs. A given world box (`view`) is fitted instead
when set.

```lean (name := frameEx)
#eval twoDisks.frame.scale
#eval twoDisks.pixelSize
#eval (twoDisks.frame.toScreen ⟨0, 0⟩).x
```

```leanResult frameEx
```

# Colours, Twins and Metadata
%%%
tag := "plane-style"
%%%

Colours are roles of the style's {name}`PILean.PlaneStyle` ({name}`PILean.Style.plane`): the ink,
three accents, a faint construction colour and the opacity of tinted fills. The light and dark
values meet the WCAG contrast requirements on their backgrounds, so the same figure in
{name}`PILean.Style.dark` is its dark twin; a page with a dark theme shows that twin.

An item's metadata ({name}`PILean.Plane.Item.named`, {name}`PILean.Plane.Item.describedBy`,
{name}`PILean.Plane.Item.withClass`, {name}`PILean.Plane.Item.withId`,
{name}`PILean.Plane.Item.declRef`) is written to SVG as `title` and `desc` children and `class`,
`id` and `data-lean-decl` attributes ({name}`PILean.Canvas.Shape.tagged`); images leave it out.

```lean (name := metaEx)
#eval (Plane.Figure.toSvg { items := #[point ⟨0, 0⟩ |>.named "the origin"] }).length > 0
#eval Svg.isInert twoDisks.toSvg
```

```leanResult metaEx
```

# Exact Points
%%%
tag := "plane-exact"
%%%

{api}`PILean.Exact.Plane` builds plane figures from exact values. A type with an instance of
{name}`PILean.Exact.PlanePoint` gives rational balls ({name}`PILean.Exact.RatBall`) around the
coordinates of its values at any precision; {name}`PILean.Exact.RealValue` does the same for real
numbers such as radii. Rationals, integers and their pairs are their own balls. The builders of
`PILean.Plane.Exact` convert at the last step ({name}`PILean.Exact.PlanePoint.toPoint`), and the
theorems say where the result is drawn: an exact point as a marker centred at the frame's image
of its conversion ({name}`PILean.Plane.Exact.point_draw`,
{name}`PILean.Plane.Exact.figure_points_draw`).

```lean (name := exactEx)
#eval Exact.PlanePoint.toPoint ((1 / 4 : Rat), (-3 : Rat))
#eval Exact.sqrtBall 5 20
#eval Exact.sqrtCertified 5 (Exact.sqrtBall 5 20)
```

```leanResult exactEx
```

The tests give worked instances for numbers of ℚ(√5) and for the ring ℤ\[ζ₅\] as arrays of integer
coefficients, whose balls are checked exactly by squaring rationals.
