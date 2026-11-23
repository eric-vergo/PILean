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

# Regions, Fills, Markers and Ticks
%%%
tag := "plane-regions"
%%%

The intersection, union and difference of two closed disks are regions bounded by arcs of their
circles ({name}`PILean.Plane.lens`, {name}`PILean.Plane.diskUnion`,
{name}`PILean.Plane.diskDifference`), drawn with exact circular arcs, not sampled polygons. A
shape's tint and outline are styled apart: {name}`PILean.Plane.Item.fillTone`,
{name}`PILean.Plane.Item.fillOpacity`, {name}`PILean.Plane.Item.noOutline`,
{name}`PILean.Plane.Item.noFill`. A point's marker can be a dot, a ring, a square, a diamond or
a cross ({name}`PILean.Plane.Item.marker`), on a halo of the background
({name}`PILean.Plane.Item.halo`); a tick ({name}`PILean.Plane.tickOn`) crosses a line at a
point with a length in pixels, resolved when the figure is fitted.

Colours can be named roles of the style ({name}`PILean.PlaneRole`: a light and a dark colour,
{name}`PILean.Plane.Item.role`), so that a figure's own palette has its dark twin too, and a
label can follow the role of the point it names ({name}`PILean.Plane.Item.labelFor`). The
image of a plane figure is composited in sRGB, as a browser composites its SVG, so the PNG and
the SVG show the same tints; text is drawn as shapes by default, so every viewer shows the
lettering the layout measured.

```lean
/-- The lens of two disks as its own region, a chord in two role colours with labels beside its
pieces, and ticks where the pieces meet. -/
@[figure]
def lensFigure : Plane.Figure where
  width := 480
  narrowWidth := some 320
  style := { Style.light with plane := { PlaneStyle.light with
    roles := #[⟨"lens", ⟨154, 69, 0, 255⟩, ⟨245, 184, 61, 255⟩⟩,
      ⟨"a", ⟨29, 78, 216, 255⟩, ⟨143, 176, 252, 255⟩⟩,
      ⟨"b", ⟨13, 107, 99, 255⟩, ⟨94, 224, 200, 255⟩⟩] } }
  items :=
    let p : Point := ⟨0, 1.3⟩
    let q : Point := ⟨0, -1.3⟩
    #[disk ⟨-0.8, 0⟩ 1.5 |>.noFill |>.width 1.5, disk ⟨0.8, 0⟩ 1.5 |>.noFill |>.width 1.5,
      lens ⟨-0.8, 0⟩ 1.5 ⟨0.8, 0⟩ 1.5 |>.role "lens" |>.fillOpacity 0.14,
      segment q ⟨0, 0.3⟩ |>.role "a" |>.width 5, segment ⟨0, 0.3⟩ p |>.role "b" |>.width 5,
      labelBeside "S₁" q ⟨0, 0.3⟩ |>.role "a", labelBeside "S₂" ⟨0, 0.3⟩ p |>.role "b",
      tickOn q p 0.62, point p |>.incident .on "both circles",
      point q |>.incident .on "both circles"]
```

:::figure PILeanManual.PlaneGuide.lensFigure (alt := "Two outlined circles overlapping; the lens between them is tinted orange with a strong outline; a vertical chord joins the circles' crossings, its lower piece blue and labelled S1, its upper piece green and labelled S2, with a tick where they meet.")
:::

# Checks and Automatic Placement
%%%
tag := "plane-checks"
%%%

{name}`PILean.Plane.Figure.problems` reports what a reader objects to in a fitted figure
({api}`PILean.Plane.Check`): labels that overlap, a label over a line or marker it does not
name, something beyond the page, markers that read as one, a point drawn too near a curve for a
reader to see whether it is on it (unless the point records where it is,
{name}`PILean.Plane.Item.incident`; {name}`PILean.Plane.Exact.pointNearDisk` decides it
exactly), and a colour of too little contrast against what it is drawn on, in both themes. A
figure's `checks` level makes `pilean-build` and the Verso blocks warn about them or fail.
Labels placed `auto` (or beside a segment, {name}`PILean.Plane.labelBeside`) take the least
offset and the first side at which they collide with nothing
({name}`PILean.Plane.Figure.autoPlaced`).

```lean (name := checkEx)
#eval (lensFigure.problems).size
#eval (Plane.Figure.problems { items := #[point ⟨0, 0⟩, point ⟨0.001, 0⟩] }).map (·.kind)
```

```leanResult checkEx
```

# Explorers
%%%
tag := "plane-explorers"
%%%

An {name}`PILean.Explorer` is a finite family of frames computed in Lean: a parameter axis shown
with a slider ({name}`PILean.Plane.slider`), a step sequence shown with previous, play and next
({name}`PILean.Plane.stepper`), or both ({name}`PILean.Explorer.grid`). Its files are its poster;
a Verso page shows every frame inline with `:::figure_explorer`, with pan and zoom, and lists the
frames when it cannot run the script. {name}`PILean.Explorer.toAnimation` plays a step sequence
as an animation, and {name}`PILean.Plane.animation` does so for plane figures.

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

{api}`PILean.Exact.Algebraic` has numbers of ℚ(√d) ({name}`PILean.Exact.QSqrt`), the ring
ℤ\[ζ₅\] as arrays of integer coefficients ({name}`PILean.Exact.Zeta5`), exact square roots
({name}`PILean.Exact.SqrtOf`), and constructions whose results are certified enclosures
({name}`PILean.Exact.circleCircle`, {name}`PILean.Exact.lineCircle`,
{name}`PILean.Exact.foot`, {name}`PILean.Exact.midpoint`).

```lean (name := algEx)
#eval (Exact.Zeta5.pow 1 - Exact.Zeta5.pow 2 + Exact.Zeta5.ofInt 1).normSq
#eval Exact.QSqrt5.phi * Exact.QSqrt5.phi
```

```leanResult algEx
```
