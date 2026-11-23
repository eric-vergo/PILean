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
/-- Two closed disks of radius `1.9` about `±1`, the chord where their boundaries meet (at
`(0, ±√(1.9² - 1))`), and a clockwise turn of 72° about the left centre. -/
@[figure]
def twoDisks : Plane.Figure where
  width := 480
  items :=
    let r := 1.9
    let e : Point := ⟨0, Float.sqrt (r * r - 1)⟩
    let onBoth := fun (it : Item) =>
      it.incident .on "the left circle" |>.incident .on "the right circle"
    #[disk ⟨-1, 0⟩ r |>.accent 0 |>.named "the left circle",
      disk ⟨1, 0⟩ r |>.accent 1 |>.named "the right circle",
      segment e ⟨e.x, -e.y⟩ |>.width 3,
      angleMark ⟨-1, 0⟩ (deg 20) (deg 20 - deg 72) (some 44) |>.faint,
      point ⟨-1, 0⟩, point ⟨1, 0⟩, onBoth (point e |>.accent 2),
      onBoth (point ⟨e.x, -e.y⟩ |>.accent 2),
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
/-- The lens of two disks as its own region, the chord between the circles' crossings in two role
colours with labels beside its pieces, and a tick where the pieces meet. -/
@[figure]
def lensFigure : Plane.Figure where
  width := 480
  narrowWidth := some 320
  style := { Style.light with plane := { PlaneStyle.light with
    roles := #[⟨"lens", ⟨154, 69, 0, 255⟩, ⟨245, 184, 61, 255⟩⟩,
      ⟨"a", ⟨29, 78, 216, 255⟩, ⟨143, 176, 252, 255⟩⟩,
      ⟨"b", ⟨13, 107, 99, 255⟩, ⟨94, 224, 200, 255⟩⟩] } }
  items :=
    -- the circles of radius 1.5 about (±0.8, 0) cross at (0, ±√(1.5² - 0.8²)) = (0, ±√1.61)
    let h := Float.sqrt (1.5 * 1.5 - 0.8 * 0.8)
    let p : Point := ⟨0, h⟩
    let q : Point := ⟨0, -h⟩
    let m : Point := q.lerp p 0.62
    let corner := fun (c : Point) =>
      point c |>.incident .on "the left circle" |>.incident .on "the right circle"
        |>.incident .on "the lens"
    #[disk ⟨-0.8, 0⟩ 1.5 |>.noFill |>.width 1.5 |>.named "the left circle",
      disk ⟨0.8, 0⟩ 1.5 |>.noFill |>.width 1.5 |>.named "the right circle",
      lens ⟨-0.8, 0⟩ 1.5 ⟨0.8, 0⟩ 1.5 |>.role "lens" |>.fillOpacity 0.14 |>.named "the lens",
      segment q m |>.role "a" |>.width 5, segment m p |>.role "b" |>.width 5,
      labelBeside "S₁" q m |>.role "a", labelBeside "S₂" m p |>.role "b",
      tickOn q p 0.62, corner p, corner q]
```

```lean -show
-- The figures of this chapter have no layout problems, and the lens's corners are on both
-- circles (and the chord's ends on both circles of the first figure).
#guard twoDisks.problems.isEmpty && lensFigure.problems.isEmpty
#guard
  let p : Point := ⟨0, Float.sqrt (1.5 * 1.5 - 0.8 * 0.8)⟩
  ((p - ⟨-0.8, 0⟩).norm - 1.5).abs < 1e-12 && ((p - ⟨0.8, 0⟩).norm - 1.5).abs < 1e-12
#guard
  let e : Point := ⟨0, Float.sqrt (1.9 * 1.9 - 1)⟩
  ((e - ⟨-1, 0⟩).norm - 1.9).abs < 1e-12 && ((e - ⟨1, 0⟩).norm - 1.9).abs < 1e-12
```

:::figure PILeanManual.PlaneGuide.lensFigure (alt := "Two outlined circles overlapping; the lens between them is tinted orange with a strong outline; a vertical chord joins the circles' crossings, its lower piece blue and labelled S1, its upper piece green and labelled S2, with a tick where they meet.")
:::

# Checks and Automatic Placement
%%%
tag := "plane-checks"
%%%

{name}`PILean.Plane.Figure.problems` reports what a reader objects to in a fitted figure
({api}`PILean.Plane.Check`): labels that overlap, a label over a line or marker it does not
name (a label centred on a line included), something beyond the page, markers that read as one,
a point drawn too near an element for a reader to see whether it is on it, a colour of too
little contrast against what it is drawn on (at its opacity, along every stroke, over the fills
beneath), in both themes, a number that is not finite, a polygon or segment with too few
distinct points, a circle, disk, arc, sector, region or angle mark whose radius is zero, negative
or not finite (drawn as nothing), a role the style does not name, and a colour the dark theme of an
inline picture would get wrong. A point near an element records
where it stands relative to it with {name}`PILean.Plane.Item.incident`, naming the element by
its title ({name}`PILean.Plane.Item.named`); the check holds the record to that element, so a
point recorded on a circle but drawn off it is a problem too, and a record against one element
does not excuse the point from another. {name}`PILean.Plane.Exact.pointNearDisk` decides the
incidence exactly. A figure's `checks` level makes `pilean-build` and the Verso blocks warn
about the problems or fail. Labels placed `auto` (or beside a segment,
{name}`PILean.Plane.labelBeside`) take the least offset and the first side at which they collide
with nothing, keeping a few pixels from strokes where they can
({name}`PILean.Plane.Figure.autoPlaced`).

```lean (name := checkEx)
#eval (lensFigure.problems).size
#eval (Plane.Figure.problems { items := #[point ⟨0, 0⟩, point ⟨0.001, 0⟩] }).map (·.kind)
#eval (Plane.Figure.problems { items := #[circle ⟨0, 0⟩ 1 |>.named "c",
  point ⟨1.2, 0⟩ |>.incident .on "c"] }).map (·.kind)
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
as an animation, every step as long as the others, and {name}`PILean.Plane.animation` does so
for plane figures, composited and lettered as the figures are. Every frame of an explorer is a
file of its own with its fingerprint, so the pictures a page shows inline are in the manifest,
and every frame keeps its figure's problems, which a build reports frame by frame.

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
ℤ\[ζ₅\] as arrays of integer coefficients ({name}`PILean.Exact.Zeta5`, compared by their
normal form), exact square roots ({name}`PILean.Exact.SqrtOf`), and constructions whose results
are enclosures ({name}`PILean.Exact.circleCircle`, {name}`PILean.Exact.lineCircle`,
{name}`PILean.Exact.foot`, {name}`PILean.Exact.midpoint`). Nothing is made up: a division by a
ball that holds 0 is `none` ({name}`PILean.Exact.RatBall.inv`), and a meeting of two curves is
two points, a tangent point, none, or undecided ({name}`PILean.Exact.Meeting`), the last when
the balls tried do not decide it; a radius not decided to be positive is no circle
(`degenerate`), never read as its absolute value. The order and the equality of ℚ(√d) need
`d` not to be a square ({name}`PILean.Exact.QSqrt.NonSquare`, given for 2, 3 and 5): for a square
`d` the pairs `(a, b)` do not determine the number, and comparing them cannot be written.

A figure's theorem writes out the figure's items in drawing order, each with its colour, title,
labels and recorded incidences, so that a change to what the figure draws breaks the build, and
checks the incidences by exact arithmetic in the representation, so that the picture's facts are
facts about its items. {name}`PILean.Plane.Exact.IsPoint` and its companions say what an item
is, for lemmas such as {name}`PILean.Plane.Exact.IsPoint.draw`.

```lean (name := algEx)
#eval (Exact.Zeta5.pow 1 - Exact.Zeta5.pow 2 + Exact.Zeta5.ofInt 1).normSq
#eval Exact.QSqrt5.phi * Exact.QSqrt5.phi
#eval Exact.RatBall.inv ⟨0, 1⟩
#eval (Exact.circleCircle ((0 : Rat), (0 : Rat)) ((2 : Rat), (0 : Rat)) (1 : Rat) (1 : Rat)).decided
```

```leanResult algEx
```
