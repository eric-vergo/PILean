/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Canvas
import PILean.Style
import PILean.CheckLevel

/-!
# Plane figures: the model

The elements of a figure of plane geometry, in *world coordinates*: `x` to the right and `y`
upwards, angles in radians counterclockwise from the positive `x` axis, as in mathematics.
`PILean.Plane.Frame` maps them to the page and `PILean.Plane.Figure` draws them; lengths given in
pixels (stroke widths, marker sizes, arrowheads, label offsets, the radius of an angle mark) stay
in pixels whatever the scale.

* `Geom`: what an element is: a point, a segment, a line or a ray (clipped to the frame), an
  arrow, a circle, a closed disk (a tinted fill with its boundary), an arc, a sector, a polygon or
  a polyline, an angle mark with an arrowhead, or a label attached to a point.
* `Look`: how it is drawn: a `Tone` (a role of the style's `PlaneStyle`, so that the light and
  the dark style colour it alike, or a fixed colour), a stroke width, a dash pattern, whether a
  closed shape is tinted, an arrowhead, a size.
* `Item`: an element with its look and metadata (`Canvas.ShapeInfo`), or a group of items.

The builders (`point`, `segment`, `line`, `ray`, `arrow`, `circle`, `disk`, `arc`, `sector`,
`polygon`, `regularPolygon`, `polyline`, `angleMark`, `label`, `group`) make items with the default
look; the modifiers (`Item.tone`, `Item.accent`, `Item.faint`, `Item.width`, `Item.dashed`,
`Item.filled`, `Item.size`, `Item.named`, `Item.describedBy`, `Item.withClass`, `Item.withId`,
`Item.declRef`) change one aspect, so that a figure reads as a list:

```
#[Plane.disk ⟨-1, 0⟩ 1.9 |>.accent 0, Plane.point ⟨0, 0⟩ |>.named "the origin"]
```

## Main definitions

* `Tone`, `Placement`, `Geom`, `Look`, `Item`.
* `deg`, `polar`, `unit`, `rootOfUnity`: points and angles.
-/

namespace PILean.Plane

/-- π. -/
def pi : Float := 3.141592653589793

/-- `x` degrees in radians. -/
def deg (x : Float) : Float := x * pi / 180

/-- The point at distance `r` from the origin in the direction `θ` (radians). -/
def polar (r θ : Float) : Point := ⟨r * θ.cos, r * θ.sin⟩

/-- The unit vector in the direction `θ` (radians). -/
def unit (θ : Float) : Point := polar 1 θ

/-- `ζₙ ^ j` with `ζₙ = e^{2πi/n}`, as a point: the unit vector at angle `2πj/n` (the origin for
`n = 0`). -/
def rootOfUnity (n j : Nat) : Point :=
  if n == 0 then ⟨0, 0⟩ else unit (2 * pi * j.toFloat / n.toFloat)

/-- The colour of an element: a role of the style's `PlaneStyle`, or a fixed colour. -/
inductive Tone where
  /-- The ink. -/
  | ink
  /-- Accent `i` of the style (wrapping round). -/
  | accent (i : Nat)
  /-- The faint construction colour. -/
  | faint
  /-- A fixed colour, the same in every style. -/
  | color (c : Rgba)
  /-- A named role of the style (`PlaneStyle.roles`), in its light or dark colour; the ink when
  the style does not name it. -/
  | role (name : String)
  deriving BEq, Inhabited, Repr

/-- The colour of a tone in a style. -/
def Tone.resolve (p : PlaneStyle) : Tone → Rgba
  | .ink => p.ink
  | .accent i => p.accent i
  | .faint => p.faint
  | .color c => c
  | .role n => (p.role? n).getD p.ink

/-- The shape of a point's marker. -/
inductive MarkerShape where
  /-- A filled disc. -/
  | dot
  /-- An open circle. -/
  | ring
  /-- A filled square. -/
  | square
  /-- A filled diamond. -/
  | diamond
  /-- A cross of two strokes. -/
  | cross
  deriving BEq, Inhabited, Repr

/-- How two disks combine into a region bounded by arcs of their circles. -/
inductive RegionOp where
  /-- The points in both (a lens when the circles cross). -/
  | intersection
  /-- The points in either. -/
  | union
  /-- The points in the first and not in the second. -/
  | difference
  deriving BEq, Inhabited, Repr

/-- Where a label stands relative to its point: centred on it, on one of eight sides, or in a
direction (radians, counterclockwise from the positive `x` axis, in world coordinates). -/
inductive Placement where
  /-- Centred on the point. -/
  | center
  /-- Above. -/
  | above
  /-- Below. -/
  | below
  /-- To the left. -/
  | left
  /-- To the right. -/
  | right
  /-- Above and to the left. -/
  | aboveLeft
  /-- Above and to the right. -/
  | aboveRight
  /-- Below and to the left. -/
  | belowLeft
  /-- Below and to the right. -/
  | belowRight
  /-- In the direction `θ`. -/
  | toward (θ : Float)
  /-- The first of the eight sides, from above right round the compass, where the label collides
  with nothing, at the least offset that clears (`Figure.autoPlaced`); above right when every side
  collides. -/
  | auto
  /-- Beside a line in the direction `θ` (radians): on its left or, if that collides, its right
  side, at the least offset that clears (`Figure.autoPlaced`); a label for a piece of a segment. -/
  | across (θ : Float)
  deriving BEq, Inhabited, Repr

/-- The unit direction of a placement on screen (`y` down); `(0, 0)` for `center`. -/
def Placement.screenDir : Placement → Point
  | .center => ⟨0, 0⟩
  | .above => ⟨0, -1⟩
  | .below => ⟨0, 1⟩
  | .left => ⟨-1, 0⟩
  | .right => ⟨1, 0⟩
  | .aboveLeft => ⟨-0.7071067811865476, -0.7071067811865476⟩
  | .aboveRight => ⟨0.7071067811865476, -0.7071067811865476⟩
  | .belowLeft => ⟨-0.7071067811865476, 0.7071067811865476⟩
  | .belowRight => ⟨0.7071067811865476, 0.7071067811865476⟩
  | .toward θ => ⟨θ.cos, -θ.sin⟩
  | .auto => ⟨0.7071067811865476, -0.7071067811865476⟩
  | .across θ => ⟨-θ.sin, -θ.cos⟩

/-- The eight sides `Placement.auto` tries, in order. -/
def Placement.compass : Array Placement :=
  #[.aboveRight, .above, .aboveLeft, .left, .belowLeft, .below, .belowRight, .right]

/-- Where a point stands relative to a curve or a region: on it, inside, or outside. -/
inductive Incidence where
  /-- On the curve (the boundary). -/
  | on
  /-- Inside the region. -/
  | inside
  /-- Outside the region. -/
  | outside
  deriving BEq, Inhabited, Repr

/-- The incidence in words: `on`, `inside`, `outside`. -/
def Incidence.text : Incidence → String
  | .on => "on" | .inside => "inside" | .outside => "outside"

/-- What an element is, in world coordinates (see the module docstring). Angles are in radians,
counterclockwise; lengths marked *pixels* are on the page. -/
inductive Geom where
  /-- A point, drawn as a marker. -/
  | point (p : Point)
  /-- The segment from `a` to `b`. -/
  | segment (a b : Point)
  /-- The line through `a` and `b`, clipped to the frame. -/
  | line (a b : Point)
  /-- The ray from `a` through `b`, clipped to the frame. -/
  | ray (a b : Point)
  /-- The segment from `a` to `b` with an arrowhead at `b`. -/
  | arrow (a b : Point)
  /-- The circle with centre `c` and radius `r`. -/
  | circle (c : Point) (r : Float)
  /-- The closed disk with centre `c` and radius `r`: a tinted fill and its boundary. -/
  | disk (c : Point) (r : Float)
  /-- The arc of the circle with centre `c` and radius `r` from angle `θ₀` to `θ₁`
  (counterclockwise when `θ₁ > θ₀`, clockwise otherwise). -/
  | arc (c : Point) (r θ₀ θ₁ : Float)
  /-- The sector of the disk with centre `c` and radius `r` between the angles `θ₀` and `θ₁`. -/
  | sector (c : Point) (r θ₀ θ₁ : Float)
  /-- The closed polygon with these vertices. -/
  | polygon (vs : Array Point)
  /-- The open polyline through these points. -/
  | polyline (vs : Array Point)
  /-- An angle mark at `c`: an arc of `radius` *pixels* (the style's `angleRadius` when `none`)
  from angle `θ₀` to `θ₁` with an arrowhead at `θ₁` (so `θ₁ < θ₀` marks a clockwise turn). -/
  | angleMark (c : Point) (θ₀ θ₁ : Float) (radius : Option Float)
  /-- The text `s` attached to the point `at_`, placed `offset` *pixels* (the style's
  `labelOffset` when `none`) away from it in the direction of `place`. -/
  | label (s : String) (at_ : Point) (place : Placement) (offset : Option Float)
  /-- A tick mark at `p` across the direction `dir` (a world vector along the line or curve it
  marks), `length` *pixels* long (the style's `tickLength` when `none`), resolved when the figure
  is fitted. -/
  | tick (p dir : Point) (length : Option Float)
  /-- The region two closed disks make (`RegionOp`), bounded by arcs of their circles. -/
  | disks (op : RegionOp) (c₁ : Point) (r₁ : Float) (c₂ : Point) (r₂ : Float)
  deriving Inhabited, Repr

/-- Whether every number of an element is finite: its points, radii, angles and the pixel lengths
it gives (an offset, a radius, a tick's length). An element that is not is drawn as nothing or as
nonsense, and `Figure.problems` reports it. -/
def Geom.finite : Geom → Bool
  | .point p => p.isFinite
  | .segment a b | .line a b | .ray a b | .arrow a b => a.isFinite && b.isFinite
  | .circle c r | .disk c r => c.isFinite && r.isFinite
  | .arc c r θ₀ θ₁ | .sector c r θ₀ θ₁ =>
    c.isFinite && r.isFinite && θ₀.isFinite && θ₁.isFinite
  | .polygon vs | .polyline vs => vs.all Point.isFinite
  | .angleMark c θ₀ θ₁ radius =>
    c.isFinite && θ₀.isFinite && θ₁.isFinite && radius.all Float.isFinite
  | .label _ p place offset =>
    p.isFinite && offset.all Float.isFinite && match place with
      | .toward θ | .across θ => θ.isFinite
      | _ => true
  | .tick p dir length => p.isFinite && dir.isFinite && length.all Float.isFinite
  | .disks _ c₁ r₁ c₂ r₂ => c₁.isFinite && r₁.isFinite && c₂.isFinite && r₂.isFinite

/-- How an element is drawn. `none` takes the style's value. -/
structure Look where
  /-- The colour. -/
  tone : Tone := .ink
  /-- The stroke width in pixels. -/
  width : Option Float := none
  /-- The dash pattern in pixels (empty for solid). -/
  dash : Array Float := #[]
  /-- Whether a polygon or sector is tinted inside (a disk and a region of disks are unless
  `noFill`). -/
  filled : Bool := false
  /-- Whether a disk or a region of disks is left untinted. -/
  noFill : Bool := false
  /-- The colour of the tint, when it is not the item's own (`tone`). -/
  fill : Option Tone := none
  /-- The opacity of the tint, when it is not the style's `fillOpacity`. -/
  fillOpacity : Option Float := none
  /-- Whether a closed shape's outline is drawn. -/
  outline : Bool := true
  /-- The shape of a point's marker. -/
  marker : MarkerShape := .dot
  /-- Whether a marker has a halo of the background colour, so that it stays legible on a line. -/
  halo : Bool := true
  /-- The weight of a label (1 is regular). -/
  weight : Option Float := none
  /-- Whether a label is slanted (drawn as shapes; SVG text in a font family is upright). -/
  italic : Bool := false
  /-- Whether an arc or a segment ends in an arrowhead (an arrow and an angle mark always do). -/
  arrowHead : Bool := false
  /-- The radius of a point's marker or the size of a label, in pixels. -/
  size : Option Float := none
  /-- For a point: where it stands relative to the curves or regions it is near, as decided by the
  author (exactly, for exact points), each with the title of the element it is relative to
  (`Item.named`). A point drawn too near an element for a reader to see on which side it is must
  record it, and the layout checks hold each record to the element it names
  (`PILean.Plane.Check`). -/
  incidences : Array (Incidence × String) := #[]
  deriving Inhabited, Repr

/-- A plane figure's element with its look and metadata, or a group of items with metadata. -/
inductive Item where
  /-- An element. -/
  | shape (g : Geom) (look : Look := {}) (info : Canvas.ShapeInfo := {})
  /-- Items drawn together, with metadata for the group. -/
  | group (items : Array Item) (info : Canvas.ShapeInfo := {})
  deriving Inhabited

/-! ### Builders -/

/-- A point. -/
def point (p : Point) : Item := .shape (.point p)

/-- The segment from `a` to `b`. -/
def segment (a b : Point) : Item := .shape (.segment a b)

/-- The line through `a` and `b`, clipped to the frame. -/
def line (a b : Point) : Item := .shape (.line a b)

/-- The ray from `a` through `b`, clipped to the frame. -/
def ray (a b : Point) : Item := .shape (.ray a b)

/-- The segment from `a` to `b` with an arrowhead at `b`. -/
def arrow (a b : Point) : Item := .shape (.arrow a b)

/-- The circle with centre `c` and radius `r`. -/
def circle (c : Point) (r : Float) : Item := .shape (.circle c r)

/-- The closed disk with centre `c` and radius `r`. -/
def disk (c : Point) (r : Float) : Item := .shape (.disk c r)

/-- The arc from angle `θ₀` to `θ₁` (radians, counterclockwise when `θ₁ > θ₀`). -/
def arc (c : Point) (r θ₀ θ₁ : Float) : Item := .shape (.arc c r θ₀ θ₁)

/-- The sector between the angles `θ₀` and `θ₁`, tinted. -/
def sector (c : Point) (r θ₀ θ₁ : Float) : Item :=
  .shape (.sector c r θ₀ θ₁) { filled := true }

/-- The closed polygon with these vertices. -/
def polygon (vs : Array Point) : Item := .shape (.polygon vs)

/-- The vertices of the regular `n`-gon with centre `c` whose first vertex is at distance `r` in
the direction `phase`, counterclockwise. -/
def regularVertices (c : Point) (r : Float) (n : Nat) (phase : Float := 0) : Array Point :=
  (List.range n).toArray.map fun k => c + polar r (phase + 2 * pi * k.toFloat / n.toFloat)

/-- The regular `n`-gon with centre `c` and circumradius `r`, its first vertex in the direction
`phase`. -/
def regularPolygon (c : Point) (r : Float) (n : Nat) (phase : Float := 0) : Item :=
  polygon (regularVertices c r n phase)

/-- The open polyline through these points. -/
def polyline (vs : Array Point) : Item := .shape (.polyline vs)

/-- An angle mark at `c` from angle `θ₀` to `θ₁` (radians) with an arrowhead at `θ₁`, of radius
`radius` pixels (the style's `angleRadius` when `none`): `angleMark c 0 (-deg 72)` marks a turn of
72° clockwise. -/
def angleMark (c : Point) (θ₀ θ₁ : Float) (radius : Option Float := none) : Item :=
  .shape (.angleMark c θ₀ θ₁ radius)

/-- The text `s` at the point `p`, in the direction `place`, `offset` pixels away (the style's
`labelOffset` when `none`). -/
def label (s : String) (p : Point) (place : Placement := .center) (offset : Option Float := none) :
    Item :=
  .shape (.label s p place offset)

/-- Items drawn together. -/
def group (items : Array Item) : Item := .group items

/-- The text `s` beside the segment from `a` to `b`, at its middle, on whichever side is clear
(`Placement.across`): a label for a piece of a chord. -/
def labelBeside (s : String) (a b : Point) (offset : Option Float := none) : Item :=
  let v := b - a
  label s (a.mid b) (.across (Float.atan2 v.y v.x)) offset

/-- A tick mark at `p` across the direction `dir`, `length` pixels long. -/
def tick (p dir : Point) (length : Option Float := none) : Item := .shape (.tick p dir length)

/-- A tick mark across the segment from `a` to `b` at the fraction `t` of the way. -/
def tickOn (a b : Point) (t : Float) (length : Option Float := none) : Item :=
  tick (a.lerp b t) (b - a) length

/-- The intersection of two closed disks (a lens when their circles cross), tinted. -/
def lens (c₁ : Point) (r₁ : Float) (c₂ : Point) (r₂ : Float) : Item :=
  .shape (.disks .intersection c₁ r₁ c₂ r₂)

/-- The union of two closed disks, tinted. -/
def diskUnion (c₁ : Point) (r₁ : Float) (c₂ : Point) (r₂ : Float) : Item :=
  .shape (.disks .union c₁ r₁ c₂ r₂)

/-- The first closed disk without the second, tinted. -/
def diskDifference (c₁ : Point) (r₁ : Float) (c₂ : Point) (r₂ : Float) : Item :=
  .shape (.disks .difference c₁ r₁ c₂ r₂)

/-! ### Modifiers -/

namespace Item

/-- The item with its look changed (a group's items each). -/
def mapLook (f : Look → Look) : Item → Item
  | .shape g l i => .shape g (f l) i
  | .group xs i => .group (xs.attach.map fun ⟨x, _⟩ => mapLook f x) i

/-- The item with its metadata changed (a group's own). -/
def mapInfo (f : Canvas.ShapeInfo → Canvas.ShapeInfo) : Item → Item
  | .shape g l i => .shape g l (f i)
  | .group xs i => .group xs (f i)

/-- The item in a tone. -/
def tone (t : Tone) (it : Item) : Item := it.mapLook ({ · with tone := t })

/-- The item in accent `i`. -/
def accent (i : Nat) (it : Item) : Item := it.tone (.accent i)

/-- The item in the faint construction colour. -/
def faint (it : Item) : Item := it.tone .faint

/-- The item in a fixed colour. -/
def color (c : Rgba) (it : Item) : Item := it.tone (.color c)

/-- The item with a stroke width in pixels. -/
def width (w : Float) (it : Item) : Item := it.mapLook ({ · with width := some w })

/-- The item dashed with a pattern in pixels (`#[5, 4]` by default). -/
def dashed (pattern : Array Float := #[5, 4]) (it : Item) : Item :=
  it.mapLook ({ · with dash := pattern })

/-- The item tinted inside (polygons and sectors), or not. -/
def filled (b : Bool := true) (it : Item) : Item := it.mapLook ({ · with filled := b })

/-- The item ending in an arrowhead (segments and arcs). -/
def withArrow (it : Item) : Item := it.mapLook ({ · with arrowHead := true })

/-- The item in a named role of the style (`PlaneStyle.roles`). -/
def role (name : String) (it : Item) : Item := it.tone (.role name)

/-- The item's tint in another colour than its outline. -/
def fillTone (t : Tone) (it : Item) : Item := it.mapLook ({ · with fill := some t })

/-- The item's tint at an opacity of its own. -/
def fillOpacity (a : Float) (it : Item) : Item := it.mapLook ({ · with fillOpacity := some a })

/-- The item without its outline (a tinted region alone). -/
def noOutline (it : Item) : Item := it.mapLook ({ · with outline := false })

/-- The item without its tint (a disk or region outlined alone). -/
def noFill (it : Item) : Item := it.mapLook ({ · with noFill := true, filled := false })

/-- The point drawn with another marker. -/
def marker (m : MarkerShape) (it : Item) : Item := it.mapLook ({ · with marker := m })

/-- The marker with or without its halo of the background colour. -/
def halo (b : Bool) (it : Item) : Item := it.mapLook ({ · with halo := b })

/-- The label in bold (weight 1.4). -/
def bold (it : Item) : Item := it.mapLook ({ · with weight := some 1.4 })

/-- The label slanted. -/
def italic (it : Item) : Item := it.mapLook ({ · with italic := true })

/-- The item with a marker radius or label size in pixels. -/
def size (s : Float) (it : Item) : Item := it.mapLook ({ · with size := some s })

/-- The point recorded as standing `rel` (on, inside, outside) relative to the element whose title
is `what` (`Item.named`, `"the window"`; on a disk or a region means on its boundary): the look
keeps the record for the layout checks, which hold it to that element (`PILean.Plane.Check`),
and the title says it (`inside the window`, after the title if there is one). Recording a second
incidence keeps the first. -/
def incident (rel : Incidence) (what : String) (it : Item) : Item :=
  let words := s!"{rel.text} {what}"
  (it.mapLook fun l => { l with incidences := l.incidences.push (rel, what) }).mapInfo fun i =>
    { i with title := if i.title.isEmpty then words else s!"{i.title}, {words}" }

/-- A label for a point item, in the point's colour (the label follows the role of what it names):
the text `s` at the point, placed `place`; for any other item, an ink label at the origin. -/
def labelFor (it : Item) (s : String) (place : Placement := .auto) : Item :=
  match it with
  | .shape (.point p) l _ => (Plane.label s p place).tone l.tone
  | _ => Plane.label s ⟨0, 0⟩ place

/-- The item with an accessible name (an SVG `title`). -/
def named (t : String) (it : Item) : Item := it.mapInfo ({ · with title := t })

/-- The item with an accessible description (an SVG `desc`). -/
def describedBy (d : String) (it : Item) : Item := it.mapInfo ({ · with description := d })

/-- The item with a CSS class added. -/
def withClass (c : String) (it : Item) : Item :=
  it.mapInfo fun i => i.merge { cssClass := c }

/-- The item with a stable id. -/
def withId (s : String) (it : Item) : Item := it.mapInfo ({ · with id := s })

/-- The item referring to a Lean declaration (`data-lean-decl` in SVG): `.declRef ``Foo.bar`. -/
def declRef (n : Lean.Name) (it : Item) : Item := it.mapInfo ({ · with leanDecl := n.toString })

end Item

end PILean.Plane
