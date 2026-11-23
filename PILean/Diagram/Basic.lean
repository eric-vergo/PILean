/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Exact.Plane

/-!
# Diagrams: exact drawings of finite mathematical objects

A `Diagram` is a list of `Mark`s, each an exact shape (rational coordinates, `y` up) tagged with
the `Part` of the object it depicts: vertex `i`, edge `(i, j)`, cell `(i, j)`, the entry of a cell,
the strand of a value, a set, a step of a path. A diagram is drawn as a plane figure
(`Diagram.toPlane`): one plane item per mark, in order, built from the mark's exact points by the
builders of `PILean.Exact.Plane`.

The combinatorial kinds (graphs, Hasse diagrams, Young diagrams, permutations, trees, set systems,
lattice paths) share one pattern, which later kinds follow too:

* a plain-data structure, the mathematical content (a relation on `Fin n`, a partition as a list);
* a pure `layout`, the exact positions;
* `draw data layout : Diagram` and `figure data := draw data (layout data)`;
* a decidable predicate `Faithful data layout diagram`, stated by reading the diagram back
  (`Diagram.edges`, `Diagram.cells`, …) and comparing what it draws with the data: as full lists
  (every drawn part, in order, against the canonical list of the data's parts) and mark by mark
  (each mark is placed where the layout puts the part it depicts);
* `draw_faithful : Faithful data L (draw data L)` for every layout `L`, and `builder_faithful`,
  its instance for `layout`.

So a theorem about a kind is a theorem about the exact marks of the figure. What happens after
them (the conversion of rationals to floating point, the fitting of the frame, text, the
rasteriser, colours and style) is the tested code of plane figures, and no theorem speaks of it.

## Main definitions

* `QPoint`, `Part`, `Side`, `Shape`, `Ink`, `Mark`, `Diagram`
* `Diagram.edges`, `Diagram.vertices`, `Diagram.cells`, `Diagram.entries`, `Diagram.steps`:
  read-backs
* `Mark.toItem`, `Mark.toItemIn`, `Diagram.toPlane`: the drawing as a plane figure
* `maxMarks`: the most marks a diagram is drawn with

## Main results

* `Diagram.toPlane_items`: the plane figure's items are the marks' items, in order.
-/

namespace PILean.Diagram

open PILean.Plane

/-- A point with exact rational coordinates, `y` up. -/
abbrev QPoint := Rat × Rat

/-- The part of the object of study a mark depicts. -/
inductive Part where
  /-- Vertex, element or node `i`. -/
  | vertex (i : Nat)
  /-- The edge, cover or parent link from `i` to `j`. -/
  | edge (i j : Nat)
  /-- The cell in row `i` and column `j`. -/
  | cell (i j : Nat)
  /-- The entry written in the cell `(i, j)` (row `i` of a two-line notation, say). -/
  | entry (i j : Nat)
  /-- The strand of the value `i` (a permutation's wire). -/
  | strand (i : Nat)
  /-- Set `k` of a set system. -/
  | set (k : Nat)
  /-- Element `x` drawn in the region of the sets of the bit mask `mask`. -/
  | member (x mask : Nat)
  /-- Step `k` of a path. -/
  | step (k : Nat)
  /-- Arrow `k` of a diagram, from object `i` to object `j` (several arrows may join the same two
  objects, and an arrow may be a loop, `i = j`). -/
  | arrow (k i j : Nat)
  /-- The 2-cell `k` of a diagram: a double arrow between two arrows. -/
  | twoCell (k : Nat)
  /-- The heading of row `i` (`axis = 0`) or of column `i` (`axis = 1`) of a table. -/
  | header (axis i : Nat)
  /-- An annotation (a title, an axis name): text that depicts no part of the object. -/
  | note (k : Nat)
  /-- A guide (grid lines, a frame): a drawing that depicts no part of the object. -/
  | guide
  deriving DecidableEq, Repr, Inhabited

/-- Which side of its point a text stands on. -/
inductive Side where
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
  /-- On the side the plane figure's label placement chooses (`Placement.auto`). -/
  | auto
  deriving DecidableEq, Repr, Inhabited

/-- The plane figure's placement of a side. -/
def Side.toPlacement : Side → Placement
  | .center => .center
  | .above => .above
  | .below => .below
  | .left => .left
  | .right => .right
  | .aboveLeft => .aboveLeft
  | .aboveRight => .aboveRight
  | .belowLeft => .belowLeft
  | .belowRight => .belowRight
  | .auto => .auto

/-- How the line of a `Shape.path` is drawn. -/
inductive Stroke where
  /-- A solid line. -/
  | solid
  /-- A dashed line. -/
  | dashed
  /-- Two parallel lines `gap` apart (world length), as for an equality in a diagram. -/
  | double (gap : Rat)
  deriving DecidableEq, Repr, Inhabited

/-- An exact shape. -/
inductive Shape where
  /-- A point, drawn as a marker. -/
  | dot (p : QPoint)
  /-- The segment from `p` to `q`. -/
  | segment (p q : QPoint)
  /-- The segment from `p` to `q` with an arrowhead towards `q` (the drawing stops short of `q`
  by the diagram's `arrowGap`, so that the head is not hidden under a marker at `q`). -/
  | arrow (p q : QPoint)
  /-- The open polyline through the points. -/
  | polyline (ps : List QPoint)
  /-- The closed axis-parallel rectangle with lower-left corner `lo` and upper-right corner
  `hi`. -/
  | rect (lo hi : QPoint)
  /-- The circle with centre `c` and radius `r`. -/
  | circle (c : QPoint) (r : Rat)
  /-- The text `s` at `p`, on the side `side` of it. -/
  | text (s : String) (p : QPoint) (side : Side)
  /-- The open polyline through the points, drawn with the stroke `stroke`: the body of an arrow
  of a diagram (its tip and tail are other shapes of the same part). -/
  | path (ps : List QPoint) (stroke : Stroke)
  deriving DecidableEq, Repr, Inhabited

/-- How a mark is coloured, by the house style's roles (`Style.plane`). -/
inductive Ink where
  /-- The ink. -/
  | ink
  /-- The faint ink (guides, secondary lines). -/
  | faint
  /-- Accent `k` (0, 1, 2), its outline only. -/
  | accent (k : Nat)
  /-- Accent `k` with a tinted inside (a rectangle or circle). -/
  | tint (k : Nat)
  /-- Colour `k` of the twelve series colours (`seriesRole`), with a tinted inside when
  `tinted`: a colour per element of a group, per generator, per residue. -/
  | series (k : Nat) (tinted : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- Whether an ink is one of the series colours. -/
def Ink.isSeries : Ink → Bool
  | .series .. => true
  | _ => false

/-- A mark: the part it depicts, its exact shape and its ink. -/
structure Mark where
  /-- What the mark depicts. -/
  part : Part
  /-- Its shape, in exact coordinates. -/
  shape : Shape
  /-- Its colour role. -/
  ink : Ink := .ink
  deriving DecidableEq, Repr, Inhabited

/-- A diagram: marks drawn in order (later ones on top) with a page width, a style and a title. -/
structure Diagram where
  /-- The marks. -/
  marks : List Mark
  /-- The title (the figure's accessible name). -/
  title : String := ""
  /-- A description of what is drawn. -/
  description : String := ""
  /-- The page width in pixels. -/
  width : Float := 360
  /-- The style (light by default; `Style.dark` for the dark rendition). -/
  style : Style := {}
  /-- The world length by which an arrow stops short of its head's point. -/
  arrowGap : Float := 0.12
  /-- A second, narrower width for small screens. -/
  narrowWidth : Option Float := none
  deriving Inhabited

/-- The most marks a diagram is drawn with: the builders of the kinds refuse data whose drawing
would have more (each kind states its own cap on the data, below this). -/
def maxMarks : Nat := 20000

/-- Mapping every element to nothing leaves nothing (a lemma for the read-backs). -/
@[simp] theorem filterMap_none {α β : Type} (l : List α) :
    l.filterMap (fun _ => (none : Option β)) = [] := by
  induction l <;> simp_all

namespace Diagram

/-- The parts the diagram depicts, in the order of its marks. -/
def parts (d : Diagram) : List Part := d.marks.map (·.part)

/-- The edges the diagram draws, `(i, j)` for each mark of the part `edge i j`, in order. -/
def edges (d : Diagram) : List (Nat × Nat) :=
  d.marks.filterMap fun m => match m.part with
    | .edge i j => some (i, j)
    | _ => none

/-- The vertices the diagram draws, `i` for each mark of the part `vertex i` that is a dot. -/
def vertices (d : Diagram) : List Nat :=
  d.marks.filterMap fun m => match m.part, m.shape with
    | .vertex i, .dot _ => some i
    | _, _ => none

/-- The cells the diagram draws, `(i, j)` for each mark of the part `cell i j`, in order. -/
def cells (d : Diagram) : List (Nat × Nat) :=
  d.marks.filterMap fun m => match m.part with
    | .cell i j => some (i, j)
    | _ => none

/-- The entries the diagram writes: `((i, j), s)` for each mark of the part `entry i j` that is
the text `s`, in order. -/
def entries (d : Diagram) : List ((Nat × Nat) × String) :=
  d.marks.filterMap fun m => match m.part, m.shape with
    | .entry i j, .text s _ _ => some ((i, j), s)
    | _, _ => none

/-- The steps the diagram draws: `(k, p, q)` for each mark of the part `step k` that is the
segment from `p` to `q`, in order. -/
def steps (d : Diagram) : List (Nat × QPoint × QPoint) :=
  d.marks.filterMap fun m => match m.part, m.shape with
    | .step k, .segment p q => some (k, p, q)
    | _, _ => none

/-- The decorations the diagram draws: `(part, shape)` for each mark whose part is a `guide` or a
`note` (a part that depicts nothing of the object), in order. A kind's `Faithful` requires them to
be exactly the builder's, so that nothing is drawn under a decoration's part. -/
def decorations (d : Diagram) : List (Part × Shape) :=
  d.marks.filterMap fun m => match m.part with
    | .guide => some (m.part, m.shape)
    | .note _ => some (m.part, m.shape)
    | _ => none

/-- The arrows the diagram draws: `(k, i, j)` for each mark of the part `arrow k i j` that is a
path (the body of the arrow; its tips, tail and label are other marks of the same part), in
order. -/
def arrows (d : Diagram) : List (Nat × Nat × Nat) :=
  d.marks.filterMap fun m => match m.part, m.shape with
    | .arrow k i j, .path _ _ => some (k, i, j)
    | _, _ => none

/-- The marks of the diagram whose part satisfies `p`, in order. -/
def marksWhere (d : Diagram) (p : Part → Bool) : List Mark := d.marks.filter fun m => p m.part

/-- The texts the diagram writes: `(part, s, p)` for each mark that is the text `s` at `p`, in
order. -/
def texts (d : Diagram) : List (Part × String × QPoint) :=
  d.marks.filterMap fun m => match m.shape with
    | .text s p _ => some (m.part, s, p)
    | _ => none

end Diagram

/-- The title a mark's item carries (its accessible name in SVG): the part in words. -/
def Part.title : Part → String
  | .vertex i => s!"vertex {i}"
  | .edge i j => s!"edge {i} → {j}"
  | .cell i j => s!"cell ({i}, {j})"
  | .entry i j => s!"entry ({i}, {j})"
  | .strand i => s!"strand {i}"
  | .set k => s!"set {k}"
  | .member x m => s!"element {x} in region {m}"
  | .step k => s!"step {k}"
  | .arrow k i j => s!"arrow {k}: {i} → {j}"
  | .twoCell k => s!"2-cell {k}"
  | .header a i => if a = 0 then s!"row {i}" else s!"column {i}"
  | .note _ => ""
  | .guide => ""

/-- The point `q` moved `gap` towards `p` (in floating point; `q` itself when the two are closer
than twice `gap`). -/
def shortened (p q : QPoint) (gap : Float) : Point :=
  let a := Exact.PlanePoint.toPoint p
  let b := Exact.PlanePoint.toPoint q
  let dx := b.x - a.x
  let dy := b.y - a.y
  let len := Float.sqrt (dx * dx + dy * dy)
  if len ≤ 2 * gap then b else ⟨b.x - dx * gap / len, b.y - dy * gap / len⟩

/-- The polyline through `ps` moved by `off` (in floating point), for a double stroke. -/
def offsetPolyline (ps : List QPoint) (off : Point) : Item :=
  Plane.polyline ((ps.map fun p => Exact.PlanePoint.toPoint p + off).toArray)

/-- The item of a path: a polyline, dashed, or two polylines `gap` apart (moved each way by half
the gap across the line from the first point to the last). -/
def Stroke.toItem (ps : List QPoint) : Stroke → Item
  | .solid => Exact.polyline ps
  | .dashed => (Exact.polyline ps).dashed #[6, 4]
  | .double gap =>
    let a := Exact.PlanePoint.toPoint (ps.headD (0, 0))
    let b := Exact.PlanePoint.toPoint (ps.getLastD (0, 0))
    let n := unitOf ⟨a.y - b.y, b.x - a.x⟩
    let h := Exact.toFloat gap / 2
    Plane.group #[offsetPolyline ps (h * n), offsetPolyline ps ((-h) * n)]

/-- The plane item of a shape, before its ink: the builders of `PILean.Exact.Plane` applied to
the exact points (a rectangle as the polygon of its four corners, counterclockwise from `lo`). -/
def Shape.toItem (gap : Float) : Shape → Item
  | .dot p => Exact.point p
  | .segment p q => Exact.segment p q
  | .arrow p q => Plane.arrow (Exact.PlanePoint.toPoint p) (shortened p q gap)
  | .polyline ps => Exact.polyline ps
  | .rect lo hi => Exact.polygon [lo, (hi.1, lo.2), hi, (lo.1, hi.2)]
  | .circle c r => Exact.circle c r
  | .text s p side => Exact.label s p side.toPlacement
  | .path ps st => st.toItem ps

/-- The opacity of the inside of a cell tinted in a series colour (stronger than the house tint,
so that a table's colours tell its elements apart). -/
def seriesFillOpacity : Float := 0.3

/-- The item with the ink's colour role: accents and the faint ink as tones, a tint as an accent
with a tinted inside. -/
def Ink.apply : Ink → Item → Item
  | .ink, it => it
  | .faint, it => it.faint
  | .accent k, it => it.accent k
  | .tint k, it => (it.accent k).filled
  | .series k false, it => it.role s!"series-{k % 12}"
  | .series k true, it =>
    ((it.role s!"series-{k % 12}").filled).fillOpacity seriesFillOpacity

/-- Series colour `k` (of twelve): a hue of the OKLCH circle, the twelve hues `30°` apart and
taken in steps of `150°` so that consecutive colours differ most, darker on light surfaces and
lighter on dark ones. -/
def seriesRole (k : Nat) : PlaneRole :=
  let h := ((k % 12) * 5 % 12).toFloat * 30 + 15
  { name := s!"series-{k % 12}", light := Rgba.ofOkLch ⟨0.5, 0.13, h⟩,
    dark := Rgba.ofOkLch ⟨0.76, 0.12, h⟩ }

/-- The style with the twelve series colours among its plane roles. -/
def withSeriesRoles (st : Style) : Style :=
  { st with plane := { st.plane with roles := st.plane.roles ++ (List.range 12).toArray.map seriesRole } }

/-- The titles of the circles among `marks` that pass exactly through `p`
(`(p - c)² = r²` in rational arithmetic), for the incidences a dot records. -/
def circlesThrough (marks : List Mark) (p : QPoint) : List String :=
  marks.filterMap fun m => match m.shape with
    | .circle c r =>
      if (p.1 - c.1) * (p.1 - c.1) + (p.2 - c.2) * (p.2 - c.2) = r * r && !m.part.title.isEmpty
      then some m.part.title else none
    | _ => none

/-- The plane item of a mark: its shape's item in its ink, named by its part (`Part.title`); a dot
records that it is on each of the `onCircles` (by title), which the layout checks of plane figures
require of a point drawn on a curve. -/
def Mark.toItem (gap : Float) (m : Mark) (onCircles : List String := []) : Item :=
  let it := m.ink.apply (m.shape.toItem gap)
  let it := onCircles.foldl (fun it t => it.incident .on t) it
  if m.part.title.isEmpty then it else it.named m.part.title

/-- The plane item of the mark `m` of the diagram's `marks`: a dot records the circles of the
diagram it lies on exactly (`circlesThrough`). -/
def Mark.toItemIn (gap : Float) (marks : List Mark) (m : Mark) : Item :=
  match m.shape with
  | .dot p => m.toItem gap (circlesThrough marks p)
  | _ => m.toItem gap

namespace Diagram

/-- The diagram as a plane figure: one item per mark, in order (`Mark.toItemIn`), with the
diagram's width, style and title. -/
def toPlane (d : Diagram) : Plane.Figure where
  items := (d.marks.map (Mark.toItemIn d.arrowGap d.marks)).toArray
  width := d.width
  style := if d.marks.any (·.ink.isSeries) then withSeriesRoles d.style else d.style
  info := { title := d.title, description := d.description }
  narrowWidth := d.narrowWidth

/-- The plane figure's items are the marks' items, in order. -/
theorem toPlane_items (d : Diagram) :
    d.toPlane.items = (d.marks.map (Mark.toItemIn d.arrowGap d.marks)).toArray := rfl

/-- The diagram `d ()` when `ok`, otherwise a diagram with the note `what` only: how a builder
refuses data beyond its caps, so that the work on hostile input stays bounded. The diagram is a
function of `Unit` so that it is not computed when `ok` is false. -/
def capped (ok : Bool) (what : String) (d : Unit → Diagram) : Diagram :=
  if ok then d () else { marks := [{ part := .note 0, shape := .text what (0, 0) .center }] }

/-- Within its caps a builder draws the diagram itself. -/
theorem capped_of {ok : Bool} (h : ok = true) (what : String) (d : Unit → Diagram) :
    capped ok what d = d () := by
  simp [capped, h]

/-- The diagram in the dark style. -/
def dark (d : Diagram) : Diagram := { d with style := Style.dark }

end Diagram

end PILean.Diagram
