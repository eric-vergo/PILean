/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plane.Draw

/-!
# Layout checks of plane figures

What a reader objects to in a fitted plane figure, reported as a list of problems (in the manner
of `PILean.Graph.Check`), measured on the page, in pixels:

* `labelOverlap`: two labels' boxes overlap by more than `labelTolerance` both ways.
* `labelOverItem`: a label's box meets the strokes of an element (a segment, a line, a circle's
  boundary, an arrowhead, …) or a point's marker that the label is not attached to. A label is
  attached only to the marker at its point (within `attachTolerance`): a label beside a point, or
  centred on it, keeps clear of every stroke, those through its point included.
* `outside`: a label, a marker or a stroke reaches beyond the page.
* `markersTooClose`: two markers come within `markerGap` of each other (or overlap), so that they
  read as one.
* `undecidedIncidence`: a point lies within `incidenceTolerance` of an element's strokes, so that a
  reader cannot see whether it is on it or on which side, and records no incidence relative to
  that element (`Item.incident`, which names the element by its title; `Plane.Exact.pointNearDisk`
  decides it exactly and records it). A point at one of the element's defining points (the end of
  a segment, a vertex, the end of an arc) is not reported.
* `unknownIncidenceTarget`: a point records an incidence relative to a title no element has, or
  one that several elements have.
* `degenerate`: a polygon with fewer than three distinct vertices (a regular polygon of a radius
  that is not positive has none), a polyline with fewer than two, or a segment or an arrow whose
  ends coincide: drawn as nothing or as a dot; and a circle, a disk, an arc, a sector, a region of
  disks or an angle mark with a radius that is zero, negative or not finite (`Geom.radiiOk`):
  drawn as nothing.
* `wrongIncidence`: a recorded incidence the drawing contradicts: a point recorded `on` an element
  more than `onTolerance` from its strokes, or recorded `inside` or `outside` a closed element
  (a circle, a disk, a sector, a polygon, a region of disks) on the other side of its boundary
  and more than `onTolerance` from it, or recorded `inside` or `outside` an element that encloses
  nothing.
* `lowContrast`: a colour an element uses, composited at its alpha over what it is drawn on, is
  below `textContrast` (labels) or `graphicContrast` (everything else) against that: the
  background with the fills of the earlier elements that enclose a region (a disk, a polygon, a
  sector, a region of disks; composited in sRGB) at the label's centre,
  at the marker's (the page itself for a marker with a halo), and at points along every stroke
  (the least contrast along it), in the figure's style and, for a figure in the default light
  colours, in its dark twin (`Style.dark`'s background, `PlaneStyle.dark`, and the dark colours of
  its roles).
* `nonFinite`: an element has a coordinate, radius, angle or pixel length that is not finite; it
  is drawn as nothing or as nonsense.
* `unknownRole`: an element's colour is a role (`Tone.role`) the style does not name, which is
  drawn in the ink.
* `darkThemeClash`: a page that shows the figure inline in its dark theme restyles each colour by
  its light value (`Style.darkColourPairs`, the first pairing of a light colour kept), and an
  element's colour would come out other than its dark twin's there: a fixed colour (`Tone.color`)
  that equals a colour of the style, or a role whose light colour another role or style colour
  shares with a different dark one.

The geometry of an element is that of its drawing (`drawGeom`): its paths flattened to within a
quarter pixel, so arcs, arrowheads and clipped lines are checked as drawn.

`Figure.autoPlaced` uses the same geometry to place the labels whose placement is `auto` (the eight
sides, `Placement.compass`) or `across` a line (either side of it): each in turn takes the least
offset, and at it the first side, where its box stays on the page, meets no other label and keeps
`labelClearance` pixels from everything it is not attached to (or, where no side gives that room,
merely meets nothing). `Figure.problems` checks the finished figure again.

## Main definitions

* `Leaf`, `Figure.leaves`, `CheckOptions`, `ProblemKind`, `Problem`.
* `Figure.problems`: the problems of a figure (after automatic placement).
* `Figure.autoPlaced`, `Figure.autoPlaced_of_noAuto`.
-/

namespace PILean.Plane

open Canvas

/-- An element of a figure with its look and metadata, as the checks see it (groups flattened, in
drawing order). -/
structure Leaf where
  /-- The element. -/
  geom : Geom
  /-- Its look. -/
  look : Look
  /-- Its metadata. -/
  info : ShapeInfo
  deriving Inhabited

/-- The elements of an item, in drawing order. -/
def Item.leaves : Item → Array Leaf
  | .shape g l i => #[⟨g, l, i⟩]
  | .group xs _ => xs.attach.flatMap fun ⟨x, _⟩ => x.leaves

/-- The elements of a figure, in drawing order; problems name them by their position here. -/
def Figure.leaves (fig : Figure) : Array Leaf := fig.items.flatMap Item.leaves

/-- The tolerances of the checks, in pixels, and the contrast thresholds. -/
structure CheckOptions where
  /-- Overlaps of labels up to this much (either way) are not reported. -/
  labelTolerance : Float := 0.5
  /-- Markers whose discs come closer than this read as one. -/
  markerGap : Float := 2
  /-- A point this near an element's strokes cannot be seen to be on it or off it. -/
  incidenceTolerance : Float := 2.5
  /-- A label is attached to a marker centred this near its point. -/
  attachTolerance : Float := 1.5
  /-- A point recorded on an element is at most this far from its strokes (the strokes are
  flattened to within a quarter pixel). -/
  onTolerance : Float := 0.5
  /-- The most points along one stroke at which its contrast is measured. -/
  strokeSamples : Nat := 48
  /-- The room an automatic label keeps from the strokes and markers it is not attached to, in
  pixels, when a side and an offset give it that room (`chooseAutoPlacements`). -/
  labelClearance : Float := 3
  /-- The least contrast of a label's colour against the background. -/
  textContrast : Float := 4.5
  /-- The least contrast of any other element's colour against the background. -/
  graphicContrast : Float := 3
  deriving Inhabited, Repr

/-- The kinds of problem (see the module docstring). -/
inductive ProblemKind where
  /-- Two labels overlap. -/
  | labelOverlap
  /-- A label meets an element or a marker it is not attached to. -/
  | labelOverItem
  /-- Something reaches beyond the page. -/
  | outside
  /-- Two markers read as one. -/
  | markersTooClose
  /-- A point is too near an element to be seen on it or off it, and records no incidence. -/
  | undecidedIncidence
  /-- A point records an incidence relative to a title no element has. -/
  | unknownIncidenceTarget
  /-- A recorded incidence that the drawing contradicts. -/
  | wrongIncidence
  /-- A colour has too little contrast against what it is drawn on. -/
  | lowContrast
  /-- An element has a number that is not finite. -/
  | nonFinite
  /-- An element's colour is a role the style does not name. -/
  | unknownRole
  /-- An element's colour comes out wrong in the dark theme of an inline picture. -/
  | darkThemeClash
  /-- A polygon, polyline, segment or arrow that encloses or spans nothing. -/
  | degenerate
  deriving BEq, Inhabited, Repr

/-- A problem: its kind, the positions of the elements involved (in `Figure.leaves`) and a
message. -/
structure Problem where
  /-- The kind. -/
  kind : ProblemKind
  /-- The elements involved, by position in `Figure.leaves`. -/
  items : Array Nat
  /-- What is wrong, in words. -/
  message : String
  deriving Inhabited, Repr

/-! ### Page geometry -/

/-- `c` (with its alpha) over the opaque `bg`, mixed in sRGB: what a browser shows for a
translucent fill, and what PILean's images of plane figures show. -/
def srgbOver (c bg : Rgba) : Rgba :=
  let a := c.a.toFloat / 255
  let mix := fun (x y : UInt8) => (a * x.toFloat + (1 - a) * y.toFloat).round.toUInt8
  ⟨mix c.r bg.r, mix c.g bg.g, mix c.b bg.b, 255⟩

/-- The distance from `q` to the segment from `a` to `b`. -/
def distToSegment (q a b : Point) : Float :=
  let d := b - a
  let n := d.x * d.x + d.y * d.y
  if n == 0 then (q - a).norm
  else
    let t := max 0 (min 1 (((q.x - a.x) * d.x + (q.y - a.y) * d.y) / n))
    (q - (a + t * d)).norm

/-- Whether the segment from `a` to `b` meets the box (Liang and Barsky on `t ∈ [0, 1]`). -/
def segmentMeetsBox (a b : Point) (box : Box) : Bool := Id.run do
  let d := b - a
  let mut t0 : Float := 0
  let mut t1 : Float := 1
  for (p, q) in [(-d.x, a.x - box.x0), (d.x, box.x1 - a.x), (-d.y, a.y - box.y0),
      (d.y, box.y1 - a.y)] do
    if p == 0 then
      if q < 0 then return false
    else
      let t := q / p
      if p < 0 then t0 := max t0 t else t1 := min t1 t
  return t0 ≤ t1

/-- Whether two boxes overlap by more than `tol` both across and down. -/
def boxesOverlap (a b : Box) (tol : Float) : Bool :=
  min a.x1 b.x1 - max a.x0 b.x0 > tol && min a.y1 b.y1 - max a.y0 b.y0 > tol

/-- The distance from `q` to the box (0 inside). -/
def distToBox (q : Point) (b : Box) : Float :=
  let dx := max 0 (max (b.x0 - q.x) (q.x - b.x1))
  let dy := max 0 (max (b.y0 - q.y) (q.y - b.y1))
  (dx * dx + dy * dy).sqrt

/-- The segments of a polyline, the closing one included for a closed polyline. -/
def polylineSegments (pl : Polyline) : Array (Point × Point) := Id.run do
  let mut out := #[]
  for i in [1:pl.points.size] do
    out := out.push (pl.points[i - 1]!, pl.points[i]!)
  if pl.closed && pl.points.size > 2 then out := out.push (pl.points.back!, pl.points[0]!)
  return out

/-- The page segments of an element's strokes, outlines and arrowheads: its drawn paths, flattened
to within a quarter pixel. Points and labels have none. -/
def strokeSegments (e : Env) (lf : Leaf) : Array (Point × Point) :=
  match lf.geom with
  | .point _ | .label .. => #[]
  | g => (drawGeom e lf.look g).flatMap fun s => match s with
    | .path p _ _ _ => (p.flatten 0.25).flatMap polylineSegments
    | _ => #[]

/-- The page centre and radius (ring included) of a point's marker. -/
def markerOf (e : Env) (lf : Leaf) : Option (Point × Float) :=
  match lf.geom with
  | .point p => some (e.frame.toScreen p, lf.look.size.getD e.ps.markerRadius + e.ps.markerRing)
  | _ => none

/-- The page box of a label and its point's page position. -/
def labelOf (e : Env) (lf : Leaf) : Option (Box × Point) :=
  match lf.geom with
  | .label s p place offset =>
    let size := lf.look.size.getD e.ps.labelSize
    let (b, _) := labelBox e.style s size (offset.getD e.ps.labelOffset) place
    let q := e.frame.toScreen p
    some (⟨q.x + b.x0, q.y + b.y0, q.x + b.x1, q.y + b.y1⟩, q)
  | _ => none

/-- The world points that define an element and that a point may coincide with without being an
undecided incidence: the ends of segments, lines, rays and arcs, vertices, a sector's centre. -/
def definingPoints : Geom → Array Point
  | .segment a b | .line a b | .ray a b | .arrow a b => #[a, b]
  | .polygon vs | .polyline vs => vs
  | .arc c r θ₀ θ₁ => #[c + polar r θ₀, c + polar r θ₁]
  | .sector c r θ₀ θ₁ => #[c, c + polar r θ₀, c + polar r θ₁]
  | .angleMark c .. => #[c]
  | _ => #[]

/-- How an element is named in a message: its title, or what it is and its position. -/
def Leaf.name (lf : Leaf) (i : Nat) : String :=
  if !lf.info.title.isEmpty then s!"“{lf.info.title}” (element {i})"
  else match lf.geom with
    | .label s .. => s!"label “{s}” (element {i})"
    | .point _ => s!"point (element {i})"
    | .segment .. => s!"segment (element {i})"
    | .line .. => s!"line (element {i})"
    | .ray .. => s!"ray (element {i})"
    | .arrow .. => s!"arrow (element {i})"
    | .circle .. => s!"circle (element {i})"
    | .disk .. => s!"disk (element {i})"
    | .arc .. => s!"arc (element {i})"
    | .sector .. => s!"sector (element {i})"
    | .polygon .. => s!"polygon (element {i})"
    | .polyline .. => s!"polyline (element {i})"
    | .angleMark .. => s!"angle mark (element {i})"
    | .tick .. => s!"tick (element {i})"
    | .disks .. => s!"region (element {i})"

/-- The least distance from `q` to a set of segments (a very large number for none). -/
def distToSegments (q : Point) (segs : Array (Point × Point)) : Float :=
  segs.foldl (fun m (a, b) => min m (distToSegment q a b)) 1e300

/-- Whether a label box meets an element or marker: a stroke through the box, or a marker disc
reaching into it. -/
def boxMeets (box : Box) (segs : Array (Point × Point)) (marker : Option (Point × Float)) :
    Bool :=
  segs.any (fun (a, b) => segmentMeetsBox a b box) ||
    (marker.any fun (c, r) => distToBox c box < r)

/-- Whether a label at page point `q` is attached to an element: the element is a marker centred
within `tol` of `q` (the label names the point). A label is attached to no stroke, so it must keep
clear of the segments and curves through its point. -/
def attachedTo (q : Point) (marker : Option (Point × Float)) (tol : Float) : Bool :=
  marker.any fun (c, _) => (c - q).norm ≤ tol

/-! ### The checks -/

/-- Whether the page point `q` is inside a closed polyline (even-odd). -/
def insidePolyline (q : Point) (pl : Polyline) : Bool := Id.run do
  let ps := pl.points
  let mut inside := false
  for i in [0:ps.size] do
    let a := ps[i]!
    let b := ps[(i + 1) % ps.size]!
    if (a.y > q.y) != (b.y > q.y) then
      let x := a.x + (q.y - a.y) * (b.x - a.x) / (b.y - a.y)
      if q.x < x then inside := !inside
  return inside

/-- Whether the page point `q` is inside a set of closed polylines (even-odd over all of them). -/
def insidePolylines (q : Point) (pls : Array Polyline) : Bool :=
  pls.foldl (fun b pl => if insidePolyline q pl then !b else b) false

/-- Whether an element encloses a region whose inside and outside a point can be on: a circle, a
disk, a sector, a polygon or a region of disks. -/
def Geom.encloses : Geom → Bool
  | .circle .. | .disk .. | .sector .. | .polygon .. | .disks .. => true
  | _ => false

/-- The fills an element that encloses a region (`Geom.encloses`) lays on the page: each filled
path of its drawing, flattened, with its colour (translucent or not); none for other elements
(markers, labels, arrowheads), which other elements are not drawn on. -/
def tintsOf (e : Env) (lf : Leaf) : Array (Array Polyline × Rgba) :=
  if !lf.geom.encloses then #[]
  else (drawGeom e lf.look lf.geom).filterMap fun s => match s with
    | .path p (some (.solid c)) _ _ => some (p.flatten 0.25, c)
    | _ => none

/-- What an element lies on at the page point `q`: the background with the tints `layers` (of the
earlier elements, in drawing order) whose filled outline holds `q`, composited in sRGB (the colour
browsers and PILean's images of plane figures show there). -/
def backgroundOver (bg : Rgba) (layers : Array (Array (Array Polyline × Rgba))) (q : Point) :
    Rgba :=
  layers.foldl (init := bg) fun bg ts =>
    ts.foldl (init := bg) fun bg (pls, c) => if insidePolylines q pls then srgbOver c bg else bg

/-- The tints an element lies on at the page point `q`: `backgroundOver` the tints of the
elements `before`. -/
def backgroundAt (e : Env) (before : Array Leaf) (q : Point) : Rgba :=
  backgroundOver e.style.background (before.map (tintsOf e)) q

/-- The styles a figure's colours are checked in: its own, and its dark twin when it has the
default light colours (named for the messages). -/
def checkedStyles (st : Style) : Array (String × Style) :=
  let twin := st.plane.sameColours PlaneStyle.light && st.background == Style.light.background
  let dark : Style :=
    { st with background := Style.dark.background, plane := st.plane.withColoursOf PlaneStyle.dark }
  #[("its style", st)] ++ (if twin then #[("the dark twin", dark)] else #[])

/-- Whether a look's own numbers (stroke width, size, tint opacity, dashes) are finite. -/
def Look.finite (l : Look) : Bool :=
  l.width.all Float.isFinite && l.size.all Float.isFinite && l.fillOpacity.all Float.isFinite &&
    l.weight.all Float.isFinite && l.dash.all Float.isFinite

/-- The closed page polylines that bound an element's region (`Geom.encloses`): its drawn paths,
flattened. -/
def regionPolylines (e : Env) (lf : Leaf) : Array Polyline :=
  (drawGeom e lf.look lf.geom).flatMap fun s => match s with
    | .path p _ _ _ => p.flatten 0.25
    | _ => #[]

/-- At most `n` points spread evenly along a stroke's segments (their midpoints). -/
def strokeSamplePoints (segs : Array (Point × Point)) (n : Nat) : Array Point :=
  let m := segs.size
  if m == 0 || n == 0 then #[]
  else
    let step := max 1 ((m + n - 1) / n)
    ((List.range ((m + step - 1) / step)).toArray.map fun k =>
      let (a, b) := segs[k * step]!
      a.mid b)

/-- The roles a look names that the style does not. -/
def Look.unknownRoles (ps : PlaneStyle) (l : Look) : Array String :=
  let named := fun (t : Tone) => match t with
    | .role n => if (ps.role? n).isSome then #[] else #[n]
    | _ => #[]
  named l.tone ++ (match l.fill with | some t => named t | none => #[])

/-- The problems of a figure as it is laid out (no automatic placement; see `Figure.problems`). -/
def problemsOf (fig : Figure) (o : CheckOptions := {}) : Array Problem := Id.run do
  let e := fig.env
  let leaves := fig.leaves
  let segs := leaves.map (strokeSegments e)
  let markers := leaves.map (markerOf e)
  let labels := leaves.map (labelOf e)
  let page : Box := ⟨-0.5, -0.5, e.frame.width + 0.5, e.frame.height + 0.5⟩
  let mut out : Array Problem := #[]
  let n := leaves.size
  -- numbers that are not finite, and roles the style does not name
  for i in [0:n] do
    let lf := leaves[i]!
    if !(lf.geom.finite && lf.look.finite) then
      out := out.push ⟨.nonFinite, #[i], s!"{lf.name i} has a number that is not finite and is \
        not drawn as given"⟩
    let distinct := fun (vs : Array Point) =>
      (vs.foldl (fun acc v => if acc.contains v then acc else acc.push v) #[]).size
    let degenerate : Bool := match lf.geom with
      | .polygon vs => distinct vs < 3
      | .polyline vs => distinct vs < 2
      | .segment a b | .arrow a b => a == b
      | _ => false
    if degenerate then
      out := out.push ⟨.degenerate, #[i], s!"{lf.name i} has too few distinct points to be \
        drawn as it is meant"⟩
    if !lf.geom.radiiOk then
      out := out.push ⟨.degenerate, #[i], s!"{lf.name i} has a radius that is zero, negative \
        or not finite, and is drawn as nothing"⟩
    for r in lf.look.unknownRoles e.ps do
      out := out.push ⟨.unknownRole, #[i], s!"{lf.name i} is in the role “{r}”, which the style \
        does not name; it is drawn in the ink"⟩
  -- colours the dark theme of an inline picture would restyle wrongly
  let pairs := fig.style.darkColourPairs
  if let some twin := fig.style.darkTwin? then
    for i in [0:n] do
      let lf := leaves[i]!
      for t in #[lf.look.tone] ++ (match lf.look.fill with | some t => #[t] | none => #[]) do
        let light := (t.resolve e.ps).rgbHex
        let dark := (match t with | .color c => c | _ => t.resolve twin.plane).rgbHex
        if let some (_, shown) := pairs.find? (·.1 == light) then
          if shown != dark then
            out := out.push ⟨.darkThemeClash, #[i], s!"{lf.name i}: its colour {light} comes \
              out {shown} in the dark theme of an inline picture, which restyles colours by \
              their light value, where its dark twin has {dark}; give it a colour of its own"⟩
  -- labels against labels and against everything else
  for i in [0:n] do
    let some (bi, qi) := labels[i]! | continue
    for j in [i + 1:n] do
      if let some (bj, _) := labels[j]! then
        if boxesOverlap bi bj o.labelTolerance then
          out := out.push ⟨.labelOverlap, #[i, j],
            s!"{leaves[i]!.name i} overlaps {leaves[j]!.name j}"⟩
    for j in [0:n] do
      if j == i || (labels[j]!).isSome then continue
      if boxMeets bi segs[j]! markers[j]! && !attachedTo qi markers[j]! o.attachTolerance then
        out := out.push ⟨.labelOverItem, #[i, j],
          s!"{leaves[i]!.name i} lies over {leaves[j]!.name j}"⟩
  -- the page
  for i in [0:n] do
    let w := (leaves[i]!.look.width.getD e.ps.lineWidth) / 2
    let outLabel := match labels[i]! with
      | some (b, _) => b.x0 < page.x0 || b.y0 < page.y0 || b.x1 > page.x1 || b.y1 > page.y1
      | none => false
    let outMarker := match markers[i]! with
      | some (c, r) => c.x - r < page.x0 || c.y - r < page.y0 || c.x + r > page.x1 ||
          c.y + r > page.y1
      | none => false
    let outStroke := segs[i]!.any fun (a, b) => [a, b].any fun q =>
      q.x < page.x0 - w || q.y < page.y0 - w || q.x > page.x1 + w || q.y > page.y1 + w
    if outLabel || outMarker || outStroke then
      out := out.push ⟨.outside, #[i], s!"{leaves[i]!.name i} reaches beyond the page"⟩
  -- markers
  for i in [0:n] do
    let some (ci, ri) := markers[i]! | continue
    for j in [i + 1:n] do
      if let some (cj, rj) := markers[j]! then
        let d := (ci - cj).norm
        if d < ri + rj + o.markerGap then
          out := out.push ⟨.markersTooClose, #[i, j],
            s!"{leaves[i]!.name i} and {leaves[j]!.name j} are {d} pixels apart and read as one"⟩
  -- incidences: each record held to the elements it names, and every near element recorded
  for i in [0:n] do
    let some (ci, _) := markers[i]! | continue
    let recs := leaves[i]!.look.incidences
    for (rel, what) in recs do
      let targets := (List.range n).filter fun j => j != i && leaves[j]!.info.title == what
      if targets.isEmpty then
        out := out.push ⟨.unknownIncidenceTarget, #[i], s!"{leaves[i]!.name i} is recorded \
          {rel.text} “{what}”, but no element has that title (Item.named)"⟩
      if targets.length > 1 then
        out := out.push ⟨.unknownIncidenceTarget, #[i] ++ targets.toArray, s!"{leaves[i]!.name i} \
          is recorded {rel.text} “{what}”, but {targets.length} elements have that title"⟩
      for j in (if targets.length == 1 then targets else []) do
        let d := distToSegments ci segs[j]!
        let lj := leaves[j]!
        let wrong : Option String := match rel with
          | .on =>
            if segs[j]!.isEmpty then some "which has no strokes to be on"
            else if d > o.onTolerance then some s!"but is {d} pixels from it"
            else none
          | .inside | .outside =>
            if !lj.geom.encloses then some "which encloses nothing"
            else if d ≤ o.onTolerance then none
            else
              let ins := insidePolylines ci (regionPolylines e lj)
              if ins == (rel == .inside) then none
              else some s!"but is drawn {if ins then "inside" else "outside"} it, {d} pixels \
                from its boundary"
        if let some why := wrong then
          out := out.push ⟨.wrongIncidence, #[i, j],
            s!"{leaves[i]!.name i} is recorded {rel.text} {lj.name j}, {why}"⟩
    for j in [0:n] do
      if j == i || segs[j]!.isEmpty then continue
      if recs.any fun (_, what) => leaves[j]!.info.title == what then continue
      let atDefining := (definingPoints leaves[j]!.geom).any fun p =>
        (e.frame.toScreen p - ci).norm ≤ 0.5
      if atDefining then continue
      let d := distToSegments ci segs[j]!
      if d ≤ o.incidenceTolerance then
        out := out.push ⟨.undecidedIncidence, #[i, j],
          s!"{leaves[i]!.name i} is {d} pixels from {leaves[j]!.name j}: a reader cannot see \
            whether it is on it; record where it is (Item.incident)"⟩
  -- contrast, against what each element is drawn on
  let mut seen : Array (String × String) := #[]
  for (themeName, st) in checkedStyles fig.style do
    let et : Env := { e with style := st }
    let layers := leaves.map (tintsOf et)
    for i in [0:n] do
      let lf := leaves[i]!
      let c := lf.look.tone.resolve st.plane
      let isText := (labels[i]!).isSome
      let need := if isText then o.textContrast else o.graphicContrast
      let spots : Array Point := match labels[i]!, markers[i]! with
        | some (b, _), _ => #[⟨(b.x0 + b.x1) / 2, (b.y0 + b.y1) / 2⟩]
        | none, some (q, _) => if lf.look.halo then #[] else #[q]
        | none, none => strokeSamplePoints segs[i]! o.strokeSamples
      let unders : Array Rgba :=
        if spots.isEmpty then #[st.background]
        else spots.map (backgroundOver st.background (layers.extract 0 i))
      -- the least contrast of the colour, at its alpha, against what it lies on
      let (r, under) := unders.foldl (init := ((1e300 : Float), st.background)) fun (m, u) bg =>
        let x := contrast (srgbOver c bg) bg
        if x < m then (x, bg) else (m, u)
      let key := (Svg.rgbHex c ++ toString c.a ++ Svg.rgbHex under ++ (if isText then "t" else "g"),
        themeName)
      if r < need && !seen.contains key then
        seen := seen.push key
        let alpha := if c.a == 255 then "" else s!" at opacity {c.a.toNat.toFloat / 255}"
        out := out.push ⟨.lowContrast, #[i],
          s!"{lf.name i}: the colour {Svg.rgbHex c}{alpha} has contrast {r} against \
            {Svg.rgbHex under}, what it is drawn on in {themeName}, below {need}"⟩
  return out

/-! ### Automatic placement of labels -/

/-- Whether an element is a label placed `auto` or `across`. -/
def Leaf.isAuto (lf : Leaf) : Bool :=
  match lf.geom with
  | .label _ _ .auto _ | .label _ _ (.across _) _ => true
  | _ => false

/-- The sides an automatic placement tries, in order. -/
def Placement.candidates : Placement → Array Placement
  | .auto => Placement.compass
  | .across θ => #[.toward (θ + pi / 2), .toward (θ - pi / 2)]
  | p => #[p]

/-- The item with its automatic labels' placements and offsets replaced, in drawing order, by
those of the list (one left over when the list runs out keeps its own). -/
def Item.replaceAuto : Item → StateM (List (Placement × Float)) Item
  | .shape (.label s p pl off) l i => do
    if pl == .auto || (match pl with | .across _ => true | _ => false) then
      match ← get with
      | (q, o) :: rest => set rest; pure (.shape (.label s p q (some o)) l i)
      | [] => pure (.shape (.label s p pl off) l i)
    else pure (.shape (.label s p pl off) l i)
  | .shape g l i => pure (.shape g l i)
  | .group xs i => do
    let ys ← xs.attach.mapM fun ⟨x, _⟩ => x.replaceAuto
    pure (.group ys i)

/-- How much farther than its own offset an automatic label may be pushed to clear (pixels). -/
def autoReach : Nat := 12

/-- The sides and offsets chosen for the automatic labels of `leaves` in the frame of `e`, in
drawing order: for each label in turn, the least offset (from its own, in whole pixels up to
`autoReach` more) and, at that offset, the first side (`Placement.candidates`) where its box stays
on the page and meets no other label, and keeps `labelClearance` pixels from everything it is not
attached to; failing that, the same with no room asked; the first side at its own offset when
none clears. -/
def chooseAutoPlacements (e : Env) (leaves : Array Leaf) (o : CheckOptions := {}) :
    List (Placement × Float) := Id.run do
  let segs := leaves.map (strokeSegments e)
  let markers := leaves.map (markerOf e)
  let page : Box := ⟨0, 0, e.frame.width, e.frame.height⟩
  let mut boxes : Array Box := #[]
  for i in [0:leaves.size] do
    if !leaves[i]!.isAuto then
      if let some (b, _) := labelOf e leaves[i]! then boxes := boxes.push b
  let mut chosen : Array (Placement × Float) := #[]
  for i in [0:leaves.size] do
    let lf := leaves[i]!
    let .label s p pl off := lf.geom | continue
    if !lf.isAuto then continue
    let cands := pl.candidates
    let base := off.getD e.ps.labelOffset
    let fits := fun (q : Placement) (d : Float) (room : Float) =>
      match labelOf e { lf with geom := .label s p q (some d) } with
      | none => false
      | some (b, at_) =>
        let wide : Box := ⟨b.x0 - room, b.y0 - room, b.x1 + room, b.y1 + room⟩
        b.x0 ≥ page.x0 && b.y0 ≥ page.y0 && b.x1 ≤ page.x1 && b.y1 ≤ page.y1 &&
          boxes.all (fun c => !boxesOverlap b c o.labelTolerance) &&
          (List.range leaves.size).all fun j =>
            (labelOf e leaves[j]!).isSome || !boxMeets wide segs[j]! markers[j]! ||
              attachedTo at_ markers[j]! o.attachTolerance
    let mut pick : Placement × Float := (cands[0]!, base)
    let mut found := false
    for room in [o.labelClearance, 0] do
      for k in [0:autoReach + 1] do
        if found then break
        for q in cands do
          if fits q (base + k.toFloat) room then
            pick := (q, base + k.toFloat)
            found := true
            break
    if let some (b, _) := labelOf e { lf with geom := .label s p pick.1 (some pick.2) } then
      boxes := boxes.push b
    chosen := chosen.push pick
  return chosen.toList

/-- The figure with every automatic label given a side and an offset (see `chooseAutoPlacements`),
chosen in the figure's frame and chosen again in the frame of the result (a label's box changes
the frame's scale); the figure itself when it has no automatic label. -/
def Figure.autoPlaced (fig : Figure) (o : CheckOptions := {}) : Figure :=
  if fig.leaves.all (!·.isAuto) then fig
  else
    let place := fun (env : Env) =>
      let picks := chooseAutoPlacements env fig.leaves o
      { fig with items := (fig.items.mapM Item.replaceAuto).run' picks }
    let first := place fig.env
    place first.env

/-- A figure without automatic labels is drawn as it is. -/
theorem Figure.autoPlaced_of_noAuto (fig : Figure) (o : CheckOptions)
    (h : fig.leaves.all (!·.isAuto) = true) : fig.autoPlaced o = fig := by
  simp [Figure.autoPlaced, h]

/-- The problems of a figure after its `auto` labels are placed. -/
def Figure.problems (fig : Figure) (o : CheckOptions := {}) : Array Problem :=
  problemsOf (fig.autoPlaced o) o

end PILean.Plane
