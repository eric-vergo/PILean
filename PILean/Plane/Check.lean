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
  attached to the marker at its point, and, when it is centred on its point, to the strokes that
  pass within `attachTolerance` of it; a label beside a point keeps clear of the segments and
  curves through that point.
* `outside`: a label, a marker or a stroke reaches beyond the page.
* `markersTooClose`: two markers come within `markerGap` of each other (or overlap), so that they
  read as one.
* `undecidedIncidence`: a point lies within `incidenceTolerance` of an element's strokes, so that a
  reader cannot see whether it is on it or on which side, and its look records no incidence
  (`Item.incident`; `Plane.Exact.pointNearDisk` decides it exactly and records it). A point at one
  of the element's defining points (the end of a segment, a vertex, the end of an arc) is not
  reported.
* `lowContrast`: a colour an element uses is below `textContrast` (labels) or `graphicContrast`
  (everything else) against the background, in the figure's style and, for a figure in the default
  light colours, in its dark twin (`Style.dark`'s background and `PlaneStyle.dark`).

The geometry of an element is that of its drawing (`drawGeom`): its paths flattened to within a
quarter pixel, so arcs, arrowheads and clipped lines are checked as drawn.

`Figure.autoPlaced` uses the same geometry to place the labels whose placement is `auto`: each in
turn takes the first of the eight sides (`Placement.compass`) where its box stays on the page and
meets no other label and nothing it is not attached to.

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
  /-- A label is attached to what passes this near its point. -/
  attachTolerance : Float := 1.5
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
  /-- A colour has too little contrast against the background. -/
  | lowContrast
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
within `tol` of `q` (the label names the point), or the label is centred on its point (`centred`)
and the element's strokes pass within `tol` of it (a label set on a line on purpose). A label
beside a point is not attached to the segments and curves through that point, so it must keep
clear of them. -/
def attachedTo (q : Point) (centred : Bool) (segs : Array (Point × Point))
    (marker : Option (Point × Float)) (tol : Float) : Bool :=
  (centred && distToSegments q segs ≤ tol) || (marker.any fun (c, _) => (c - q).norm ≤ tol)

/-- Whether an element is a label centred on its point. -/
def Leaf.centred (lf : Leaf) : Bool :=
  match lf.geom with
  | .label _ _ .center _ => true
  | _ => false

/-! ### The checks -/

/-- The styles a figure's colours are checked in: its own, and its dark twin when it has the
default light colours (named for the messages). -/
def checkedStyles (st : Style) : Array (String × Style) :=
  let twin := st.plane.sameColours PlaneStyle.light && st.background == Style.light.background
  let dark : Style :=
    { st with background := Style.dark.background, plane := st.plane.withColoursOf PlaneStyle.dark }
  #[("its style", st)] ++ (if twin then #[("the dark twin", dark)] else #[])

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
      if boxMeets bi segs[j]! markers[j]! &&
          !attachedTo qi leaves[i]!.centred segs[j]! markers[j]! o.attachTolerance then
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
  -- incidences
  for i in [0:n] do
    let some (ci, _) := markers[i]! | continue
    if leaves[i]!.look.incidence.isSome then continue
    for j in [0:n] do
      if j == i || segs[j]!.isEmpty then continue
      let atDefining := (definingPoints leaves[j]!.geom).any fun p =>
        (e.frame.toScreen p - ci).norm ≤ 0.5
      if atDefining then continue
      let d := distToSegments ci segs[j]!
      if d ≤ o.incidenceTolerance then
        out := out.push ⟨.undecidedIncidence, #[i, j],
          s!"{leaves[i]!.name i} is {d} pixels from {leaves[j]!.name j}: a reader cannot see \
            whether it is on it; record where it is (Item.incident)"⟩
  -- contrast
  let mut seen : Array (String × String) := #[]
  for (themeName, st) in checkedStyles fig.style do
    for i in [0:n] do
      let lf := leaves[i]!
      let c := lf.look.tone.resolve st.plane
      let isText := (labels[i]!).isSome
      let need := if isText then o.textContrast else o.graphicContrast
      let r := contrast c st.background
      let key := (Svg.rgbHex c ++ (if isText then "t" else "g"), themeName)
      if r < need && !seen.contains key then
        seen := seen.push key
        out := out.push ⟨.lowContrast, #[i],
          s!"{lf.name i}: the colour {Svg.rgbHex c} has contrast {r} against the background in \
            {themeName}, below {need}"⟩
  return out

/-! ### Automatic placement of labels -/

/-- Whether an element is a label placed `auto`. -/
def Leaf.isAuto (lf : Leaf) : Bool :=
  match lf.geom with
  | .label _ _ .auto _ => true
  | _ => false

/-- The item with the placements of its `auto` labels replaced, in drawing order, by those of
the list (an `auto` label left over when the list runs out stays `auto`). -/
def Item.replaceAuto : Item → StateM (List Placement) Item
  | .shape (.label s p .auto off) l i => do
    match ← get with
    | pl :: rest => set rest; pure (.shape (.label s p pl off) l i)
    | [] => pure (.shape (.label s p .auto off) l i)
  | .shape g l i => pure (.shape g l i)
  | .group xs i => do
    let ys ← xs.attach.mapM fun ⟨x, _⟩ => x.replaceAuto
    pure (.group ys i)

/-- The placements chosen for the `auto` labels of a figure, in drawing order (see the module
docstring). -/
def chooseAutoPlacements (fig : Figure) (o : CheckOptions := {}) : List Placement := Id.run do
  let e := fig.env
  let leaves := fig.leaves
  let segs := leaves.map (strokeSegments e)
  let markers := leaves.map (markerOf e)
  let page : Box := ⟨0, 0, e.frame.width, e.frame.height⟩
  let mut boxes : Array Box := #[]
  for i in [0:leaves.size] do
    if !leaves[i]!.isAuto then
      if let some (b, _) := labelOf e leaves[i]! then boxes := boxes.push b
  let mut chosen : Array Placement := #[]
  for i in [0:leaves.size] do
    let lf := leaves[i]!
    let .label s p .auto off := lf.geom | continue
    let mut pick : Placement := .aboveRight
    for pl in Placement.compass do
      let some (b, q) := labelOf e { lf with geom := .label s p pl off } | continue
      let onPage := b.x0 ≥ page.x0 && b.y0 ≥ page.y0 && b.x1 ≤ page.x1 && b.y1 ≤ page.y1
      let clearOfLabels := boxes.all fun c => !boxesOverlap b c o.labelTolerance
      let clearOfItems := (List.range leaves.size).all fun j =>
        (labelOf e leaves[j]!).isSome ||
          !boxMeets b segs[j]! markers[j]! ||
            attachedTo q false segs[j]! markers[j]! o.attachTolerance
      if onPage && clearOfLabels && clearOfItems then
        pick := pl
        break
    if let some (b, _) := labelOf e { lf with geom := .label s p pick off } then
      boxes := boxes.push b
    chosen := chosen.push pick
  return chosen.toList

/-- The figure with every `auto` label given a side (see the module docstring); the figure itself
when it has no `auto` label. -/
def Figure.autoPlaced (fig : Figure) (o : CheckOptions := {}) : Figure :=
  if fig.leaves.all (!·.isAuto) then fig
  else
    let picks := chooseAutoPlacements fig o
    { fig with items := (fig.items.mapM Item.replaceAuto).run' picks }

/-- A figure without `auto` labels is drawn as it is. -/
theorem Figure.autoPlaced_of_noAuto (fig : Figure) (o : CheckOptions)
    (h : fig.leaves.all (!·.isAuto) = true) : fig.autoPlaced o = fig := by
  simp [Figure.autoPlaced, h]

/-- The problems of a figure after its `auto` labels are placed. -/
def Figure.problems (fig : Figure) (o : CheckOptions := {}) : Array Problem :=
  problemsOf (fig.autoPlaced o) o

end PILean.Plane
