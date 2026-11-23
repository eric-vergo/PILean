/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Graph.Layout
import PILean.Graph.Channel

/-!
# Bundled orthogonal routes

The edges of a layered drawing drawn as horizontal and vertical segments in bundles of parallel
lanes (`Routing.bundled`), in the manner of well laid cable trays:

* **One entry and one exit port per node.** In the layers' frame (layers from the top down) an
  edge leaves its source at the middle of the source's lower side and enters its target at the
  middle of the target's upper side; the other directions are this frame turned or mirrored.
  The edges that leave a node share one vertical *stem* from the port, and each leaves it on its
  own track; the edges that enter a node join one stem, which ends in one arrowhead.
* **Channels and tracks.** Between two layers lies a channel; an edge that changes its position
  across the layers there does so on a horizontal run, on a track of its own height
  (`PILean.Graph.Channel`: vertical constraints, the nesting of the runs that turn the same way,
  doglegs, the left-edge rule). A channel is as high as its tracks need, and the layout makes
  room for it: the tracks are `laneGap` apart, the first and last `stemLength` and a corner from
  the boxes (and the arrowhead below).
* **Lanes.** A long edge runs through the layers between its ends as a straight vertical lane at
  the place of its dummy node, beside the nodes of those layers (the dummy nodes of a bundled
  layout stand `laneGap` apart, so the lanes of a bundle are parallel and evenly spaced); it
  never passes through a node, and through a cluster box only as the spline routes do.
* **Edges against the layers and self-loops** keep the port rule: such an edge leaves its source
  downwards, turns back up a corridor beside the source (room the layout keeps on the node's
  right), runs up the lanes of its dummy nodes, passes up a corridor beside its target, and comes
  down into the target's entry port.
* **Concentric corners.** Corners of the same turn whose centres can coincide (the corners of
  lanes that are `laneGap` apart turning onto tracks `laneGap` apart lie on one diagonal) form a
  bundle and are drawn as concentric quarter circles: the innermost with `radius`, the lane `k`
  places further out with `radius + k * laneGap`. A corner never takes more of a segment than it
  has: of a segment between two corners each takes at most its share in proportion to the radii
  they want, of one at a port at most its length less the stem (and the arrowhead); a bundle whose
  corners do not fit keeps them concentric with a smaller innermost radius when one of at least
  zero is enough, and is scaled as a whole otherwise.

Every route starts at its source's exit port, ends at its target's entry port and has only
horizontal and vertical segments (`routeWalk_head`, `routeWalk_last`, `routeWalk_axis`, proved
for the walk every route is made from). That no two edges share a segment outside the stems,
that no edge passes through a node, and the crossings, bends and lengths are tested
(`PILeanTest/GraphBundles.lean`).

Work: the legs of the routes are the sum of the spans of the edges; the channels cost `O(k²)` for
`k` runs in one channel (`placeRuns`); the corners are grouped by sorting, `O(c log c)` for `c`
corners.

## Main definitions

* `Move`, `walk`, `routeWalk`: routes as walks of horizontal and vertical moves.
* `Leg`, `BundleInput`, `BundleTracks`, `bundleTracks`: the legs of the routes and their tracks.
* `BundleGeometry`, `bundleRoutes`: the routes, their paths and the ports' stems and arrowheads.
-/

namespace PILean.Graph

/-- A move of a walk: vertically to a height, or horizontally to a position across. -/
inductive Move where
  /-- Vertically to the height `y`. -/
  | v (y : Float)
  /-- Horizontally to the position `x`. -/
  | h (x : Float)
  deriving Inhabited, Repr

/-- Where a move from `p` ends. -/
def Move.apply (p : Point) : Move → Point
  | .v y => ⟨p.x, y⟩
  | .h x => ⟨x, p.y⟩

/-- The points of a walk from `p` by the moves, `p` first. -/
def walk (p : Point) : List Move → List Point
  | [] => [p]
  | m :: ms => p :: walk (m.apply p) ms

/-- The walk of a route: from the exit port `start` by the moves, then across to the entry port
`finish` and down to it. -/
def routeWalk (start finish : Point) (ms : List Move) : List Point :=
  walk start (ms ++ [.h finish.x, .v finish.y])

/-- A walk starts where it starts from. -/
theorem walk_head (p : Point) (ms : List Move) : (walk p ms).head? = some p := by
  cases ms <;> rfl

/-- A walk has a point. -/
theorem walk_ne_nil (p : Point) (ms : List Move) : walk p ms ≠ [] := by
  cases ms <;> simp [walk]

/-- A walk that ends by moving across to `x` and then to the height `y` ends at `(x, y)`. -/
theorem walk_append_last (p : Point) (x y : Float) :
    ∀ ms : List Move, (walk p (ms ++ [.h x, .v y])).getLast? = some ⟨x, y⟩
  | [] => by simp [walk, Move.apply]
  | m :: ms => by
    simp only [List.cons_append, walk]
    rw [List.getLast?_cons, walk_append_last (m.apply p) x y ms]
    rfl

/-- Two points of a walk in a row lie on one horizontal or vertical line. -/
def axisStep (a b : Point) : Prop := a.x = b.x ∨ a.y = b.y

/-- Every two points in a row of the list lie on one horizontal or vertical line. -/
def AxisChain : List Point → Prop
  | a :: b :: rest => axisStep a b ∧ AxisChain (b :: rest)
  | _ => True

/-- Every two points in a row of a walk lie on one horizontal or vertical line. -/
theorem walk_axis : ∀ (p : Point) (ms : List Move), AxisChain (walk p ms)
  | p, [] => by simp [walk, AxisChain]
  | p, m :: ms => by
    have ih := walk_axis (m.apply p) ms
    have step : axisStep p (m.apply p) := by cases m <;> simp [axisStep, Move.apply]
    cases ms with
    | nil => exact ⟨step, trivial⟩
    | cons m' ms' => exact ⟨step, ih⟩

/-- Every route starts at its exit port. -/
theorem routeWalk_head (start finish : Point) (ms : List Move) :
    (routeWalk start finish ms).head? = some start :=
  walk_head start _

/-- Every route ends at its entry port. -/
theorem routeWalk_last (start finish : Point) (ms : List Move) :
    (routeWalk start finish ms).getLast? = some finish :=
  walk_append_last start finish.x finish.y ms

/-- Every segment of a route is horizontal or vertical. -/
theorem routeWalk_axis (start finish : Point) (ms : List Move) :
    AxisChain (routeWalk start finish ms) :=
  walk_axis start _

/-- The points of a route without repeated points and without points inside a straight
segment: the same polyline with only its ends and its corners. -/
def simplifyRoute (pts : Array Point) : Array Point := Id.run do
  let mut out : Array Point := #[]
  for p in pts do
    if out.back? == some p then continue
    if out.size ≥ 2 then
      let a := out.getD (out.size - 2) ⟨0, 0⟩
      let b := out.getD (out.size - 1) ⟨0, 0⟩
      -- `b` lies on the line from `a` to `p` and between them
      let straight := (a.x == b.x && b.x == p.x &&
          ((a.y ≤ b.y && b.y ≤ p.y) || (a.y ≥ b.y && b.y ≥ p.y))) ||
        (a.y == b.y && b.y == p.y && ((a.x ≤ b.x && b.x ≤ p.x) || (a.x ≥ b.x && b.x ≥ p.x)))
      if straight then out := out.pop
    out := out.push p
  return out

/-- One leg of a route: its crossing of one channel (the channel `c` lies above layer `c`). -/
structure Leg where
  /-- The channel. -/
  channel : Nat
  /-- The run's ends, in the order of travel. -/
  run : RunSpec
  deriving Inhabited

/-- Whether a leg crosses its channel straight down or up, without a run. -/
def Leg.straight (l : Leg) : Bool :=
  l.run.start.reach != l.run.finish.reach && l.run.start.x == l.run.finish.x

/-- What the bundled routes need from the earlier phases of the layout, in the layers' frame
(first coordinate across the layers, second along them, layers from the top down). -/
structure BundleInput where
  /-- The number of real nodes. -/
  n : Nat
  /-- The number of layers. -/
  layers : Nat
  /-- The layer of every real and dummy node. -/
  layerAll : Array Nat
  /-- The centre of every real and dummy node across the layers. -/
  across : Array Float
  /-- The half breadth of the box of every real node. -/
  half : Array Float
  /-- For every valid edge, its chain of nodes from the upper end to the lower (empty for a
  self-loop). -/
  chains : Array (Array Nat)
  /-- For every valid edge, whether it runs against the layers. -/
  reversed : Array Bool
  /-- For every valid edge, its source and its target. -/
  ends : Array (Nat × Nat)
  /-- The look. -/
  style : BundleStyle

/-- The corridor beside a node: its position across the layers, `k` lanes to the right of the
node's box. -/
def BundleInput.corridor (b : BundleInput) (v k : Nat) : Float :=
  b.across.getD v 0 + b.half.getD v 0 + b.style.laneGap * (k + 1).toFloat

/-- How many corridors every real node needs: one for each self-loop at it and for each end of
an edge against the layers. -/
def corridorUses (n : Nat) (ends : Array (Nat × Nat)) (reversed : Array Bool) : Array Nat :=
  Id.run do
  let mut uses : Array Nat := Array.replicate n 0
  for (s, t) in ends, r in reversed do
    if s == t then uses := uses.modify s (· + 1)
    else if r then
      uses := uses.modify s (· + 1)
      uses := uses.modify t (· + 1)
  return uses

/-- The legs of every route, in the order of travel (see the module docstring for their
shapes). Pieces: the end below node `v` (real or dummy) belongs to `2 v`, the end above it to
`2 v + 1`; the corridors take numbers from twice the number of real and dummy nodes on, two
each, and a node's corridors are numbered in the order of the edges. -/
def bundleLegs (b : BundleInput) : Array (Array Leg) := Id.run do
  let size := b.layerAll.size
  let lay := fun (v : Nat) => b.layerAll.getD v 0
  let xs := fun (v : Nat) => b.across.getD v 0
  let below := fun (v : Nat) => ({ x := xs v, reach := .up, piece := some (2 * v) } : RunEnd)
  let above := fun (v : Nat) =>
    ({ x := xs v, reach := .down, piece := some (2 * v + 1) } : RunEnd)
  let mut used : Array Nat := Array.replicate b.n 0
  let mut nextCorridor := 2 * size
  let mut out : Array (Array Leg) := #[]
  for c in b.chains, (s, t) in b.ends, r in b.reversed do
    -- a corridor beside a node: its ends below and above the node's layer
    let take := fun (used : Array Nat) (nextCorridor : Nat) (v : Nat) =>
      let k := used.getD v 0
      let x := b.corridor v k
      ((used.modify v (· + 1)), nextCorridor + 2,
        ({ x, reach := .up, piece := some nextCorridor } : RunEnd),
        ({ x, reach := .down, piece := some (nextCorridor + 1) } : RunEnd))
    if s == t then
      let (u', nc, cUp, cDown) := take used nextCorridor s
      used := u'; nextCorridor := nc
      out := out.push #[{ channel := lay s + 1, run := ⟨below s, cUp⟩ },
        { channel := lay s, run := ⟨cDown, above s⟩ }]
    else if c.size < 2 then out := out.push #[]
    else if !r then
      out := out.push <| (Array.range (c.size - 1)).map fun j =>
        let u := c.getD j 0
        let w := c.getD (j + 1) 0
        { channel := lay u + 1, run := ⟨below u, above w⟩ }
    else
      -- from the source (the chain's lower end) up to the target (its upper end)
      let (u1, nc1, sUp, sDown) := take used nextCorridor s
      let (u2, nc2, tUp, tDown) := take u1 nc1 t
      used := u2; nextCorridor := nc2
      let m := c.size - 1
      let mut legs : Array Leg := #[{ channel := lay s + 1, run := ⟨below s, sUp⟩ }]
      for i in [0:m] do
        let j := m - i
        let v := c.getD j 0
        let w := c.getD (j - 1) 0
        let from_ := if j == m then sDown else above v
        let to := if j - 1 == 0 then tUp else below w
        legs := legs.push { channel := lay v, run := ⟨from_, to⟩ }
      legs := legs.push { channel := lay t, run := ⟨tDown, above t⟩ }
      out := out.push legs
  return out

/-- The tracks of the bundled routes: the legs of every route, where every leg was placed
(`none` for a straight one), and the number of tracks of every channel. -/
structure BundleTracks where
  /-- The legs of every route. -/
  legs : Array (Array Leg)
  /-- Where every leg was placed. -/
  placed : Array (Array (Option Placed))
  /-- The number of tracks of every channel (the channel `c` lies above layer `c`; there are
  one more channels than layers). -/
  depth : Array Nat

/-- The legs of the routes and their tracks, channel by channel (`placeRuns`). A straight leg
needs no run; another leg with the same two pieces (an edge that repeats it) gets one, split at
a free column. -/
def bundleTracks (b : BundleInput) : BundleTracks := Id.run do
  let legs := bundleLegs b
  let channels := b.layers + 1
  -- the runs and the blocked columns of every channel, with where each run came from
  let mut runs : Array (Array RunSpec) := Array.replicate channels #[]
  let mut from_ : Array (Array (Nat × Nat)) := Array.replicate channels #[]
  let mut blocked : Array (Array Float) := Array.replicate channels #[]
  let mut seen : Std.HashSet (Nat × Nat × Nat) := {}
  for ls in legs, k in [0:legs.size] do
    for l in ls, j in [0:ls.size] do
      let c := min l.channel (channels - 1)
      if l.straight then
        let key := (c, l.run.start.piece.getD 0, l.run.finish.piece.getD 0)
        if !seen.contains key then
          seen := seen.insert key
          blocked := blocked.modify c (·.push l.run.start.x)
          continue
      runs := runs.modify c (·.push l.run)
      from_ := from_.modify c (·.push (k, j))
  let mut placed : Array (Array (Option Placed)) := legs.map fun ls => ls.map fun _ => none
  let mut depth : Array Nat := Array.replicate channels 0
  for c in [0:channels] do
    let (ps, d) := placeRuns (runs.getD c #[]) b.style.laneGap b.style.trackGap
      (blocked.getD c #[]) b.style.maxRuns
    depth := depth.setIfInBounds c d
    for p in ps, (k, j) in from_.getD c #[] do
      placed := placed.modify k fun a => a.setIfInBounds j (some p)
  return { legs, placed, depth }

/-- The moves of a route through its legs: on a leg's track down or up to its height and across
to its finish (by its jog when it has one); nothing for a straight leg. `trackY c t` is the
height of track `t` of channel `c`. -/
def legMoves (legs : Array Leg) (placed : Array (Option Placed)) (trackY : Nat → Nat → Float) :
    List Move :=
  (legs.zip placed).toList.flatMap fun (l, p) =>
    match p with
    | none => []
    | some (.track t) => [.v (trackY l.channel t), .h l.run.finish.x]
    | some (.jog t₁ x t₂) =>
      [.v (trackY l.channel t₁), .h x, .v (trackY l.channel t₂), .h l.run.finish.x]

/-- A corner of a route: the point, the directions it arrives in and leaves in (unit vectors
along the axes). -/
structure Corner where
  /-- The corner point. -/
  at_ : Point
  /-- The direction it is reached in. -/
  inDir : Point
  /-- The direction it is left in. -/
  outDir : Point
  deriving Inhabited

/-- The unit vector along the axis from `a` to `b` (they lie on one horizontal or vertical
line). -/
def axisDir (a b : Point) : Point :=
  if (b.x - a.x).abs ≥ (b.y - a.y).abs then ⟨if b.x ≥ a.x then 1 else -1, 0⟩
  else ⟨0, if b.y ≥ a.y then 1 else -1⟩

/-- The corners of a simplified route, its inner points in order. -/
def routeCorners (pts : Array Point) : Array Corner :=
  (Array.range (pts.size - 2)).map fun i =>
    let a := pts.getD i ⟨0, 0⟩
    let b := pts.getD (i + 1) ⟨0, 0⟩
    let c := pts.getD (i + 2) ⟨0, 0⟩
    { at_ := b, inDir := axisDir a b, outDir := axisDir b c }

/-- The radius of every corner of every route (`corners`, by route): concentric within a bundle
and fitted to the segments, as the module docstring states. `room route i` is the length the
first (`i = 0`) or last segment of a route may give to its corner. -/
def cornerRadii (st : BundleStyle) (routes : Array (Array Point)) (corners : Array (Array Corner))
    (room : Nat → Bool → Float) : Array (Array Float) := Id.run do
  -- the bundles: corners of one turn on one diagonal, in steps of `laneGap` from the innermost
  let mut keyed : Array ((Int × Int × Int) × Float × Nat × Nat) := #[]
  for cs in corners, k in [0:corners.size] do
    for c in cs, i in [0:cs.size] do
      let s : Point := c.outDir - c.inDir
      let turn : Int :=
        (c.inDir.x + 2 * c.inDir.y + 4 * c.outDir.x + 8 * c.outDir.y).round.toInt64.toInt
      let diag : Int := (s.y * c.at_.x - s.x * c.at_.y).round.toInt64.toInt
      -- how far towards the inside of the turn: the innermost corner has the largest value
      let inward := s.x * c.at_.x
      keyed := keyed.push ((turn, diag, 0), inward, k, i)
  let sorted := keyed.qsort fun a b =>
    a.1.1 < b.1.1 || (a.1.1 == b.1.1 && (a.1.2.1 < b.1.2.1 ||
      (a.1.2.1 == b.1.2.1 && (a.2.1 > b.2.1 || (a.2.1 == b.2.1 && (a.2.2.1 < b.2.2.1 ||
        (a.2.2.1 == b.2.2.1 && a.2.2.2 < b.2.2.2)))))))
  let mut want : Array (Array Float) := corners.map fun cs => cs.map fun _ => st.radius
  let mut family : Array (Array Nat) := corners.map fun cs => cs.map fun _ => 0
  let mut families := 0
  let mut start := 0
  for j in [0:sorted.size] do
    let (key, inward, k, i) := sorted.getD j ((0, 0, 0), 0, 0, 0)
    if j > 0 then
      let (key', inward', _, _) := sorted.getD (j - 1) ((0, 0, 0), 0, 0, 0)
      if key' != key || ((inward' - inward) - st.laneGap).abs > 0.5 then
        start := j
        families := families + 1
    let (_, first, _, _) := sorted.getD start ((0, 0, 0), 0, 0, 0)
    want := want.modify k (·.setIfInBounds i (st.radius + (first - inward)))
    family := family.modify k (·.setIfInBounds i families)
  -- the most every corner may take: of a segment between two corners its share in proportion
  -- to the radii they want, of a segment at a port the room the port leaves
  let mut cap : Array (Array Float) := corners.map fun cs => cs.map fun _ => 0
  for pts in routes, k in [0:routes.size] do
    let ws := want.getD k #[]
    let m := ws.size
    for i in [0:m] do
      let r := ws.getD i 0
      let p := pts.getD (i + 1) ⟨0, 0⟩
      let before := (pts.getD i ⟨0, 0⟩).dist p
      let after := p.dist (pts.getD (i + 2) ⟨0, 0⟩)
      let share := fun (len other : Float) => if r + other ≤ 0 then 0 else len * r / (r + other)
      let capBefore := if i == 0 then max 0 (room k false) else share before (ws.getD (i - 1) 0)
      let capAfter := if i + 1 == m then max 0 (room k true) else share after (ws.getD (i + 1) 0)
      cap := cap.modify k (·.setIfInBounds i (min r (min capBefore capAfter)))
  -- a bundle keeps its corners concentric by a smaller innermost radius when that is enough, and
  -- is scaled as a whole when it is not
  let mut base : Array Float := Array.replicate (families + 1) st.radius
  let mut ratio : Array Float := Array.replicate (families + 1) 1
  for fs in family, k in [0:family.size] do
    for f in fs, i in [0:fs.size] do
      let w := (want.getD k #[]).getD i 0
      let c := (cap.getD k #[]).getD i 0
      base := base.modify f (min · (c - (w - st.radius)))
      if w > 0 then ratio := ratio.modify f (min · (c / w))
  return want.mapIdx fun k ws => ws.mapIdx fun i w =>
    let f := (family.getD k #[]).getD i 0
    let b := base.getD f 0
    if b ≥ 0 then b + (w - st.radius) else w * ratio.getD f 0

/-- The path along a route from `first` (a point on its first segment) to `last` (a point on its
last segment) through its corners, each rounded by its radius (a quarter circle as a cubic). -/
def roundedRoute (corners : Array Corner) (radii : Array Float) (first last : Point) : Path :=
  Id.run do
  let mut path := Path.empty.moveTo first
  let mut cur := first
  for c in corners, r in radii do
    if r < 0.25 then
      if cur != c.at_ then path := path.lineTo c.at_
      cur := c.at_
    else
      let a := c.at_ - r * c.inDir
      let b := c.at_ + r * c.outDir
      let k := Path.kappa * r
      if cur != a then path := path.lineTo a
      path := path.cubicTo (a + k * c.inDir) (b - k * c.outDir) b
      cur := b
  return if cur != last then path.lineTo last else path

/-- What the layout knows of the geometry when the routes are drawn, in the layers' frame. -/
structure BundleGeometry where
  /-- The height of track `t` of channel `c`. -/
  trackY : Nat → Nat → Float
  /-- The box of every real node. -/
  boxes : Array Box
  /-- The length of an arrowhead. -/
  arrowLength : Float
  /-- The half-width of an arrowhead. -/
  arrowHalfWidth : Float
  /-- For every valid edge, whether it has an arrowhead. -/
  arrows : Array Bool

/-- The routes of the edges (in the layers' frame, in the order of travel, simplified), the
paths each edge draws of its own, and the ports' stems and arrowheads. -/
def bundleRoutes (b : BundleInput) (tr : BundleTracks) (geo : BundleGeometry) :
    Array (Array Point) × Array Path × Array PortMark := Id.run do
  let st := b.style
  let m := b.ends.size
  let boxOf := fun (v : Nat) => geo.boxes.getD v ⟨0, 0, 0, 0⟩
  let exitPort := fun (v : Nat) => (⟨b.across.getD v 0, (boxOf v).y1⟩ : Point)
  let entryPort := fun (v : Nat) => (⟨b.across.getD v 0, (boxOf v).y0⟩ : Point)
  let routes : Array (Array Point) := (Array.range m).map fun k =>
    let (s, t) := b.ends.getD k (0, 0)
    let legs := tr.legs.getD k #[]
    if legs.isEmpty then #[exitPort s, entryPort t]
    else simplifyRoute (routeWalk (exitPort s) (entryPort t)
      (legMoves legs (tr.placed.getD k #[]) geo.trackY)).toArray
  -- how many edges use every port
  let mut outs : Array Nat := Array.replicate b.n 0
  let mut ins : Array Nat := Array.replicate b.n 0
  let mut headAt : Array Bool := Array.replicate b.n false
  for (s, t) in b.ends, a in geo.arrows do
    outs := outs.modify s (· + 1)
    ins := ins.modify t (· + 1)
    if a then headAt := headAt.setIfInBounds t true
  let cut := geo.arrowLength - 1
  let corners := routes.map routeCorners
  let room := fun (k : Nat) (atEnd : Bool) =>
    let pts := routes.getD k #[]
    if atEnd then
      let (_, t) := b.ends.getD k (0, 0)
      let last := (pts.getD (pts.size - 2) ⟨0, 0⟩).dist (pts.getD (pts.size - 1) ⟨0, 0⟩)
      last - st.stemLength - (if headAt.getD t false then geo.arrowLength else 0)
    else (pts.getD 0 ⟨0, 0⟩).dist (pts.getD 1 ⟨0, 0⟩) - st.stemLength
  let radii := cornerRadii st routes corners room
  -- whether an edge leaves its source's stem in the channel below it, or joins its target's stem
  -- in the channel above it
  let branches := fun (k : Nat) =>
    match (tr.placed.getD k #[])[0]? with
    | some (some _) => true
    | _ => false
  let joins := fun (k : Nat) =>
    let (_, t) := b.ends.getD k (0, 0)
    let legs := tr.legs.getD k #[]
    let ps := tr.placed.getD k #[]
    match legs.back?, ps.back? with
    | some l, some (some _) => l.channel == b.layerAll.getD t 0
    | _, _ => false
  -- the stems: from the exit port down to the last point where an edge leaves it, and from the
  -- first point where an edge joins it down to the arrowhead
  let mut exitEnd : Array (Option (Float × Float)) := Array.replicate b.n none
  let mut entryStart : Array (Option (Float × Float)) := Array.replicate b.n none
  for k in [0:m] do
    let (s, t) := b.ends.getD k (0, 0)
    let cs := corners.getD k #[]
    let rs := radii.getD k #[]
    if branches k && !cs.isEmpty then
      let c := cs.getD 0 default
      let y := c.at_.y - rs.getD 0 0
      exitEnd := exitEnd.modify s fun
        | none => some (y, c.at_.y)
        | some (a, b) => some (max a y, max b c.at_.y)
    if joins k && !cs.isEmpty then
      let c := cs.getD (cs.size - 1) default
      let y := c.at_.y + rs.getD (rs.size - 1) 0
      entryStart := entryStart.modify t fun
        | none => some (y, c.at_.y)
        | some (a, b) => some (min a y, min b c.at_.y)
  let paths : Array Path := (Array.range m).map fun k =>
    let (s, t) := b.ends.getD k (0, 0)
    let pts := routes.getD k #[]
    let cs := corners.getD k #[]
    let rs := radii.getD k #[]
    let p0 := pts.getD 0 ⟨0, 0⟩
    let pn := pts.getD (pts.size - 1) ⟨0, 0⟩
    -- where the edge's own path starts and ends
    let first : Point :=
      if outs.getD s 0 < 2 then p0
      else if branches k && !cs.isEmpty then
        let c := cs.getD 0 default
        c.at_ - rs.getD 0 0 * c.inDir
      else match exitEnd.getD s none with
        | some (y, _) => ⟨p0.x, y⟩
        | none => p0
    let last : Point :=
      if ins.getD t 0 < 2 then
        if headAt.getD t false then ⟨pn.x, pn.y - cut⟩ else pn
      else if joins k && !cs.isEmpty then
        let c := cs.getD (cs.size - 1) default
        c.at_ + rs.getD (rs.size - 1) 0 * c.outDir
      else match entryStart.getD t none with
        | some (y, _) => ⟨pn.x, y⟩
        | none => if headAt.getD t false then ⟨pn.x, pn.y - cut⟩ else pn
    roundedRoute cs rs first last
  -- the ports
  let mut ports : Array PortMark := #[]
  for v in [0:b.n] do
    let x := b.across.getD v 0
    if outs.getD v 0 ≥ 1 then
      let p := exitPort v
      match exitEnd.getD v none with
      | some (y, reach) =>
        if outs.getD v 0 ≥ 2 then
          let stem := (Path.empty.moveTo p).lineTo ⟨x, y⟩
          ports := ports.push { node := v, entry := false, stem := some stem,
                                trunk := (p, ⟨x, reach⟩) }
      | none => pure ()
    if ins.getD v 0 ≥ 1 then
      let p := entryPort v
      let base : Point := if headAt.getD v false then ⟨x, p.y - cut⟩ else p
      let head := if headAt.getD v false then
          some (arrowPath p ⟨0, 1⟩ geo.arrowLength geo.arrowHalfWidth) else none
      let (stem, trunk) : Option Path × (Point × Point) := match entryStart.getD v none with
        | some (y, reach) =>
          if ins.getD v 0 ≥ 2 then
            (some ((Path.empty.moveTo ⟨x, y⟩).lineTo base), (⟨x, reach⟩, p))
          else (none, (p, p))
        | none => (none, (p, p))
      if head.isSome || stem.isSome then
        ports := ports.push { node := v, entry := true, stem, head, trunk }
  return (routes, paths, ports)

end PILean.Graph
