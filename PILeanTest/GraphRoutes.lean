/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILeanTest.GraphQuality
import PILeanTest.GraphOrder

/-!
# Checks of the routes of edges and of the layers of graphs with clusters

* The shortest route (`tautRoute`): it passes every gate, bends only at ends of gates, and is no
  longer than the best route found by trying every whole position in every gate.
* The curve (`roundedPieces`, `fitPieces`): it starts and ends where the route does, turns as
  much as the route and never the other way, lies in the triangles of the route's bends, and
  stays in the zones it is given; the check `piecesFit` reports a curve that does not.
* The routes of whole layouts: no edge turns back across the layers, every arrowhead touches
  its node and points along its curve.
* Layers with clusters (`wrapLayers`, `levelLayers`, `nestedLayers`, `strays`): edges keep
  pointing down, a cluster that an edge joins to another lies wholly above or below it, and no
  edge passes through a cluster that holds neither of its ends.

Every check of a checker comes with a planted fault that the checker must report.
-/

namespace PILeanTest.GraphRoutes

open PILean PILean.Graph

/-- Where the polyline, whose heights increase, is at the height `y` (`none` outside it). -/
def crossingAt (pts : Array Point) (y : Float) : Option Float := Id.run do
  for j in [1:pts.size] do
    let a := pts.getD (j - 1) ⟨0, 0⟩
    let b := pts.getD j ⟨0, 0⟩
    if a.y ≤ y && y ≤ b.y then
      return some (if b.y == a.y then a.x else a.x + (y - a.y) / (b.y - a.y) * (b.x - a.x))
  return none

/-- Whether the polyline passes every gate. -/
def throughGates (pts : Array Point) (gates : Array Gate) : Bool :=
  gates.all fun g => match crossingAt pts g.y with
    | some x => g.lo - 1e-6 ≤ x && x ≤ g.hi + 1e-6
    | none => false

/-- The length of a polyline. -/
def polyLength (pts : Array Point) : Float :=
  (Array.range (pts.size - 1)).foldl (init := 0) fun s j =>
    s + (pts.getD j ⟨0, 0⟩).dist (pts.getD (j + 1) ⟨0, 0⟩)

/-- A start, `n` gates and an end from the generator at `seed`: the gates 40 apart in height,
each between 4 and 60 wide, anywhere within 300 of the start. -/
def randomGates (seed n : Nat) : Point × Array Gate × Point := Id.run do
  let (r, _) := GraphOrder.draws seed.toUInt64 (2 * n + 2) 300
  let gates := (Array.range n).map fun i =>
    let lo := (r.getD (2 * i) 0).toFloat
    ({ lo, hi := lo + 4 + ((r.getD (2 * i + 1) 0) % 57).toFloat, y := 40 * (i + 1).toFloat } : Gate)
  return (⟨(r.getD (2 * n) 0).toFloat, 0⟩, gates,
    ⟨(r.getD (2 * n + 1) 0).toFloat, 40 * (n + 1).toFloat⟩)

/-- The length of the shortest route through the gates among those that pass every gate at a
whole position (a search over all of them, gate by gate). -/
def gridShortest (start : Point) (gates : Array Gate) (finish : Point) : Float := Id.run do
  -- the best length to every position of the gate before
  let mut front : Array (Point × Float) := #[(start, 0)]
  for g in gates do
    let count := (g.hi - g.lo).floor.toUInt64.toNat + 1
    front := (Array.range count).map fun k =>
      let p : Point := ⟨g.lo + k.toFloat, g.y⟩
      (p, front.foldl (fun m (q, d) => min m (d + q.dist p)) 1e30)
  return front.foldl (fun m (q, d) => min m (d + q.dist finish)) 1e30

/-- Whether the shortest route through random gates passes them all, bends only at ends of
gates, and is no longer than the best route through whole positions. -/
def tautOk (seed : Nat) : Bool :=
  let (s, gates, t) := randomGates seed (2 + seed % 6)
  let pts := tautRoute s gates t
  pts.getD 0 ⟨-1, -1⟩ == s && pts.back? == some t && throughGates pts gates &&
    (pts.extract 1 (pts.size - 1)).all (fun p =>
      gates.any fun g => p.y == g.y && (p.x == g.lo || p.x == g.hi)) &&
    polyLength pts ≤ gridShortest s gates t + 1e-6 &&
    gridShortest s gates t ≤ polyLength pts + 0.05 * gates.size.toFloat

/-- The flattened curve of the pieces. -/
def flat (pieces : Array Piece) : Array Point :=
  ((piecesPath pieces).flatten 0.05).foldl (fun acc pl => acc ++ pl.points) #[]

/-- The sum of the angles by which a polyline turns. -/
def turning (pts : Array Point) : Float :=
  (GraphQuality.turns pts).foldl (fun s a => s + a.abs) 0

/-- A polyline of `n` points from the generator at `seed`, 30 to 90 apart in height. -/
def randomRoute (seed n : Nat) : Array Point := Id.run do
  let (r, _) := GraphOrder.draws seed.toUInt64 (2 * n) 400
  let mut y : Float := 0
  let mut out : Array Point := #[]
  for i in [0:n] do
    out := out.push ⟨(r.getD (2 * i) 0).toFloat, y⟩
    y := y + 30 + ((r.getD (2 * i + 1) 0) % 61).toFloat
  return out

/-- The distance from a point to a polyline. -/
def distanceTo (pts : Array Point) (p : Point) : Float :=
  (Array.range (pts.size - 1)).foldl (init := 1e30) fun m j =>
    let a := pts.getD j ⟨0, 0⟩
    let v := pts.getD (j + 1) ⟨0, 0⟩ - a
    let l2 := v.x * v.x + v.y * v.y
    let t := if l2 == 0 then 0 else max 0 (min 1 (((p.x - a.x) * v.x + (p.y - a.y) * v.y) / l2))
    min m (p - (a + t * v)).norm

/-- Whether the rounded curve of a random polyline starts and ends where the polyline does,
keeps its control points on the polyline (so that it lies in the triangles of the bends), turns
no more than the polyline and no more often the other way, and runs down all the way. -/
def roundedOk (seed : Nat) : Bool :=
  let pts := randomRoute seed (2 + seed % 7)
  let (pieces, bends) := roundedPieces pts
  let curve := flat pieces
  pieces.size == bends.size &&
    (pieces.getD 0 default).1 == pts.getD 0 ⟨-1, -1⟩ &&
    (pieces.back?.map (·.2.2.2)) == pts.back? &&
    pieces.all (fun (a, b, c, d) => [a, b, c, d].all fun p => distanceTo pts p < 1e-6) &&
    turning curve ≤ turning pts + 0.5 &&
    GraphQuality.inflections (GraphQuality.turns curve) 2 ≤
      GraphQuality.inflections (GraphQuality.turns pts) 1 &&
    (Array.range (curve.size - 1)).all fun j =>
      (curve.getD j ⟨0, 0⟩).y ≤ (curve.getD (j + 1) ⟨0, 0⟩).y + 1e-9

/-- A route around a box: down, far to the right past the box's corner, and down. The zone is
the room beside the box. -/
def corner : Array Point × Array Zone :=
  (#[⟨0, 0⟩, ⟨200, 60⟩, ⟨200, 300⟩], #[⟨198, 1e6, 70, 300⟩])

/-- Whether a point lies on the outline of a node: on the boundary of its box (within a pixel),
or near the ellipse inside it. -/
def onOutline (n : NodeBox) (p : Point) : Bool :=
  if n.shape == .ellipse then
    let u := (p.x - (n.box.x0 + n.box.x1) / 2) / (n.box.width / 2)
    let v := (p.y - (n.box.y0 + n.box.y1) / 2) / (n.box.height / 2)
    0.8 ≤ u * u + v * v && u * u + v * v ≤ 1.25
  else Graphs.onBoundary n.box p

/-- Whether every arrowhead of the layout has its tip on the outline of the node it points at
and lies along the end of its curve (within a degree). -/
def headsOk (l : Layout) : Bool :=
  l.edges.all fun e => match e.head with
    | none => true
    | some h =>
      let hp := (h.flatten 0.1).foldl (fun acc pl => acc ++ pl.points) #[]
      let tip := hp.getD 0 ⟨0, 0⟩
      let base := (hp.getD 1 ⟨0, 0⟩).mid (hp.getD 2 ⟨0, 0⟩)
      -- the direction in which the curve ends: from its last control point to its end
      let controls := e.path.cmds.foldl (fun acc c => acc ++ c.points) ([] : List Point)
      let along := match controls.reverse with
        | last :: before :: _ => unit (last - before)
        | _ => ⟨0, 0⟩
      let axis := unit (tip - base)
      (l.nodes[e.dst]?.any fun n => onOutline n tip) &&
        (e.src == e.dst || along.x * axis.x + along.y * axis.y > 0.9999)

/-- A graph of two clusters joined by edges, each with an edge inside, and a node outside. -/
def twoClusters : Graph :=
  { nodes := (Array.range 7).map fun v => { label := s!"n{v}" },
    edges := #[(0, 1), (2, 3), (1, 2), (0, 3), (4, 0), (3, 5), (4, 6)].map
      fun (a, b) => { src := a, dst := b },
    clusters := #[{ name := "Upper", members := #[0, 1] },
      { name := "Lower", members := #[2, 3] }] }

/-- The first and last layer (by the top of the boxes) of a cluster's nodes. -/
def clusterExtent (g : Graph) (l : Layout) (c : Nat) : Float × Float :=
  let ys := ((g.clusters.getD c default).members.filterMap fun v => l.nodes[v]?).map (·.box.y0)
  (ys.foldl min 1e30, ys.foldl max (-1e30))

/-- Whether `wrapLayers` keeps every pair of items that lay one below the whole of the other so,
moves nothing up, and leaves no row wider than the limit unless one item alone is. -/
def wrapOk (seed : Nat) : Bool := Id.run do
  let m := 6 + seed % 30
  let (r, _) := GraphOrder.draws seed.toUInt64 (3 * m) 1000
  let top := (Array.range m).map fun i => r.getD (3 * i) 0 % 5
  let height := (Array.range m).map fun i => 1 + r.getD (3 * i + 1) 0 % 3
  let width := (Array.range m).map fun i => 20 + (r.getD (3 * i + 2) 0 % 80).toFloat
  let limit : Float := 150
  let out := wrapLayers top height width (Array.replicate m 0) limit
  let below := fun (t : Array Nat) (a b : Nat) => t.getD a 0 + height.getD a 1 ≤ t.getD b 0
  let mut ok := out.size == m
  for a in [0:m] do
    if out.getD a 0 < top.getD a 0 then ok := false
    for b in [0:m] do
      if below top a b && !below out a b then ok := false
  -- the items that start in a row are together within the limit, or the row has one of them
  let rows := out.foldl max 0 + 1
  for row in [0:rows] do
    let starters := (Array.range m).filter fun i => out.getD i 0 == row
    let sum := starters.foldl (fun s i => s + width.getD i 0) 0
    if starters.size > 1 && sum > limit + 1e-9 then ok := false
  return ok

/-- The checks (see the module docstring). -/
def checks : Array (String × Bool) :=
  let (cornerPts, cornerZones) := corner
  let full := (roundedPieces cornerPts).1
  let fitted := fitPieces cornerPts cornerZones
  let line := #[linePiece ⟨0, 0⟩ ⟨30, 40⟩]
  let (cut, dir) := shortenEnd line 5
  let g := (GraphQuality.graphs.find? (·.1 == "blueprint-a")).map (·.2) |>.getD {}
  let chapters := (GraphQuality.graphs.find? (·.1 == "blueprint-a-chapters")).map (·.2) |>.getD {}
  let l := g.layout
  let lr := g.layout { direction := .leftToRight }
  let nested := chapters.layout
  let together := chapters.layout { nestedClusters := false }
  let two := twoClusters.layout
  let (upperTop, upperBottom) := clusterExtent twoClusters two 0
  let (lowerTop, _) := clusterExtent twoClusters two 1
  -- a planted fault: the first edge of the layout drawn back up through the drawing
  let bent : Layout := { l with edges := l.edges.modify 0 fun e =>
    { e with path := ((Path.empty.moveTo ⟨10, 400⟩).lineTo ⟨900, 10⟩).lineTo ⟨900, 500⟩ } }
  let star := Graph.ofPairs ((List.range 60).map fun i => (0, i + 1))
  let wide := star.layout
  let wrapped := star.layout { maxLayerWidth := 600 }
  let tree := ClusterTree.of twoClusters
  let layers := nestedLayers 7 tree (twoClusters.edges.map fun e => (e.src, e.dst))
    (Array.replicate 7 60) 12 0 1000000
  let (order, relaxed) := assignNested 7 tree (twoClusters.edges.toList.map fun e => (e.src, e.dst))
    (Array.replicate 7 60) 12 0
  #[("routes: nothing in the way is one straight line",
      tautRoute ⟨0, 0⟩ #[⟨-50, 50, 10⟩, ⟨-5, 80, 30⟩] ⟨20, 40⟩ == #[⟨0, 0⟩, ⟨20, 40⟩]),
    ("routes: a gate to one side bends the route at its nearer end",
      tautRoute ⟨0, 0⟩ #[⟨50, 60, 10⟩] ⟨0, 20⟩ == #[⟨0, 0⟩, ⟨50, 10⟩, ⟨0, 20⟩]),
    ("routes: a gate that is one point is passed there",
      tautRoute ⟨0, 0⟩ #[⟨7, 7, 10⟩, ⟨7, 7, 20⟩] ⟨0, 30⟩ == #[⟨0, 0⟩, ⟨7, 10⟩, ⟨7, 20⟩, ⟨0, 30⟩]),
    ("routes: the shortest route passes every gate, bends at gate ends and is the shortest \
      (300 random cases)", (List.range 300).all tautOk),
    ("routes: a route moved out of a gate is reported",
      !throughGates #[⟨0, 0⟩, ⟨80, 10⟩, ⟨0, 20⟩] #[⟨50, 60, 10⟩] &&
        throughGates #[⟨0, 0⟩, ⟨55, 10⟩, ⟨0, 20⟩] #[⟨50, 60, 10⟩]),
    ("routes: the curve keeps the ends, lies in the triangles of the bends, turns as the route \
      does and runs down (300 random cases)", (List.range 300).all roundedOk),
    ("routes: without cuts the curve is the polyline",
      flat (roundedPieces cornerPts #[0, 0, 0]).1 == cornerPts),
    ("routes: the full rounding of a bend at a box leaves its zone, and the check reports it",
      (piecesFit full cornerZones).contains false),
    ("routes: the fitted curve stays in its zone and still rounds the bend",
      (piecesFit fitted cornerZones).all id && fitted.size > 2 &&
        (flat fitted).all fun p => p.y < 70 || p.x ≥ 198 - 0.01),
    ("routes: a polyline outside its zones is left a polyline",
      flat (fitPieces cornerPts #[⟨500, 1e6, 70, 300⟩]) == cornerPts),
    ("routes: room for an arrowhead is taken off the end, along the curve",
      cut.size == 1 && ((cut.getD 0 default).2.2.2.dist ⟨27, 36⟩) < 1e-9 &&
        (dir.dist ⟨0.6, 0.8⟩) < 1e-9),
    ("routes: no edge of a drawing turns back across its layers",
      (GraphQuality.eye l).turnedBack false == 0 && (GraphQuality.eye lr).turnedBack true == 0 &&
        (GraphQuality.eye nested).turnedBack false == 0),
    ("routes: an edge drawn back up through the drawing is reported",
      (GraphQuality.eye bent).turnedBack false == 1 && (GraphQuality.eye bent).nearest == 0 &&
        !((clearanceProblems g bent).isEmpty)),
    ("routes: every arrowhead touches its node and lies along its curve",
      headsOk l && headsOk lr && headsOk nested),
    ("routes: an arrowhead turned away from its curve is reported",
      !headsOk { l with edges := l.edges.modify 0 fun e =>
        { e with head := e.head.map fun _ => arrowPath (e.points.back?.getD ⟨0, 0⟩) ⟨1, 0⟩ } }),
    ("routes: the same drawing twice, the starts searched at the same time",
      g.toSvg == g.toSvg && chapters.toSvg == chapters.toSvg),
    ("clusters: the layers of a wide layer split into rows keep every edge pointing down \
      (200 random cases)", (List.range 200).all wrapOk),
    ("clusters: no limit, no change", wrapLayers #[0, 0, 1] #[1, 1, 1] #[900, 900, 900] #[0, 0, 0] 0
      == #[0, 0, 1]),
    ("clusters: a star's layer of 60 nodes is split into rows",
      wrapped.width < wide.width / 2 && wrapped.height > wide.height && Graphs.disjoint wrapped &&
        (GraphQuality.eye wrapped).turnedBack false == 0 &&
        (clearanceProblems star wrapped).isEmpty),
    ("clusters: each cluster has layers of its own: the lower one begins below the upper one",
      layers.size == 7 && layers.getD 0 9 < layers.getD 1 0 && layers.getD 1 9 < layers.getD 2 0 &&
        layers.getD 2 9 < layers.getD 3 0 && layers.getD 4 9 < layers.getD 0 0 &&
        upperTop ≤ upperBottom && upperBottom < lowerTop),
    ("clusters: the final relaxation changes nothing, and the order is that of the layers",
      relaxed == layers && order == layers),
    ("clusters: no edge of the drawing by chapter passes through a chapter it does not end in",
      ((clearanceProblems chapters nested).filter (Graphs.has · "enters cluster")).isEmpty &&
        (clusterProblems chapters nested).isEmpty),
    ("clusters: layered all together, edges do pass through chapters, and the check reports it",
      !((clearanceProblems chapters together).filter (Graphs.has · "enters cluster")).isEmpty),
    ("clusters: counting the width of the layers gives a narrower drawing with boxes apart",
      (g.layout { compact := 4 }).width < l.width && Graphs.disjoint (g.layout { compact := 4 }) &&
        (clearanceProblems g (g.layout { compact := 4 })).isEmpty)]

end PILeanTest.GraphRoutes
