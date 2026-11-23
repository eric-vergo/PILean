/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Graph.Model
import PILean.Style
import PILean.Path

/-!
# Graph layouts: the result and what the layouts share

A layout of a graph is a `Layout`: a box for every node, a path (with an arrowhead and a label
plate) for every edge, a box for every cluster and the size of the picture, all in pixels with
`y` downwards. The layouts differ in how they find the positions
(`Graph.layout` in `PILean.Graph.Layered`, `Graph.circularLayout` and `Graph.treeLayout` in
`PILean.Graph.Simple`); this file holds what they share: the options, node sizes from labels,
arrowheads, the curve through points, rounded polylines, loops and clipping to node outlines.

## Main definitions

* `LayeredOptions`, `Direction`, `Routing`.
* `BundleStyle`: the look of bundled routes.
* `NodeBox`, `RoutedEdge`, `EdgeLabel`, `PortMark`, `ClusterBox`, `Layout`.
* `nodeSize`, `arrowPath`, `splinePath`, `roundedPolyline`, `loopGeometry`, `clipToNode`.
-/

namespace PILean.Graph

/-- The direction layers follow. -/
inductive Direction where
  /-- Layers are rows, the first on top. -/
  | topToBottom
  /-- Layers are columns, the first on the left. -/
  | leftToRight
  deriving BEq, Inhabited, Repr

/-- How edges are drawn through their route. -/
inductive Routing where
  /-- Smooth cubic Bézier curves through the points of the route. -/
  | spline
  /-- Horizontal and vertical segments with rounded corners. -/
  | orthogonal
  /-- Horizontal and vertical segments in bundles of parallel lanes, one entry and one exit port
  per node, concentric corners (`PILean.Graph.Bundle`); its look is `LayeredOptions.bundle`. -/
  | bundled
  deriving BEq, Inhabited, Repr

/-- The look of bundled routes (`Routing.bundled`). Lengths are pixels. -/
structure BundleStyle where
  /-- The distance between two neighbouring parallel lanes: between the tracks of a channel and
  between the vertical lanes of long edges beside each other in a layer. -/
  laneGap : Float := 6
  /-- The radius of the innermost corner of a bundle that turns; the lane `k` places further out
  turns with `radius + k * laneGap`, about the same centre. -/
  radius : Float := 6
  /-- The straight length of a stem between a node's port and the first corner of an edge that
  leaves it or the last corner of one that enters it (the arrowhead not counted). -/
  stemLength : Float := 10
  /-- The least distance between the ends of two runs on one track. -/
  trackGap : Float := 12
  deriving Inhabited, Repr

/-- The options of the layouts. Lengths are pixels. -/
structure LayeredOptions where
  /-- The direction layers follow. -/
  direction : Direction := .topToBottom
  /-- The space between one layer's nodes and the next layer's. -/
  layerGap : Float := 44
  /-- The space between neighbouring nodes of a layer. -/
  nodeGap : Float := 28
  /-- The space between neighbouring edges that cross a layer. -/
  edgeGap : Float := 14
  /-- How edges are drawn. -/
  routing : Routing := .spline
  /-- The look of bundled routes (`Routing.bundled`). -/
  bundle : BundleStyle := {}
  /-- How many times taller than `layerGap` a gap may grow: for a curve that crosses it far
  sideways (see `flattest`), or to keep the horizontal runs of orthogonal routes three pixels
  apart. -/
  sidewaysGap : Float := 2.5
  /-- The most a curve should go sideways in a gap, in gap heights: a gap grows, within
  `sidewaysGap`, until its widest step is no flatter. -/
  flattest : Float := 12
  /-- The most rounds of weighted-median sweeps (each followed by transposition) of the
  crossing reduction. -/
  sweeps : Nat := 24
  /-- The most extra starts of the crossing reduction, from depth-first orders drawn from a fixed
  sequence (`orderLayers`, `reduceClustered`); fewer are made on a large graph. More starts find
  fewer crossings and take longer. -/
  starts : Nat := 16
  /-- The number of passes that straighten edges before the network simplex assignment starts. -/
  refine : Nat := 8
  /-- The work allowed to the network simplex coordinate assignment (see `simplexBreadth`): about
  this many steps in all; when it is used up the best assignment so far is kept. -/
  coordinateWork : Nat := 90000000
  /-- The height of a node box. -/
  nodeHeight : Float := 28
  /-- The space between a node's label and its outline on each side. -/
  nodePadding : Float := 14
  /-- The smallest width of a node box. -/
  minNodeWidth : Float := 40
  /-- The distance between the points where edges meet a node's side. -/
  portStep : Float := 14
  /-- The most real and dummy nodes the crossing reduction and the coordinates work on: when the
  edges' spans would need more dummy nodes, long edges are drawn without them (straight between
  their ends, so they may cross other nodes), which keeps the work linear in the graph. -/
  maxLayoutNodes : Nat := 200000
  /-- The work allowed to the network simplex layering (in the units of `simplexComponent`):
  when it is used up, the best layering so far is kept. -/
  layerWork : Nat := 100000000
  /-- The weight of the width of every layer in the total that the coordinates minimise (the
  horizontal length of an edge between two real nodes weighs `1`): `0` places the nodes as
  Gansner et al. do, a larger weight gives a narrower drawing with more slanted edges. -/
  compact : Nat := 0
  /-- The width from which the nodes that start in one layer are split over several rows (inside
  a cluster: the nodes and clusters of one of its layers); `0` for no limit. Edges that cross the
  layer add to its width, so a drawing can be wider than this. -/
  maxLayerWidth : Float := 0
  /-- Whether a graph with clusters is layered from the inside out, every cluster keeping a
  block of layers to itself (`PILean.Graph.Nested`); otherwise all nodes are layered together
  and the nodes of a cluster pulled towards each other. -/
  nestedClusters : Bool := true
  /-- How many times at most the layers of a graph with clusters are found again to keep an edge
  from passing through a cluster that holds neither of its ends: each time, such a cluster and
  the node or cluster the edge leads to are put one above the other; the attempt with the fewest
  such edges is kept. A large graph with many clusters may need twenty rounds and more, each as
  long as the first three phases of the layout. -/
  clusterRounds : Nat := 12
  /-- The length of an arrowhead (`none`: `arrowLength`). -/
  arrowLength : Option Float := none
  /-- The half-width of an arrowhead (`none`: `arrowHalfWidth`). -/
  arrowHalfWidth : Option Float := none
  deriving Inhabited

/-- A node's box and look, resolved from the style and the node's overrides. -/
structure NodeBox where
  /-- The node's number. -/
  index : Nat
  /-- The box (an ellipse is inscribed in it). -/
  box : Box
  /-- The label. -/
  label : String
  /-- The outline shape. -/
  shape : Graph.NodeShape
  /-- The fill colour. -/
  fill : Rgba
  /-- The outline colour. -/
  stroke : Rgba
  deriving Inhabited

/-- An edge's label on a plate of the page colour. -/
structure EdgeLabel where
  /-- The text. -/
  text : String
  /-- The plate, centred on the edge. -/
  box : Box
  deriving Inhabited

/-- An edge drawn: its path from the source's outline to the target's (a path ending where an
arrowhead starts when there is one). -/
structure RoutedEdge where
  /-- The edge's position in the graph's `edges`. -/
  index : Nat
  /-- The source node. -/
  src : Nat
  /-- The target node. -/
  dst : Nat
  /-- Whether the layout reversed the edge to remove a cycle (it is drawn in its own direction
  all the same). -/
  reversed : Bool
  /-- The curve, from the source to the target. -/
  path : Path
  /-- The arrowhead (a closed path to fill), when the edge has one. -/
  head : Option Path
  /-- The label, when the edge has one. -/
  label : Option EdgeLabel
  /-- The route's points from the source's outline to the target's (dummy points of long edges
  included), the polyline that the curve follows. -/
  points : Array Point
  deriving Inhabited

/-- What a bundled layout (`Routing.bundled`) draws once at a node's port, for all the edges that
use it: the stem (the vertical trunk the edges leave or join) and, at an entry port, the
arrowhead. -/
structure PortMark where
  /-- The node. -/
  node : Nat
  /-- Whether this is the node's entry port (where edges arrive) rather than its exit port. -/
  entry : Bool
  /-- The stem, from the port to the last point where an edge leaves it (or from the first
  point where an edge joins it to the arrowhead); `none` when one edge uses the port, whose own
  path then reaches the port. -/
  stem : Option Path := none
  /-- The arrowhead (a closed path to fill), at an entry port that a directed edge reaches. -/
  head : Option Path := none
  /-- The trunk that the edges of the port share, as a segment from the port to the corner of
  the edge that leaves it last or joins it first (the stem with those corners' roundings): no two
  edges share a segment elsewhere. -/
  trunk : Point × Point
  deriving Inhabited

/-- A cluster's box. -/
structure ClusterBox where
  /-- The title. -/
  name : String
  /-- The box around the members. -/
  box : Box
  /-- The cluster's number, which picks its colour. -/
  index : Nat
  deriving Inhabited

/-- A laid-out graph. -/
structure Layout where
  /-- The width of the picture. -/
  width : Float := 0
  /-- The height of the picture. -/
  height : Float := 0
  /-- A box for every node, in node order. -/
  nodes : Array NodeBox := #[]
  /-- A route for every valid edge, in edge order (`Graph.validEdges`). -/
  edges : Array RoutedEdge := #[]
  /-- The cluster boxes. -/
  clusters : Array ClusterBox := #[]
  /-- The stems and arrowheads drawn once per port (a bundled layout; empty otherwise). -/
  ports : Array PortMark := #[]
  deriving Inhabited

/-- The smallest even whole number at least `v`. -/
def evenUp (v : Float) : Float := 2 * (v / 2).ceil

/-- The outline shape of a node (the default is a rounded box). -/
def Node.shapeOf (n : Graph.Node) : NodeShape := n.style.shape.getD .round

/-- The width and height of the box of a node with a label, from the style's text engine: the
label's width plus padding, whole even numbers of pixels; an ellipse is larger to hold the
text. A node with a `size` of its own has that size, made whole and even. -/
def nodeSize (st : Style) (o : LayeredOptions) (n : Graph.Node) : Float × Float :=
  if let some (w, h) := n.size then (evenUp (max 2 w), evenUp (max 2 h)) else
  let w := st.text.measure n.label st.nodeLabelSize
  let k : Float := if n.shapeOf == .ellipse then 1.3 else 1
  (evenUp (max (o.minNodeWidth * k) ((w + 2 * o.nodePadding) * k)), evenUp (o.nodeHeight * k))

/-- The colours and shape of a node's box. -/
def nodeBoxOf (st : Style) (i : Nat) (n : Graph.Node) (box : Box) : NodeBox :=
  { index := i, box, label := n.label, shape := n.shapeOf,
    fill := n.style.fill.getD st.nodeFill, stroke := n.style.stroke.getD st.nodeStroke }

/-- The length of an arrowhead: to the default node height as Graphviz's arrowhead is to its
default node height. -/
def arrowLength : Float := 8

/-- The half-width of an arrowhead. -/
def arrowHalfWidth : Float := 2.8

/-- The arrowhead (a triangle) with its tip at `tip`, pointing along the unit vector `dir`,
`length` long and twice `half` wide. -/
def arrowPath (tip dir : Point) (length : Float := arrowLength)
    (half : Float := arrowHalfWidth) : Path :=
  let base : Point := ⟨tip.x - length * dir.x, tip.y - length * dir.y⟩
  let n : Point := ⟨-dir.y, dir.x⟩
  let l : Point := ⟨base.x + half * n.x, base.y + half * n.y⟩
  let r : Point := ⟨base.x - half * n.x, base.y - half * n.y⟩
  (((Path.empty.moveTo tip).lineTo l).lineTo r).close

/-- The unit vector along `v` (the zero vector for a zero or non-finite one). -/
def unit (v : Point) : Point :=
  let l := v.norm
  if l > 1e-9 && !l.isInf then ⟨v.x / l, v.y / l⟩ else ⟨0, 0⟩

/-- A cubic Bézier piece, as its four points. -/
abbrev Piece := Point × Point × Point × Point

/-- The path of the pieces in order (they are joined end to start). A piece whose control points
lie on the segment between its ends is written as a line, and one that is a parabola (a quadratic
curve written as a cubic) as a quadratic curve: the same curve in fewer numbers. -/
def piecesPath (ps : Array Piece) : Path :=
  match ps[0]? with
  | none => {}
  | some (p0, _, _, _) =>
    ps.foldl (init := Path.empty.moveTo p0) fun path (a, c1, c2, d) =>
      let v := d - a
      let l2 := v.x * v.x + v.y * v.y
      -- on the segment: no distance from its line, and between its ends
      let on := fun (c : Point) =>
        let w := c - a
        (v.x * w.y - v.y * w.x).abs ≤ 1e-6 * (1 + l2.sqrt) &&
          -1e-9 ≤ v.x * w.x + v.y * w.y && v.x * w.x + v.y * w.y ≤ l2 + 1e-9
      if on c1 && on c2 then path.lineTo d
      else
        -- the control point of the parabola, from either end
        let q1 := a + (1.5 : Float) * (c1 - a)
        let q2 := d + (1.5 : Float) * (c2 - d)
        if q1.dist q2 ≤ 1e-6 * (1 + l2.sqrt) then path.quadTo q1 d else path.cubicTo c1 c2 d

/-- The pieces reversed: traversed backwards, each with its control points swapped. -/
def reversePieces (ps : Array Piece) : Array Piece :=
  ps.reverse.map fun (p, c1, c2, q) => (q, c2, c1, p)

/-- The slopes `db/dt` of a monotone interpolant (Fritsch and Butland) through the points
`(t, b) = (p.y, p.x)` with strictly increasing `t`: zero at the ends and at local extrema, so
that the curve never overshoots its points. -/
def monotoneSlopes (ps : Array Point) : Array Float := Id.run do
  let n := ps.size
  let mut out := Array.replicate n 0
  if n < 3 then return out
  let h := fun (i : Nat) => max 1e-3 (((ps.getD (i + 1) ⟨0, 0⟩).y) - (ps.getD i ⟨0, 0⟩).y)
  let s := fun (i : Nat) => ((ps.getD (i + 1) ⟨0, 0⟩).x - (ps.getD i ⟨0, 0⟩).x) / h i
  for i in [1:n - 1] do
    let s0 := s (i - 1)
    let s1 := s i
    if s0 * s1 > 0 then
      let h0 := h (i - 1)
      let h1 := h i
      out := out.setIfInBounds i (3 * (h0 + h1) / ((2 * h1 + h0) / s0 + (h1 + 2 * h0) / s1))
  return out

/-- The pieces of the smooth curve through points whose second coordinate increases: each
piece is a cubic whose second coordinate is linear, and whose first coordinate leaves and
enters every point with the monotone slope (zero at the ends: the curve meets the first and
last point perpendicular to the layers). -/
def splinePieces (ps : Array Point) : Array Piece := Id.run do
  let slopes := monotoneSlopes ps
  let mut out : Array Piece := #[]
  for i in [0:ps.size - 1] do
    let p := ps.getD i ⟨0, 0⟩
    let q := ps.getD (i + 1) ⟨0, 0⟩
    let h := max 1e-3 (q.y - p.y)
    let m0 := slopes.getD i 0
    let m1 := slopes.getD (i + 1) 0
    out := out.push (p, ⟨p.x + m0 * h / 3, p.y + h / 3⟩, ⟨q.x - m1 * h / 3, q.y - h / 3⟩, q)
  return out

/-- A polyline with its corners rounded by radius `r` (less where a side is short). -/
def roundedPolyline (pts : Array Point) (r : Float) : Path := Id.run do
  let n := pts.size
  if n == 0 then return {}
  let mut path : Path := Path.empty.moveTo (pts.getD 0 ⟨0, 0⟩)
  for i in [1:n] do
    let v := pts.getD i ⟨0, 0⟩
    if i + 1 < n then
      let a := pts.getD (i - 1) ⟨0, 0⟩
      let c := pts.getD (i + 1) ⟨0, 0⟩
      let la := a.dist v
      let lc := c.dist v
      let k := min r (min la lc / 2)
      if k < 0.5 then path := path.lineTo v
      else
        let p := v + (k / la) * (a - v)
        let q := v + (k / lc) * (c - v)
        path := (path.lineTo p).quadTo v q
    else path := path.lineTo v
  return path

/-- A self-loop on the high side of the first coordinate of `box`: the curve (ending where the
arrowhead starts when `directed`) and the arrowhead. -/
def loopGeometry (box : Box) (directed : Bool) : Path × Option Path :=
  let cy := (box.y0 + box.y1) / 2
  let q := min (box.height / 4) 8
  let l := 16
  let x1 := box.x1
  let tip : Point := ⟨x1, cy + q⟩
  let finish : Point := if directed then ⟨x1 + arrowLength - 1, cy + q⟩ else tip
  let path := (Path.empty.moveTo ⟨x1, cy - q⟩).cubicTo ⟨x1 + 1.5 * l, cy - 2.2 * q⟩
    ⟨x1 + 1.5 * l, cy + 2.2 * q⟩ finish
  (path, if directed then some (arrowPath tip ⟨-1, 0⟩) else none)

/-- The width and height of the plate behind an edge label, from the style's text engine. -/
def plateSize (st : Style) (label : String) : Float × Float :=
  (evenUp (st.text.measure label st.noteSize + 10), evenUp (st.noteSize * 1.5))

/-- Where the ray from the centre of `box` towards `toward` leaves the outline (a box or an
ellipse inscribed in it). -/
def clipToNode (box : Box) (shape : NodeShape) (toward : Point) : Point :=
  let c : Point := ⟨(box.x0 + box.x1) / 2, (box.y0 + box.y1) / 2⟩
  let hw := box.width / 2
  let hh := box.height / 2
  let dx := toward.x - c.x
  let dy := toward.y - c.y
  if (dx == 0 && dy == 0) || hw <= 0 || hh <= 0 then c
  else
    let t := match shape with
      | .ellipse => 1 / ((dx / hw) ^ 2 + (dy / hh) ^ 2).sqrt
      | _ => min (if dx == 0 then 1e18 else hw / dx.abs) (if dy == 0 then 1e18 else hh / dy.abs)
    ⟨c.x + t * dx, c.y + t * dy⟩

/-- The first and second coordinates swapped: the map from the layers' frame (breadth,
level) to the picture for layers running left to right. -/
def Direction.swap : Affine := { a := 0, b := 1, c := 1, d := 0 }

/-- The transform from the layers' frame (first coordinate across a layer, second along the
layers) to the picture. -/
def Direction.frame : Direction → Affine
  | .topToBottom => Affine.id
  | .leftToRight => Direction.swap

/-- A box of the layers' frame in the picture. -/
def Direction.box (d : Direction) (b : Box) : Box :=
  match d with
  | .topToBottom => b
  | .leftToRight => ⟨b.y0, b.x0, b.y1, b.x1⟩

/-- The boxes of the graph's clusters: the box around the members' boxes, with room for the
title on top. A cluster without a member that is a node has no box. -/
def clusterBoxes (g : Graph) (nodes : Array NodeBox) : Array ClusterBox :=
  g.clusters.zipIdx.filterMap fun (c, ci) =>
    let boxes := c.members.filterMap fun v => (nodes[v]?).map (·.box)
    match boxes.toList with
    | [] => none
    | b :: bs =>
      let u := bs.foldl Box.union b
      some { name := c.name, index := ci,
             box := ⟨u.x0 - 14, u.y0 - 34, u.x1 + 14, u.y1 + 14⟩ }

namespace Layout

/-- The box of everything drawn (nodes, clusters, edges with their heads and labels); `none` for
an empty layout. -/
def bounds (l : Layout) : Option Box :=
  let boxes : Array Box := l.nodes.map (·.box) ++ l.clusters.map (·.box) ++
    l.edges.filterMap (fun e => e.path.controlBounds) ++
    l.edges.filterMap (fun e => e.head.bind (·.controlBounds)) ++
    l.edges.filterMap (fun e => e.label.map (·.box)) ++
    l.ports.filterMap (fun p => p.stem.bind (·.controlBounds)) ++
    l.ports.filterMap (fun p => p.head.bind (·.controlBounds))
  boxes.foldl (fun acc b => some (match acc with | none => b | some a => a.union b)) none

/-- The layout moved by `(dx, dy)`. -/
def translate (l : Layout) (dx dy : Float) : Layout :=
  let m := Affine.translate dx dy
  let mv := fun (b : Box) => (⟨b.x0 + dx, b.y0 + dy, b.x1 + dx, b.y1 + dy⟩ : Box)
  { l with
    nodes := l.nodes.map fun n => { n with box := mv n.box },
    edges := l.edges.map fun e =>
      { e with path := e.path.transform m, head := e.head.map (·.transform m),
               label := e.label.map fun t => { t with box := mv t.box },
               points := e.points.map m.apply },
    clusters := l.clusters.map fun c => { c with box := mv c.box },
    ports := l.ports.map fun p =>
      { p with stem := p.stem.map (·.transform m), head := p.head.map (·.transform m),
               trunk := (m.apply p.trunk.1, m.apply p.trunk.2) } }

/-- The layout moved so that its contents have `margin` pixels around them, on whole pixels,
with `width` and `height` set to match. An empty layout is two margins in size. -/
def fit (l : Layout) (margin : Float) : Layout :=
  match l.bounds with
  | none => { l with width := 2 * margin, height := 2 * margin }
  | some b =>
    let dx := margin - b.x0.floor
    let dy := margin - b.y0.floor
    { l.translate dx dy with width := (b.x1 + dx + margin).ceil,
                             height := (b.y1 + dy + margin).ceil }

end Layout

end PILean.Graph
