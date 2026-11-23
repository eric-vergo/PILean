/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Graph.Simple
import PILean.Exact.Plane

/-!
# Graphs at given positions

`Graph.fixedLayout` puts every node of a graph at a position the caller gives (page coordinates,
`y` down) and draws the edges between them, as a `Layout` like every other: `Layout.toSvg`,
`Graph.toPng` through `Layout.draw`, and `Layout.toWebSvg` (ids, classes and titles) all take it.
The node boxes are sized from their labels as in the other layouts, and the layout is moved so
that it starts `Style.margin` from the top left corner (`Layout.fit`).

* `FixedEdges.straight`: every edge a straight segment between the nodes' outlines (parallel
  edges and the two directions of one pair are bent apart, as in the circular layout).
* `FixedEdges.aroundNodes`: an edge whose straight segment passes within `gap` pixels of another
  node's box is bent, as one quadratic curve to the side that needs the smaller bend, so that its
  middle part keeps `gap` from those boxes (each box is cleared where the edge passes it; a box
  that a bent edge then meets elsewhere is not looked at again).

`Graph.fixedLayoutAt` takes world positions (`y` up) and a scale; `Graph.fixedLayoutExact` takes
exact points (`Exact.PlanePoint`), converted at the last step.

## Main definitions

* `FixedEdges`, `Graph.fixedLayout`, `Graph.fixedLayoutAt`, `Graph.fixedLayoutExact`.
-/

namespace PILean.Graph

/-- How the edges of a fixed layout run (see the module docstring). -/
inductive FixedEdges where
  /-- Straight segments. -/
  | straight
  /-- Bent around the nodes they would pass through. -/
  | aroundNodes
  deriving BEq, Inhabited, Repr

/-- The bend (the control point's offset from the middle of the chord, along the chord's left
normal) that takes the curve from `a` to `b` `gap` pixels clear of the boxes `obstacles` where it
passes them: the smaller of the bends to either side; 0 when nothing is in the way. -/
def bendAround (a b : Point) (obstacles : Array Box) (gap : Float) : Float := Id.run do
  let v := b - a
  let len := v.norm
  if len == 0 then return 0
  let d := (1 / len) * v
  let n : Point := ⟨-d.y, d.x⟩
  let mut pos : Float := 0
  let mut neg : Float := 0
  let mut hit := false
  for bx in obstacles do
    let c : Point := ⟨(bx.x0 + bx.x1) / 2, (bx.y0 + bx.y1) / 2⟩
    let t := ((c - a).x * d.x + (c - a).y * d.y) / len
    if t ≤ 0.02 || t ≥ 0.98 then continue
    let s := (c - a).x * n.x + (c - a).y * n.y
    let h := n.x.abs * bx.width / 2 + n.y.abs * bx.height / 2
    if s.abs ≥ h + gap then continue
    hit := true
    let k := 2 * t * (1 - t)
    pos := max pos ((s + h + gap) / k)
    neg := min neg ((s - h - gap) / k)
  return if !hit then 0 else if pos ≤ -neg then pos else neg

/-- The layout of `g` with node `i` centred at `centres[i]` (page coordinates; a missing centre is
the origin), its edges as `edges` says (see the module docstring), moved to start `Style.margin`
from the corner. -/
def fixedLayout (g : Graph) (centres : Array Point) (edges : FixedEdges := .straight)
    (gap : Float := 6) (o : LayeredOptions := {}) (st : Style := {}) : Layout := Id.run do
  let n := g.nodes.size
  let nodes := boxesAt g o st centres
  let ve := g.validEdges
  let key := fun (e : Graph.Edge) => min e.src e.dst * (n + 1) + max e.src e.dst
  let counts : Std.HashMap Nat Nat := ve.foldl (fun m (_, e) =>
    m.insert (key e) (m.getD (key e) 0 + 1)) {}
  let mut seen : Std.HashMap Nat Nat := {}
  let mut out : Array RoutedEdge := #[]
  for (i, e) in ve do
    let a := nodes.getD e.src default
    let b := nodes.getD e.dst default
    if e.src == e.dst then
      let (p, h) := loopGeometry a.box (g.directed && e.directed)
      let cy := (a.box.y0 + a.box.y1) / 2
      let q := min (a.box.height / 4) 8
      let loop : RoutedEdge :=
        { index := i, src := e.src, dst := e.dst, reversed := false, path := p, head := h,
          label := none, points := #[⟨a.box.x1, cy - q⟩, ⟨a.box.x1, cy + q⟩] }
      out := out.push loop
    else
      let j := seen.getD (key e) 0
      seen := seen.insert (key e) (j + 1)
      let c := counts.getD (key e) 1
      let sign : Float := if e.src < e.dst then 1 else -1
      let parallel := sign * (j.toFloat - (c.toFloat - 1) / 2) * 26
      let around := if edges == .aroundNodes then
          let others := nodes.filter (fun nb => nb.index != e.src && nb.index != e.dst) |>.map
            (·.box)
          let ca : Point := ⟨(a.box.x0 + a.box.x1) / 2, (a.box.y0 + a.box.y1) / 2⟩
          let cb : Point := ⟨(b.box.x0 + b.box.x1) / 2, (b.box.y0 + b.box.y1) / 2⟩
          bendAround ca cb others gap
        else 0
      out := out.push (straightEdge st g.directed a b (parallel + around) i e)
  return ({ nodes, edges := out, clusters := clusterBoxes g nodes } : Layout).fit st.margin

/-- The layout of `g` with node `i` at the world point `positions[i]` (`y` up) at `scale` pixels
per unit (see `fixedLayout`). -/
def fixedLayoutAt (g : Graph) (positions : Array Point) (scale : Float := 100)
    (edges : FixedEdges := .straight) (gap : Float := 6) (o : LayeredOptions := {})
    (st : Style := {}) : Layout :=
  fixedLayout g (positions.map fun p => ⟨scale * p.x, -scale * p.y⟩) edges gap o st

/-- The layout of `g` with node `i` at the exact point `positions[i]`, converted
(`Exact.PlanePoint.toPoint`), at `scale` pixels per unit (see `fixedLayoutAt`). -/
def fixedLayoutExact {α : Type} [Exact.PlanePoint α] (g : Graph) (positions : Array α)
    (scale : Float := 100) (edges : FixedEdges := .straight) (gap : Float := 6)
    (o : LayeredOptions := {}) (st : Style := {}) : Layout :=
  fixedLayoutAt g (positions.map Exact.PlanePoint.toPoint) scale edges gap o st

end PILean.Graph
