/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Graph.Layered

/-!
# Components laid out apart and packed, and mirrored layouts

A graph with several connected components drawn as one layered picture puts them side by side in
one row of layers, however many there are: a wide, flat drawing with long empty stretches.
`Graph.layoutPacked` lays every component out on its own and packs the drawings into rows:

* **Components** (`components`): nodes joined by an edge are in one component, and so are the
  nodes of one top cluster (with the clusters inside it), so that a cluster's box stays whole.
* **Packing** (`shelves`): the drawings are sorted by height, the tallest first (the earliest
  node first among equals), and put on shelves from left to right, a new shelf starting when the
  next drawing would pass the width `sqrt (aspect × area)`; shelf packing in the order of
  decreasing height (Coffman, Garey, Johnson and Tarjan's *next fit decreasing height*). The work
  is `O(k log k)` for `k` components besides their layouts.

`Layout.mirror` turns a layout upside down or left to right, which is how layers that run from
the bottom up or from right to left are drawn: the layout of the opposite direction, mirrored.

## References

* Coffman, Garey, Johnson, Tarjan, *Performance bounds for level-oriented two-dimensional packing
  algorithms*, SIAM Journal on Computing 9 (1980).

## Main definitions

* `components`, `Graph.component`, `shelves`, `Graph.layoutPacked`, `Layout.mirror`.
-/

namespace PILean.Graph

/-- The component of every node, numbered from zero in the order of each component's first
node: two nodes are in one component when a valid edge joins them or one top cluster holds both
(see the module docstring). Work: `O((V + E + M) α)` for `M` cluster members. -/
def components (g : Graph) : Array Nat := Id.run do
  let n := g.nodes.size
  let mut parent : Array Nat := Array.range n
  let find := fun (parent : Array Nat) (v : Nat) => Id.run do
    let mut x := v
    for _ in [0:n] do
      let p := parent.getD x x
      if p == x then break
      x := p
    return x
  let mut join : Array (Nat × Nat) := g.validEdges.map fun (_, e) => (e.src, e.dst)
  -- the members of every cluster, joined to the first member of its top cluster
  let t := ClusterTree.of g
  let mut first : Array (Option Nat) := Array.replicate g.clusters.size none
  for v in [0:n] do
    if let some c := t.nodeCluster.getD v none then
      let top := (t.path (some c)).getD 0 c
      match first.getD top none with
      | none => first := first.setIfInBounds top (some v)
      | some u => join := join.push (u, v)
  for (a, b) in join do
    let ra := find parent a
    let rb := find parent b
    if ra != rb then
      -- the smaller root stays the root, so a root is its component's first node
      parent := parent.setIfInBounds (max ra rb) (min ra rb)
      parent := (parent.setIfInBounds a (min ra rb)).setIfInBounds b (min ra rb)
  let mut number : Array Nat := Array.replicate n 0
  let mut count := 0
  let mut out : Array Nat := Array.replicate n 0
  for v in [0:n] do
    let r := find parent v
    if r == v then
      number := number.setIfInBounds v count
      count := count + 1
    out := out.setIfInBounds v (number.getD r 0)
  return out

/-- The part of the graph on the nodes `keep` (in increasing order): those nodes, the valid edges
between them, and every cluster with the members among them (so the clusters keep their numbers
and parents). Also returns the position in `g.edges` of every edge of the part. -/
def component (g : Graph) (keep : Array Nat) : Graph × Array Nat := Id.run do
  let mut index : Array (Option Nat) := Array.replicate g.nodes.size none
  for i in [0:keep.size] do index := index.setIfInBounds (keep.getD i 0) (some i)
  let at? := fun (v : Nat) => index.getD v none
  let mut edges : Array Graph.Edge := #[]
  let mut origin : Array Nat := #[]
  for (i, e) in g.validEdges do
    match at? e.src, at? e.dst with
    | some a, some b =>
      edges := edges.push { e with src := a, dst := b }
      origin := origin.push i
    | _, _ => pure ()
  let clusters := g.clusters.map fun c => { c with members := c.members.filterMap at? }
  return ({ g with nodes := keep.map (g.nodes.getD · default), edges, clusters }, origin)

/-- Where each of the boxes `sizes` (width, height) goes when they are packed on shelves of
width at most `sqrt (aspect × area)` (and at least the widest box), `gap` apart: the top-left
corner of every box, in the order given. The boxes are placed in the order of decreasing height,
earlier ones first among equals. -/
def shelves (sizes : Array (Float × Float)) (gap aspect : Float) : Array (Float × Float) :=
  Id.run do
  let area := sizes.foldl (fun s (w, h) => s + (w + gap) * (h + gap)) 0
  let widest := sizes.foldl (fun m (w, _) => max m w) 0
  let limit := max widest (aspect * area).sqrt
  let byHeight := (Array.range sizes.size).sortStable fun i j =>
    (sizes.getD i (0, 0)).2 > (sizes.getD j (0, 0)).2
  let mut out : Array (Float × Float) := Array.replicate sizes.size (0, 0)
  let mut x : Float := 0
  let mut y : Float := 0
  let mut shelf : Float := 0
  for i in byHeight do
    let (w, h) := sizes.getD i (0, 0)
    if x > 0 && x + w > limit then
      x := 0
      y := y + shelf + gap
      shelf := 0
    out := out.setIfInBounds i (x, y)
    x := x + w + gap
    shelf := max shelf h
  return out

/-- The layered layout of the graph with its components laid out one by one (`Graph.layout`'s
phases on each) and packed on shelves `gap` apart, towards a picture `aspect` times as wide as
tall. A graph of one component gets `Graph.layout`'s layout. Every node has its box, every valid
edge its route (in the order of `Graph.validEdges`) and every cluster with a member its box, as
there. -/
def layoutPacked (g : Graph) (o : LayeredOptions := {}) (st : Style := {}) (gap : Float := 40)
    (aspect : Float := 1.6) : Layout := Id.run do
  let comp := components g
  let count := comp.foldl (fun m c => max m (c + 1)) 0
  if count ≤ 1 then return g.layout o st
  let mut members : Array (Array Nat) := Array.replicate count #[]
  for v in [0:comp.size] do members := members.modify (comp.getD v 0) (·.push v)
  let parts := members.map fun keep =>
    let (sub, origin) := component g keep
    ((layoutRaw sub o st).fit 0, keep, origin)
  let places := shelves (parts.map fun (l, _, _) => (l.width, l.height)) gap aspect
  let mut nodes : Array NodeBox := g.nodes.mapIdx fun i nd => nodeBoxOf st i nd ⟨0, 0, 0, 0⟩
  let mut edges : Array RoutedEdge := #[]
  let mut clusters : Array ClusterBox := #[]
  let mut ports : Array PortMark := #[]
  for (l, keep, origin) in parts, (dx, dy) in places do
    let m := l.translate dx dy
    for nb in m.nodes do
      let v := keep.getD nb.index 0
      nodes := nodes.setIfInBounds v { nb with index := v }
    for e in m.edges do
      edges := edges.push { e with index := origin.getD e.index 0, src := keep.getD e.src 0,
                                   dst := keep.getD e.dst 0 }
    clusters := clusters ++ m.clusters
    ports := ports ++ m.ports.map fun p => { p with node := keep.getD p.node 0 }
  let sorted := edges.qsort fun a b => a.index < b.index
  return ({ nodes, edges := sorted, clusters := clusters.qsort fun a b => a.index < b.index,
            ports := ports.qsort fun a b => a.node < b.node || (a.node == b.node && !a.entry && b.entry) } :
    Layout).fit st.margin

/-- The layout mirrored: upside down (`vertical`), or left to right. Boxes, routes, arrowheads,
stems and label plates keep their sizes; the picture keeps its size. -/
def Layout.mirror (l : Layout) (vertical : Bool) : Layout :=
  let m : Affine := if vertical then { d := -1, f := l.height } else { a := -1, e := l.width }
  let mb := fun (b : Box) =>
    if vertical then (⟨b.x0, l.height - b.y1, b.x1, l.height - b.y0⟩ : Box)
    else ⟨l.width - b.x1, b.y0, l.width - b.x0, b.y1⟩
  { l with
    nodes := l.nodes.map fun n => { n with box := mb n.box },
    edges := l.edges.map fun e =>
      { e with path := e.path.transform m, head := e.head.map (·.transform m),
               label := e.label.map fun t => { t with box := mb t.box },
               points := e.points.map m.apply },
    clusters := l.clusters.map fun c => { c with box := mb c.box },
    ports := l.ports.map fun p =>
      { p with stem := p.stem.map (·.transform m), head := p.head.map (·.transform m),
               trunk := (m.apply p.trunk.1, m.apply p.trunk.2) } }

end PILean.Graph
