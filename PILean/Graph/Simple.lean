/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Graph.Layered

/-!
# Two simple layouts for small graphs

Layouts that need no search, for small undirected graphs and trees:

* `Graph.circularLayout`: the nodes on a circle in node order, the first at the top, going
  clockwise. The circle is as small as the nodes' sizes and the gap allow. Edges are straight
  lines between the nodes' outlines; parallel edges are bent apart into arcs.
* `Graph.treeLayout`: a rooted tree, one level per depth: each leaf takes the room its
  box needs and each parent is centred over its children (the room of a subtree is the
  larger of its box and its children's rooms side by side, so subtrees never overlap but
  are not packed against each other as in the contour method of Reingold and Tilford). Nodes are
  reached from the root by breadth-first search over the edges taken as undirected; nodes
  that are not reached become roots of further trees, placed beside the first. The edge to
  each node's parent is drawn like layered edges; other edges are straight lines.

Both use the node sizes, gaps and direction (the tree) of `LayeredOptions` and give the same
`Layout` as `Graph.layout`, so the same drawing code applies. Work: `O(V + E)` (the circle) and
`O(V + E)` (the tree).

## References

* Reingold, Tilford, *Tidier drawings of trees*, IEEE Transactions on Software Engineering 7
  (1981).
-/

namespace PILean.Graph

/-- An edge as a straight line (or, with `bend ≠ 0`, a quadratic arc bent sideways by `bend`
pixels) between the outlines of the nodes with boxes `a` and `b`; the arrowhead at its end when
the edge is directed. -/
def straightEdge (st : Style) (graphDirected : Bool) (a b : NodeBox) (bend : Float) (i : Nat)
    (e : Graph.Edge) : RoutedEdge :=
  let ca : Point := ⟨(a.box.x0 + a.box.x1) / 2, (a.box.y0 + a.box.y1) / 2⟩
  let cb : Point := ⟨(b.box.x0 + b.box.x1) / 2, (b.box.y0 + b.box.y1) / 2⟩
  let d := unit (cb - ca)
  let ctrl : Point := ca.mid cb + bend * (⟨-d.y, d.x⟩ : Point)
  let curved := bend != 0
  let start := clipToNode a.box a.shape (if curved then ctrl else cb)
  let tip := clipToNode b.box b.shape (if curved then ctrl else ca)
  let dir := unit (tip - (if curved then ctrl else start))
  let arrow := graphDirected && e.directed
  let finish : Point := if arrow then tip - (arrowLength - 1) * dir else tip
  let path := if curved then (Path.empty.moveTo start).quadTo ctrl finish
    else (Path.empty.moveTo start).lineTo finish
  let mid : Point :=
    if curved then ⟨(start.x + 2 * ctrl.x + tip.x) / 4, (start.y + 2 * ctrl.y + tip.y) / 4⟩
    else start.mid tip
  let label : Option EdgeLabel :=
    if e.label.isEmpty then none
    else
      let (w, h) := plateSize st e.label
      some { text := e.label, box := plateAt mid w h }
  { index := i, src := e.src, dst := e.dst, reversed := false, path,
    head := if arrow then some (arrowPath tip dir) else none, label,
    points := if curved then #[start, ctrl, tip] else #[start, tip] }

/-- The nodes' boxes at the given centres. -/
def boxesAt (g : Graph) (o : LayeredOptions) (st : Style) (centres : Array Point) :
    Array NodeBox :=
  g.nodes.mapIdx fun i nd =>
    let (w, h) := nodeSize st o nd
    let c := centres.getD i ⟨0, 0⟩
    let x0 := (c.x - w / 2).round
    let y0 := (c.y - h / 2).round
    nodeBoxOf st i nd ⟨x0, y0, x0 + w, y0 + h⟩

/-- The circular layout: the nodes on a circle in node order, the first at the top and the rest
clockwise; edges straight (parallel edges and the two directions of one pair are bent apart),
self-loops beside the node. -/
def circularLayout (g : Graph) (o : LayeredOptions := {}) (st : Style := {}) : Layout := Id.run do
  let n := g.nodes.size
  let room := g.nodes.foldl (fun s nd =>
    let (w, h) := nodeSize st o nd
    s + (w + h) / 2 + o.nodeGap) 0
  let radius := if n ≤ 1 then 0 else max 48 (room / (2 * 3.141592653589793))
  let centres : Array Point := (Array.range n).map fun i =>
    let a := -1.5707963267948966 + 2 * 3.141592653589793 * i.toFloat / n.toFloat
    ⟨radius * a.cos, radius * a.sin⟩
  let nodes := boxesAt g o st centres
  let ve := g.validEdges
  -- the edges between the same two nodes, in either direction, bend apart
  let key := fun (e : Graph.Edge) => min e.src e.dst * (n + 1) + max e.src e.dst
  let counts : Std.HashMap Nat Nat := ve.foldl (fun m (_, e) =>
    m.insert (key e) (m.getD (key e) 0 + 1)) {}
  let mut seen : Std.HashMap Nat Nat := {}
  let mut edges : Array RoutedEdge := #[]
  for (i, e) in ve do
    if e.src == e.dst then
      let box := (nodes.getD e.src default).box
      let (p, h) := loopGeometry box (g.directed && e.directed)
      let cy := (box.y0 + box.y1) / 2
      let q := min (box.height / 4) 8
      let label : Option EdgeLabel :=
        if e.label.isEmpty then none
        else
          let (w, ph) := plateSize st e.label
          some { text := e.label, box := plateAt ⟨box.x1 + 22 + w / 2, cy⟩ w ph }
      edges := edges.push
        { index := i, src := e.src, dst := e.dst, reversed := false, path := p, head := h,
          label, points := #[⟨box.x1, cy - q⟩, ⟨box.x1, cy + q⟩] }
    else
      let j := seen.getD (key e) 0
      seen := seen.insert (key e) (j + 1)
      let c := counts.getD (key e) 1
      -- the side of the bend flips with the edge's direction, so that opposite edges separate
      let sign : Float := if e.src < e.dst then 1 else -1
      let bend := sign * (j.toFloat - (c.toFloat - 1) / 2) * 26
      edges := edges.push (straightEdge st g.directed (nodes.getD e.src default)
        (nodes.getD e.dst default) bend i e)
  return ({ nodes, edges, clusters := clusterBoxes g nodes } : Layout).fit st.margin

/-- The tree layout (see the module docstring) with the tree rooted at `root` (the first node
by default). -/
def treeLayout (g : Graph) (root : Nat := 0) (o : LayeredOptions := {}) (st : Style := {}) :
    Layout := Id.run do
  let n := g.nodes.size
  let ve := g.validEdges
  let m := ve.size
  let lr := o.direction == .leftToRight
  let dims := g.nodes.map (nodeSize st o)
  let nb := dims.map fun (w, h) => if lr then h else w
  let nt := dims.map fun (w, h) => if lr then w else h
  -- breadth-first search over the undirected edges
  let mut adj : Array (Array (Nat × Nat)) := Array.replicate n #[]
  for k in [0:m] do
    let e := (ve.getD k (0, default)).2
    if e.src != e.dst then
      adj := (adj.modify e.src (·.push (e.dst, k))).modify e.dst (·.push (e.src, k))
  let mut parent : Array Nat := Array.replicate n n
  let mut parentEdge : Array Nat := Array.replicate n m
  let mut depth : Array Nat := Array.replicate n 0
  let mut visited : Array Bool := Array.replicate n false
  let mut bfs : Array Nat := #[]
  let mut roots : Array Nat := #[]
  for r in (if root < n then #[root] else #[]) ++ Array.range n do
    if !visited.getD r true then
      visited := visited.setIfInBounds r true
      roots := roots.push r
      let mut head := bfs.size
      bfs := bfs.push r
      for _ in [0:n] do
        if head ≥ bfs.size then break
        let u := bfs.getD head 0
        head := head + 1
        for (v, k) in adj.getD u #[] do
          if !visited.getD v true then
            visited := visited.setIfInBounds v true
            parent := parent.setIfInBounds v u
            parentEdge := parentEdge.setIfInBounds v k
            depth := depth.setIfInBounds v (depth.getD u 0 + 1)
            bfs := bfs.push v
  -- room of subtrees, children first
  let mut kids : Array (Array Nat) := Array.replicate n #[]
  for v in bfs do
    let p := parent.getD v n
    if p < n then kids := kids.modify p (·.push v)
  let mut room : Array Float := nb
  for v in bfs.reverse do
    let ks := kids.getD v #[]
    if !ks.isEmpty then
      let total := ks.foldl (fun s c => s + room.getD c 0) 0 + o.nodeGap * (ks.size.toFloat - 1)
      room := room.modify v (max · total)
  -- positions across: each subtree's room starts at `left`
  let mut left : Array Float := Array.replicate n 0
  let mut cursor : Float := 0
  for r in roots do
    left := left.setIfInBounds r cursor
    cursor := cursor + room.getD r 0 + 2 * o.nodeGap
  let mut centre : Array Float := Array.replicate n 0
  for v in bfs do
    let ks := kids.getD v #[]
    let total := ks.foldl (fun s c => s + room.getD c 0) 0 + o.nodeGap * (ks.size.toFloat - 1)
    centre := centre.setIfInBounds v (left.getD v 0 + room.getD v 0 / 2)
    let mut run := left.getD v 0 + (room.getD v 0 - total) / 2
    for c in ks do
      left := left.setIfInBounds c run
      run := run + room.getD c 0 + o.nodeGap
  -- levels along
  let depths := bfs.foldl (fun d v => max d (depth.getD v 0 + 1)) 0
  let mut thick : Array Float := Array.replicate depths 0
  for v in [0:n] do thick := thick.modify (depth.getD v 0) (max · (nt.getD v 0))
  let mut levels : Array Float := Array.replicate depths 0
  let mut t : Float := 0
  let mut prev : Float := 0
  for l in [0:depths] do
    let th := thick.getD l 0
    t := if l == 0 then th / 2 else t + prev / 2 + o.layerGap + th / 2
    prev := th
    levels := levels.setIfInBounds l t.round
  let across := centre.map (·.round)
  let along := (Array.range n).map fun v => levels.getD (depth.getD v 0) 0
  let frameBoxes := (Array.range n).map fun v =>
    let cb := across.getD v 0
    let lv := along.getD v 0
    (⟨cb - nb.getD v 0 / 2, lv - nt.getD v 0 / 2, cb + nb.getD v 0 / 2, lv + nt.getD v 0 / 2⟩ :
      Box)
  -- the routes: tree edges as layered edges, the others straight
  let isTree := fun (k : Nat) (e : Graph.Edge) =>
    e.src != e.dst && (parentEdge.getD e.src m == k || parentEdge.getD e.dst m == k)
  let chains : Array (Array Nat) := (Array.range m).map fun k =>
    let e := (ve.getD k (0, default)).2
    if isTree k e then
      if parentEdge.getD e.dst m == k then #[parent.getD e.dst 0, e.dst]
      else #[parent.getD e.src 0, e.src]
    else #[]
  let reversed := (Array.range m).map fun k =>
    let e := (ve.getD k (0, default)).2
    (chains.getD k #[]).getD 0 e.src != e.src
  let plates := (Array.range m).map fun k =>
    let e := (ve.getD k (0, default)).2
    let (w, h) := plateSize st e.label
    if lr then (h, w) else (w, h)
  let pl : Plan :=
    { dir := o.direction, routing := o.routing, directedGraph := g.directed,
      frameBoxes, shapes := g.nodes.map (·.shapeOf), chains, reversed, across, along,
      startOffset := Array.replicate m 0, endOffset := Array.replicate m 0, plates }
  let nodes := (g.nodes.mapIdx fun i nd =>
    nodeBoxOf st i nd (o.direction.box (frameBoxes.getD i ⟨0, 0, 0, 0⟩)))
  let edges := ve.mapIdx fun k (i, e) =>
    if isTree k e then routeOne pl k i e
    else if e.src == e.dst then
      let box := (nodes.getD e.src default).box
      let (p, h) := loopGeometry box (g.directed && e.directed)
      let cy := (box.y0 + box.y1) / 2
      let q := min (box.height / 4) 8
      let label : Option EdgeLabel :=
        if e.label.isEmpty then none
        else
          let (w, ph) := plateSize st e.label
          some { text := e.label, box := plateAt ⟨box.x1 + 22 + w / 2, cy⟩ w ph }
      { index := i, src := e.src, dst := e.dst, reversed := false, path := p, head := h, label,
        points := #[⟨box.x1, cy - q⟩, ⟨box.x1, cy + q⟩] }
    else straightEdge st g.directed (nodes.getD e.src default) (nodes.getD e.dst default) 0 i e
  return ({ nodes, edges, clusters := clusterBoxes g nodes } : Layout).fit st.margin

end PILean.Graph
