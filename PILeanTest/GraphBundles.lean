/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILeanTest.GraphQuality

/-!
# Checks of bundled routes

What `Routing.bundled` promises, checked on finished layouts (the routes' polylines, in the
picture) of the measured graphs, of the graph files, in the four directions, with clusters,
packed, and of hostile graphs (multi-edges, self-loops, cycles, a node with 200 edges in, long
chains, a complete bipartite graph, nested clusters):

* every route leaves its source at the middle of its exit side and enters its target at the
  middle of its entry side (`portProblems`);
* every segment is horizontal or vertical, and so is every straight piece of the drawn paths
  (`axisProblems`);
* no two edges share a piece of a segment, but for the trunk of a port they both use
  (`sharedProblems`);
* no route passes through or within two pixels of a node it does not end at
  (`throughProblems`);
* two parallel segments of different edges that run beside each other are at least `laneGap`
  apart, but for the edges of one trunk (`spacingProblems`);
* one arrowhead per entry port that a directed edge reaches, and no arrowhead on an edge.

Each checker comes with a planted fault that it must report. The measures (crossings, bends per
edge, total length, area) are compared with the spline routes' (`compare`, printed by
`lake exe pilean-test --bundle-measures`).
-/

namespace PILeanTest.GraphBundles

open PILean PILean.Graph

/-- The options of a bundled layout. -/
def bundled (o : LayeredOptions := {}) : LayeredOptions := { o with routing := .bundled }

/-- Where an edge leaves (`entry := false`) or enters a node's box, for the layers running in
the direction `dir` (`.topToBottom` or `.leftToRight`, mirrored when `flipped`). -/
def portOf (b : Box) (lr flipped entry : Bool) : Point :=
  let cx := (b.x0 + b.x1) / 2
  let cy := (b.y0 + b.y1) / 2
  -- the side that faces the layers before
  let before := entry != flipped
  if lr then ⟨if before then b.x0 else b.x1, cy⟩ else ⟨cx, if before then b.y0 else b.y1⟩

/-- The routes that do not start at their source's exit port or end at their target's entry
port. -/
def portProblems (l : Layout) (lr flipped : Bool) : Array String := Id.run do
  let mut out := #[]
  for e in l.edges do
    let s := (l.nodes.getD e.src default).box
    let t := (l.nodes.getD e.dst default).box
    let near := fun (p q : Point) => (p.x - q.x).abs < 0.01 && (p.y - q.y).abs < 0.01
    match e.points[0]?, e.points.back? with
    | some a, some z =>
      if !near a (portOf s lr flipped false) then out := out.push s!"edge {e.index} leaves elsewhere"
      if !near z (portOf t lr flipped true) then out := out.push s!"edge {e.index} enters elsewhere"
    | _, _ => out := out.push s!"edge {e.index} has no route"
  return out

/-- The segments of the routes and the straight pieces of the paths that are neither horizontal
nor vertical. -/
def axisProblems (l : Layout) : Array String := Id.run do
  let mut out := #[]
  for e in l.edges do
    for i in [1:e.points.size] do
      let a := e.points.getD (i - 1) ⟨0, 0⟩
      let b := e.points.getD i ⟨0, 0⟩
      if a.x != b.x && a.y != b.y then out := out.push s!"edge {e.index}: slanted segment {i}"
    let mut cur : Point := ⟨0, 0⟩
    for c in e.path.cmds do
      match c with
      | .move p => cur := p
      | .line p =>
        if (p.x - cur.x).abs > 1e-6 && (p.y - cur.y).abs > 1e-6 then
          out := out.push s!"edge {e.index}: slanted line"
        cur := p
      | .quad _ p => cur := p
      | .cubic _ _ p => cur := p
      | .close => pure ()
  return out

/-- An axis segment: whether it is vertical, its line (`x` or `y`), its extent along the line,
and its edge. -/
structure AxisSeg where
  /-- Whether the segment is vertical. -/
  vertical : Bool
  /-- Its line: `x` of a vertical segment, `y` of a horizontal one. -/
  line : Float
  /-- The lower end along the line. -/
  lo : Float
  /-- The upper end along the line. -/
  hi : Float
  /-- The position of its edge in the layout. -/
  edge : Nat
  deriving Inhabited

/-- The axis segments of every route. -/
def segments (l : Layout) : Array AxisSeg := Id.run do
  let mut out := #[]
  for e in l.edges, k in [0:l.edges.size] do
    for i in [1:e.points.size] do
      let a := e.points.getD (i - 1) ⟨0, 0⟩
      let b := e.points.getD i ⟨0, 0⟩
      if a.x == b.x && a.y != b.y then
        out := out.push { vertical := true, line := a.x, lo := min a.y b.y, hi := max a.y b.y,
                          edge := k }
      else if a.y == b.y && a.x != b.x then
        out := out.push { vertical := false, line := a.y, lo := min a.x b.x, hi := max a.x b.x,
                          edge := k }
  return out

/-- Whether the stretch `(lo, hi)` of the line `x` lies on the trunk of a port that both edges
use (an exit trunk when they share their source, an entry trunk when they share their
target). -/
def onSharedTrunk (l : Layout) (a b : RoutedEdge) (vertical : Bool) (line lo hi : Float) :
    Bool :=
  l.ports.any fun p =>
    let shares := if p.entry then a.dst == p.node && b.dst == p.node
      else a.src == p.node && b.src == p.node
    let (u, v) := p.trunk
    let tv := u.x == v.x
    shares && tv == vertical &&
      (if vertical then u.x == line && min u.y v.y - 0.01 ≤ lo && hi ≤ max u.y v.y + 0.01
       else u.y == line && min u.x v.x - 0.01 ≤ lo && hi ≤ max u.x v.x + 0.01)

/-- The pairs of edges that share a piece of a segment (longer than a hundredth of a pixel) off
the trunks of their common ports: segments on one line sorted along it, each compared with the
later ones that start before it ends. -/
def sharedProblems (l : Layout) : Array String := Id.run do
  let segs := (segments l).qsort fun s t =>
    (!s.vertical && t.vertical) || (s.vertical == t.vertical && (s.line < t.line ||
      (s.line == t.line && s.lo < t.lo)))
  let mut out := #[]
  for i in [0:segs.size] do
    let s := segs.getD i default
    for j in [i + 1:segs.size] do
      let t := segs.getD j default
      if t.vertical != s.vertical || t.line != s.line || t.lo ≥ s.hi - 0.01 then break
      if t.edge == s.edge then continue
      let lo := max s.lo t.lo
      let hi := min s.hi t.hi
      if hi - lo > 0.01 then
        let a := l.edges.getD s.edge default
        let b := l.edges.getD t.edge default
        if !onSharedTrunk l a b s.vertical s.line lo hi then
          out := out.push s!"edges {a.index} and {b.index} share a segment at {s.line}"
  return out

/-- The routes that pass through or within `margin` of the box of a node they do not end at
(their own ends are left out). -/
def throughProblems (l : Layout) (margin : Float := 2) : Array String := Id.run do
  let mut out := #[]
  for e in l.edges do
    for i in [1:e.points.size] do
      let a := e.points.getD (i - 1) ⟨0, 0⟩
      let b := e.points.getD i ⟨0, 0⟩
      for nb in l.nodes do
        if nb.index == e.src || nb.index == e.dst then continue
        if segmentHitsBox a b (nb.box.inset (-margin) (-margin) (-margin) (-margin)) then
          out := out.push s!"edge {e.index} passes node {nb.index}"
  return out

/-- The pairs of parallel segments of different edges that run beside each other closer than
`gap` (and not on one line, which `sharedProblems` reports), except two edges of one trunk
(they leave or join it at their own corners). -/
def spacingProblems (l : Layout) (gap : Float) : Array String := Id.run do
  let segs := (segments l).qsort fun s t =>
    (!s.vertical && t.vertical) || (s.vertical == t.vertical && s.line < t.line)
  let mut out := #[]
  for i in [0:segs.size] do
    let s := segs.getD i default
    for j in [i + 1:segs.size] do
      let t := segs.getD j default
      if t.vertical != s.vertical || t.line - s.line ≥ gap - 0.01 then break
      if t.edge == s.edge || t.line == s.line then continue
      if min s.hi t.hi - max s.lo t.lo > 0.01 then
        let a := l.edges.getD s.edge default
        let b := l.edges.getD t.edge default
        out := out.push s!"edges {a.index} and {b.index} run {t.line - s.line} apart"
  return out

/-- The arrowheads: edges that carry one, and entry ports that a directed edge reaches without
one or that have more than one. -/
def headProblems (g : Graph) (l : Layout) : Array String := Id.run do
  let mut out := #[]
  for e in l.edges do
    if e.head.isSome then out := out.push s!"edge {e.index} has its own arrowhead"
  let mut wants : Array Bool := Array.replicate g.nodes.size false
  for (_, e) in g.validEdges do
    if g.directed && e.directed then wants := wants.setIfInBounds e.dst true
  for v in [0:g.nodes.size] do
    let heads := (l.ports.filter fun p => p.node == v && p.entry && p.head.isSome).size
    if wants.getD v false && heads != 1 then out := out.push s!"node {v} has {heads} arrowheads"
    if !wants.getD v false && heads != 0 then out := out.push s!"node {v} has an arrowhead"
  return out

/-- Every problem of a bundled layout of `g`, for layers in the direction of `lr`, mirrored when
`flipped`. -/
def problems (g : Graph) (l : Layout) (lr flipped : Bool) (gap : Float) : Array String :=
  portProblems l lr flipped ++ axisProblems l ++ sharedProblems l ++ throughProblems l ++
    spacingProblems l gap ++ headProblems g l

/-- A route's corners: its points between the ends where it turns. -/
def bends (e : RoutedEdge) : Nat := e.points.size - 2

/-- The number of pairs of edges, not sharing a node, whose routes (as polylines: the full
routes from port to port) cross. -/
def routeCrossings (l : Layout) : Nat :=
  GraphQuality.crossingPairs
    { l with edges := l.edges.map fun e =>
        { e with path := e.points.foldl (fun (p : Path) q => if p.cmds.isEmpty then p.moveTo q
          else p.lineTo q) {} } }

/-- The total length of the routes (as polylines). -/
def routeLength (l : Layout) : Float :=
  l.edges.foldl (init := 0) fun acc e =>
    (Array.range (e.points.size - 1)).foldl (init := acc) fun s j =>
      s + (e.points.getD j ⟨0, 0⟩).dist (e.points.getD (j + 1) ⟨0, 0⟩)

/-- The pairs of edges whose routes cross more than once. -/
def multipleCrossings (l : Layout) : Nat := Id.run do
  let segs := segments l
  let mut count : Std.HashMap (Nat × Nat) Nat := {}
  let vs := segs.filter (·.vertical)
  let hs := segs.filter (!·.vertical)
  for v in vs do
    for h in hs do
      if v.edge == h.edge then continue
      if h.lo < v.line && v.line < h.hi && v.lo < h.line && h.line < v.hi then
        let a := l.edges.getD v.edge default
        let b := l.edges.getD h.edge default
        if a.src == b.src || a.dst == b.dst || a.src == b.dst || a.dst == b.src then continue
        let key := (min v.edge h.edge, max v.edge h.edge)
        count := count.insert key (count.getD key 0 + 1)
  return count.fold (fun n _ c => if c > 1 then n + 1 else n) 0

end PILeanTest.GraphBundles

namespace PILeanTest.GraphBundles
open PILean PILean.Graph

/-- The lengths of the short horizontal runs of the routes (the jogs shorter than `limit`). -/
def shortRuns (l : Layout) (limit : Float) : Array (Nat × Float) := Id.run do
  let mut out := #[]
  for e in l.edges do
    for i in [1:e.points.size] do
      let a := e.points.getD (i - 1) ⟨0, 0⟩
      let b := e.points.getD i ⟨0, 0⟩
      if a.y == b.y && (a.x - b.x).abs < limit && i > 1 && i + 1 < e.points.size then
        out := out.push (e.index, (a.x - b.x).abs)
  return out

/-- The routes that enter the box of a cluster that holds neither of their ends. -/
def foreignClusterEntries (g : Graph) (l : Layout) : Nat := Id.run do
  let t := ClusterTree.of g
  let mut count := 0
  for e in l.edges do
    let cs := t.nodeCluster.getD e.src none
    let cd := t.nodeCluster.getD e.dst none
    let mut entered := false
    for cb in l.clusters do
      if t.holdsOpt cb.index cs || t.holdsOpt cb.index cd then continue
      for i in [1:e.points.size] do
        if segmentHitsBox (e.points.getD (i - 1) ⟨0, 0⟩) (e.points.getD i ⟨0, 0⟩)
            (cb.box.inset 1 1 1 1) then entered := true
    if entered then count := count + 1
  return count

/-- A graph of `n` nodes with the edges given. -/
def ofEdges (n : Nat) (edges : List (Nat × Nat)) (labels : Bool := false) : Graph :=
  { nodes := (Array.range n).map fun v => { label := s!"n{v}" },
    edges := edges.toArray.map fun (a, b) =>
      { src := a, dst := b, label := if labels && a % 3 == 0 then s!"e{a}" else "" } }

/-- Graphs that try to break the promises of bundled routes. -/
def hostile : Array (String × Graph) :=
  #[("multi-edges", ofEdges 4 [(0, 1), (0, 1), (0, 1), (0, 2), (0, 2), (1, 3), (1, 3), (2, 3)]),
    ("self-loops", ofEdges 3 [(0, 0), (0, 0), (0, 1), (1, 1), (1, 2), (2, 2), (2, 0)]),
    ("labelled", ofEdges 6 [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4), (0, 4), (4, 5), (3, 3), (5, 0)]
      (labels := true)),
    ("cycles", ofEdges 7 [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 1), (4, 5), (5, 6), (6, 0),
      (6, 3), (1, 0)]),
    ("fan-in 200", ofEdges 201 ((List.range 200).map fun i => (i + 1, 0))),
    ("fan-out 200", ofEdges 201 ((List.range 200).map fun i => (0, i + 1))),
    ("fan-in and out 60", ofEdges 121 ((List.range 60).map (fun i => (i + 1, 0)) ++
      (List.range 60).map fun i => (0, i + 61))),
    ("chain 150 with shortcuts", ofEdges 150 ((List.range 149).map (fun i => (i, i + 1)) ++
      (List.range 30).map fun i => (5 * i, min 149 (5 * i + 7 + i % 11)))),
    ("complete bipartite 8", ofEdges 16 ((List.range 64).map fun i => (i / 8, 8 + i % 8))),
    ("complete bipartite 3 layers", ofEdges 18 ((List.range 36).map (fun i => (i / 6, 6 + i % 6)) ++
      (List.range 36).map fun i => (6 + i / 6, 12 + i % 6))),
    ("long and short", ofEdges 12 ((List.range 11).map (fun i => (i, i + 1)) ++
      [(0, 11), (0, 10), (1, 11), (0, 6), (2, 9), (3, 11), (0, 11)])),
    ("nested clusters", { GraphQuality.awkwardClusters with
      clusters := GraphQuality.awkwardClusters.clusters.push
        { name := "Deep", members := #[1], parent := some 2 } }),
    ("undirected", { ofEdges 6 [(0, 1), (1, 2), (2, 0), (3, 4), (0, 0)] with directed := false })]

/-- Every problem of the bundled layouts of `g`: from the top down, from left to right, both
mirrored, and packed. -/
def allProblems (g : Graph) (st : BundleStyle := {}) : Array String :=
  let o : LayeredOptions := { routing := .bundled, bundle := st }
  let tb := g.layout o
  let lr := g.layout { o with direction := .leftToRight }
  problems g tb false false st.laneGap ++ problems g lr true false st.laneGap ++
    problems g (tb.mirror true) false true st.laneGap ++
    problems g (lr.mirror false) true true st.laneGap ++
    problems g (g.layoutPacked o) false false st.laneGap

/-- The checks of bundled routes (see the module docstring), on hostile graphs and with planted
faults. -/
def checks : Array (String × Bool) := Id.run do
  let mut out : Array (String × Bool) := #[]
  for (name, g) in hostile do
    let ps := allProblems g
    out := out.push (s!"bundled {name}: ports, axes, no shared segment, no node passed, \
      lanes apart, one arrowhead per entry port{if ps.isEmpty then "" else s!" ({ps[0]!})"}",
      ps.isEmpty)
    let l := g.layout (bundled {})
    out := out.push (s!"bundled {name}: the same drawing twice and finite numbers",
      l.toSvg {} == (g.layout (bundled {})).toSvg {} && Graphs.finite l)
  -- planted faults
  let g := ofEdges 4 [(0, 1), (0, 2), (1, 3), (2, 3)]
  let l := g.layout (bundled {})
  let moved := { l with edges := l.edges.modify 0 fun e =>
    { e with points := e.points.modify 0 fun p => ⟨p.x + 5, p.y⟩ } }
  let slanted := { l with edges := l.edges.modify 1 fun e =>
    { e with points := e.points.modify 1 fun p => ⟨p.x + 3, p.y + 2⟩ } }
  let copy : RoutedEdge := { l.edges[2]! with index := 9, src := 7, dst := 8 }
  let doubled := { l with edges := l.edges.push copy }
  -- edge 0 joins nodes 0 and 1; its route is sent down through the middle of node 3
  let b3 := l.nodes[3]!.box
  let through := { l with edges := l.edges.modify 0 fun e =>
    { e with points := #[e.points[0]!, ⟨(b3.x0 + b3.x1) / 2, e.points[0]!.y⟩,
      ⟨(b3.x0 + b3.x1) / 2, (b3.y0 + b3.y1) / 2⟩] } }
  let beside : RoutedEdge := { copy with points := copy.points.map fun p => ⟨p.x + 2, p.y⟩ }
  let near := { l with edges := l.edges.push beside }
  let twoHeads := { l with edges := l.edges.modify 0 fun e => { e with head := some {} } }
  out := out ++ #[
    ("bundled checker: a route that leaves elsewhere is reported",
      !(portProblems moved false false).isEmpty),
    ("bundled checker: a slanted segment is reported", !(axisProblems slanted).isEmpty),
    ("bundled checker: two edges on one segment are reported", !(sharedProblems doubled).isEmpty),
    ("bundled checker: a route through a node is reported", !(throughProblems through).isEmpty),
    ("bundled checker: lanes too close are reported", !(spacingProblems near 6).isEmpty),
    ("bundled checker: an arrowhead on an edge is reported", !(headProblems g twoHeads).isEmpty),
    ("bundled checker: the unchanged layout has no problem", (problems g l false false 6).isEmpty)]
  -- the tracks of a channel: overlapping runs never share a track
  let runs : Array RunSpec := #[⟨⟨0, .up, some 0⟩, ⟨40, .down, some 1⟩⟩,
    ⟨⟨0, .up, some 0⟩, ⟨20, .down, some 3⟩⟩, ⟨⟨40, .up, some 2⟩, ⟨0, .down, some 5⟩⟩,
    ⟨⟨100, .up, some 4⟩, ⟨120, .down, some 7⟩⟩]
  let (placed, depth) := placeRuns runs 6 12
  out := out.push ("bundled channel: a cycle of two runs is broken by a jog, nested runs apart",
    depth ≥ 3 && placed.any (fun p => match p with | .jog _ _ _ => true | _ => false))
  return out

/-- The measures of a layout's routes: crossings, total length (pixels), area (square pixels),
the mean number of bends of an edge, the jogs narrower than a lane, the pairs of edges that cross
more than once, and the edges that enter a cluster holding neither of their ends. For a spline
layout the curves are measured, for a bundled one the routes. -/
structure RouteMeasures where
  /-- Pairs of edges, not sharing a node, that cross. -/
  crossings : Nat
  /-- Total length. -/
  length : Float
  /-- The area of the box around everything. -/
  area : Float
  /-- The mean number of bends of an edge. -/
  bends : Float
  /-- Horizontal runs between two bends narrower than `laneGap`. -/
  narrowJogs : Nat
  /-- Pairs of edges whose routes cross more than once. -/
  multiple : Nat
  /-- Edges that enter a cluster holding neither of their ends. -/
  foreign : Nat

/-- The measures of a bundled layout. -/
def measureBundled (g : Graph) (l : Layout) (laneGap : Float) (pairs : Bool := true) :
    RouteMeasures :=
  { crossings := routeCrossings l, length := routeLength l, area := GraphQuality.area l,
    bends := (l.edges.foldl (fun n e => n + bends e) 0).toFloat / max 1 l.edges.size.toFloat,
    narrowJogs := (shortRuns l laneGap).size,
    multiple := if pairs then multipleCrossings l else 0,
    foreign := foreignClusterEntries g l }

/-- Prints the measures of the spline and the bundled layouts of the measured graphs and the
graph files (with the style `st`), and the problems of the bundled ones. -/
def printMeasures (st : BundleStyle := {}) (names : List String := []) : IO Unit := do
  let files ← GraphQuality.fileGraphs ("PILeanTest" / "graphs")
  IO.println "graph                      ms(s/b)   crossings(s/b)   length(s/b)        area(s/b, Mpx2)  bends  narrow  twice  foreign(s/b) problems"
  for (name, g) in GraphQuality.graphs ++ files do
    if (!names.isEmpty && !names.contains name) || (names.isEmpty && GraphQuality.slowGraphs.contains name) then continue
    let t0 ← IO.monoNanosNow
    let ls ← IO.lazyPure fun _ => g.layout {}
    let t1 ← IO.monoNanosNow
    let lb ← IO.lazyPure fun _ => g.layout { routing := .bundled, bundle := st }
    let t2 ← IO.monoNanosNow
    let small := g.edges.size ≤ 1000
    let m := measureBundled g lb st.laneGap small
    let ps := if small then problems g lb false false st.laneGap else #[]
    let foreignS := (clearanceProblems g ls).filter (Graphs.has · "enters cluster") |>.size
    IO.println s!"{name}  {(t1 - t0) / 1000000}/{(t2 - t1) / 1000000}  {GraphQuality.crossingPairs ls}/{m.crossings}  \
      {(GraphQuality.edgeLength ls).round}/{m.length.round}  \
      {fmtNum (GraphQuality.area ls / 1e6) 2}/{fmtNum (m.area / 1e6) 2}  {fmtNum m.bends 2}  {m.narrowJogs}  {m.multiple}  \
      {foreignS}/{m.foreign}  {ps.size}"
    for p in ps.extract 0 4 do IO.println s!"  {p}"

/-- Writes the spline and the bundled drawing of the graphs of `PILeanTest/graphs` and of the
measured graphs to `dir` as SVG and prints their measures and problems. -/
def writeSamples (dir : String) (names : List String := []) : IO Unit := do
  IO.FS.createDirAll dir
  let files ← GraphQuality.fileGraphs ("PILeanTest" / "graphs")
  for (name, g) in GraphQuality.graphs ++ files do
    if !names.isEmpty && !names.contains name then continue
    let t0 ← IO.monoNanosNow
    let lb ← IO.lazyPure fun _ => g.layout (bundled {})
    let ms ← Graphs.msSince t0
    let ls := g.layout {}
    IO.FS.writeFile s!"{dir}/{name}-spline.svg" (ls.toSvg {})
    IO.FS.writeFile s!"{dir}/{name}-bundled.svg" (lb.toSvg {})
    if g.nodes.size ≤ 200 then
      IO.FS.writeBinFile s!"{dir}/{name}-bundled.png" ((lb.toImage {} 2).writePng.toOption.getD .empty)
      IO.FS.writeBinFile s!"{dir}/{name}-spline.png" ((ls.toImage {} 2).writePng.toOption.getD .empty)
    let ps := problems g lb false false 6
    let bendsMean := (lb.edges.foldl (fun n e => n + bends e) 0).toFloat / max 1 lb.edges.size.toFloat
    IO.println s!"{name}: {ms} ms, crossings {GraphQuality.crossingPairs ls} spline / \
      {routeCrossings lb} bundled, length {GraphQuality.edgeLength ls} / {routeLength lb}, \
      area {GraphQuality.area ls} / {GraphQuality.area lb}, bends {bendsMean}, \
      problems {ps.size}"
    for p in ps.extract 0 8 do IO.println s!"  {p}"
    IO.println s!"  short runs: {shortRuns lb 12}"

end PILeanTest.GraphBundles
