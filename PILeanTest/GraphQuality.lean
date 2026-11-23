/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILeanTest.Graphs

/-!
# The quality of the layered layout

Measures of a drawing that do not depend on the eye, computed from the finished `Layout`: the
pairs of edges that cross (edges sharing a node not counted; the edges flattened to polylines),
the total length of the edges, the area of the drawing, the violations of the cluster rules
(`clusterProblems`) and of the edges' clearance (`clearanceProblems`), and the time taken; and
measures of what the eye objects to (`eye`): how much an edge turns and how often it changes
from bending one way to bending the other, how much of the edges runs outside the box around
the nodes, how near an edge comes to a node it does not end at, and whether an edge turns back
across the layers.

* `graphs`: the measured graphs: the two import graphs, two blueprint dependency graphs without
  clusters, by chapter and (the first) by chapter and section, module graphs of 800 and 3000
  nodes, random dense and sparse acyclic graphs, a tree and a long chain with shortcuts.
* `report` (`lake exe pilean-test --graph-quality [DIR]`): a table of the measures; with `DIR`,
  also `NAME.dot` (the graph with PILean's node sizes and gaps and its clusters as nested
  `cluster` subgraphs), `NAME.layout` and `NAME.time` for `tools/graph-compare.py`, which
  compares with Graphviz's `dot` when it is installed.
* `checks`: bounds on the measures that fail when the quality slips, and no violation of the
  cluster or clearance rules on any graph; they need no `dot`.
-/

namespace PILeanTest.GraphQuality

open PILean PILean.Graph

/-- A label of `n` letters (the names of the anonymised graphs are gone; their lengths are
kept). -/
def letters (n : Nat) : String := String.ofList (List.replicate (max 1 n) 'x')

/-- A blueprint's dependency graph from the anonymised fixture: `clusters` `0` for none, `1` for
one cluster per chapter, `2` for chapters with their sections inside (a chapter with one section
gets no section cluster). -/
def blueprint (nodes : Array (Nat × Nat × Nat)) (edges : Array (Nat × Nat))
    (sections : Array Nat) (clusters : Nat) : Graph := Id.run do
  let g : Graph := { nodes := nodes.map fun (len, _, _) => { label := letters len },
                     edges := edges.map fun (a, b) => { src := a, dst := b } }
  if clusters == 0 then return g
  let chapters := nodes.foldl (fun m (_, c, _) => max m (c + 1)) 0
  let mut cs : Array Cluster := (Array.range chapters).map fun c =>
    { name := s!"Chapter {c + 1}",
      members := (Array.range nodes.size).filter fun v => (nodes.getD v (0, 0, 0)).2.1 == c }
  if clusters ≥ 2 then
    for s in [0:sections.size] do
      let c := sections.getD s 0
      let siblings := (sections.filter (· == c)).size
      if siblings ≥ 2 then
        let ms := (Array.range nodes.size).filter fun v => (nodes.getD v (0, 0, 0)).2.2 == s
        let title := s!"Section {c + 1}.{s + 1}"
        cs := cs.push { name := title, parent := some c, members := ms }
  return { g with clusters := cs }

/-- A random acyclic graph of `n` nodes and about `m` edges from a fixed generator, each edge
from a node to one at most `reach` places later in a random order. -/
def randomDag (seed n m reach : Nat) : Graph := Id.run do
  let mut s : UInt64 := seed.toUInt64 * 2654435761 + 7
  let mut edges : Array Graph.Edge := #[]
  let mut seen : Std.HashSet (Nat × Nat) := {}
  for _ in [0:m] do
    let (s1, r1) := Graphs.next s
    let (s2, r2) := Graphs.next s1
    s := s2
    let a := r1 % n
    let b := a + 1 + r2 % (max 1 reach)
    if b < n && !seen.contains (a, b) then
      seen := seen.insert (a, b)
      edges := edges.push { src := a, dst := b }
  return { nodes := (Array.range n).map fun v => { label := s!"v{v}" }, edges }

/-- A complete binary tree of `n` nodes. -/
def tree (n : Nat) : Graph :=
  Graph.ofPairs ((List.range n).filterMap fun v => if v == 0 then none else some ((v - 1) / 2, v))

/-- A chain of `n` nodes with a shortcut over three nodes every fourth node. -/
def chain (n : Nat) : Graph :=
  Graph.ofPairs ((List.range (n - 1)).map (fun v => (v, v + 1)) ++
    ((List.range (n - 3)).filter (· % 4 == 0)).map fun v => (v, v + 3))

/-- The measured graphs, by name. -/
def graphs : Array (String × Graph) :=
  #[("own-imports", Graph.ofLabelled Fixtures.ownImports.toList),
    ("project-imports", Graph.ofLabelled Fixtures.projectImports.toList),
    ("blueprint-a", blueprint Fixtures.blueprintANodes Fixtures.blueprintAEdges
      Fixtures.blueprintASections 0),
    ("blueprint-a-chapters", blueprint Fixtures.blueprintANodes Fixtures.blueprintAEdges
      Fixtures.blueprintASections 1),
    ("blueprint-a-nested", blueprint Fixtures.blueprintANodes Fixtures.blueprintAEdges
      Fixtures.blueprintASections 2),
    ("blueprint-b", blueprint Fixtures.blueprintBNodes Fixtures.blueprintBEdges
      Fixtures.blueprintBSections 0),
    ("blueprint-b-chapters", blueprint Fixtures.blueprintBNodes Fixtures.blueprintBEdges
      Fixtures.blueprintBSections 1),
    ("module-800", Graphs.moduleGraph 1 800), ("module-3000", Graphs.moduleGraph 1 3000),
    ("dense-dag", randomDag 3 120 480 12), ("sparse-dag", randomDag 5 300 360 40),
    ("tree", tree 127), ("chain", chain 80)]

/-- The points of an edge's path, flattened. -/
def edgePoints (e : RoutedEdge) : Array Point :=
  (e.path.flatten 0.5).foldl (fun acc pl => acc ++ pl.points) #[]

/-- Whether the segments `ab` and `cd` properly cross. -/
def segmentsCross (a b c d : Point) : Bool :=
  let ccw := fun (p q r : Point) => (r.y - p.y) * (q.x - p.x) - (q.y - p.y) * (r.x - p.x)
  ((ccw a c d > 0) != (ccw b c d > 0)) && ((ccw a b c > 0) != (ccw a b d > 0))

/-- The number of pairs of edges, not sharing a node, whose polylines cross (segments bucketed
on a grid of 64 pixels, as `tools/graph-compare.py` counts them). -/
def crossingPairs (l : Layout) : Nat := Id.run do
  let cell : Float := 64
  let idx := fun (f : Float) => (f / cell).floor.toInt64.toInt.toNat
  let mut segs : Array (Nat × Point × Point) := #[]
  let mut grid : Std.HashMap (Nat × Nat) (Array Nat) := {}
  for k in [0:l.edges.size] do
    let pts := edgePoints (l.edges.getD k default)
    for j in [1:pts.size] do
      let a := pts.getD (j - 1) ⟨0, 0⟩
      let b := pts.getD j ⟨0, 0⟩
      let s := segs.size
      segs := segs.push (k, a, b)
      for cx in [idx (min a.x b.x):idx (max a.x b.x) + 1] do
        for cy in [idx (min a.y b.y):idx (max a.y b.y) + 1] do
          grid := grid.insert (cx, cy) ((grid.getD (cx, cy) #[]).push s)
  let mut pairs : Std.HashSet (Nat × Nat) := {}
  for (_, members) in grid.toList do
    for i in [0:members.size] do
      for j in [i + 1:members.size] do
        let (kp, a, b) := segs.getD (members.getD i 0) (0, ⟨0, 0⟩, ⟨0, 0⟩)
        let (kq, c, d) := segs.getD (members.getD j 0) (0, ⟨0, 0⟩, ⟨0, 0⟩)
        if kp == kq then continue
        let key := (min kp kq, max kp kq)
        if pairs.contains key then continue
        let ep := l.edges.getD kp default
        let eq := l.edges.getD kq default
        if ep.src == eq.src || ep.src == eq.dst || ep.dst == eq.src || ep.dst == eq.dst then
          continue
        if segmentsCross a b c d then pairs := pairs.insert key
  return pairs.size

/-- The total length of the edges' polylines. -/
def edgeLength (l : Layout) : Float :=
  l.edges.foldl (init := 0) fun acc e =>
    let pts := edgePoints e
    (Array.range (pts.size - 1)).foldl (init := acc) fun s j =>
      let a := pts.getD j ⟨0, 0⟩
      let b := pts.getD (j + 1) ⟨0, 0⟩
      s + ((b.x - a.x) ^ 2 + (b.y - a.y) ^ 2).sqrt

/-- The area of the box around the nodes, the clusters and the edges' polylines. -/
def area (l : Layout) : Float := Id.run do
  let mut lo : Point := ⟨1e300, 1e300⟩
  let mut hi : Point := ⟨-1e300, -1e300⟩
  for b in l.nodes.map (·.box) ++ l.clusters.map (·.box) do
    lo := ⟨min lo.x b.x0, min lo.y b.y0⟩
    hi := ⟨max hi.x b.x1, max hi.y b.y1⟩
  for e in l.edges do
    for p in edgePoints e do
      lo := ⟨min lo.x p.x, min lo.y p.y⟩
      hi := ⟨max hi.x p.x, max hi.y p.y⟩
  return if hi.x < lo.x then 0 else (hi.x - lo.x) * (hi.y - lo.y)

/-- The signed turning angles (degrees) at the inner points of a polyline. -/
def turns (pts : Array Point) : Array Float := Id.run do
  let mut out : Array Float := #[]
  let mut prev : Option Point := none
  for j in [1:pts.size] do
    let d := pts.getD j ⟨0, 0⟩ - pts.getD (j - 1) ⟨0, 0⟩
    if d.x * d.x + d.y * d.y < 1e-12 then continue
    if let some p := prev then
      out := out.push
        (Float.atan2 (p.x * d.y - p.y * d.x) (p.x * d.x + p.y * d.y) * 180 / 3.141592653589793)
    prev := some d
  return out

/-- How often a polyline changes from bending one way to bending the other, given its turning
angles; a bend counts when it turns by `least` degrees or more in all. -/
def inflections (angles : Array Float) (least : Float := 5) : Nat := Id.run do
  let mut bends := 0
  let mut sign : Int := 0
  let mut total : Float := 0
  for a in angles do
    let s : Int := if a > 0 then 1 else if a < 0 then -1 else 0
    if s == 0 then continue
    if s != sign then
      if total ≥ least then bends := bends + 1
      sign := s
      total := 0
    total := total + a.abs
  if total ≥ least then bends := bends + 1
  return bends - 1

/-- The length of the part of the segment `ab` inside the box (Liang and Barsky). -/
def insideLength (a b : Point) (box : Box) : Float := Id.run do
  let dx := b.x - a.x
  let dy := b.y - a.y
  let mut t0 : Float := 0
  let mut t1 : Float := 1
  for (p, q) in
      [(-dx, a.x - box.x0), (dx, box.x1 - a.x), (-dy, a.y - box.y0), (dy, box.y1 - a.y)] do
    if p == 0 then
      if q < 0 then return 0
    else
      let r := q / p
      if p < 0 then t0 := max t0 r else t1 := min t1 r
  return max 0 (t1 - t0) * (dx * dx + dy * dy).sqrt

/-- The distance between the segment `ab` and the box (`0` when they meet). -/
def segmentBoxDistance (a b : Point) (box : Box) : Float :=
  if segmentHitsBox a b box then 0
  else
    let pointSegment := fun (p c d : Point) =>
      let v := d - c
      let l2 := v.x * v.x + v.y * v.y
      let t := if l2 == 0 then 0 else max 0 (min 1 (((p.x - c.x) * v.x + (p.y - c.y) * v.y) / l2))
      (p - (c + t * v)).norm
    let pointBox := fun (p : Point) =>
      (⟨max (max (box.x0 - p.x) 0) (p.x - box.x1), max (max (box.y0 - p.y) 0) (p.y - box.y1)⟩ :
        Point).norm
    let corners : List Point :=
      [⟨box.x0, box.y0⟩, ⟨box.x1, box.y0⟩, ⟨box.x1, box.y1⟩, ⟨box.x0, box.y1⟩]
    corners.foldl (fun m c => min m (pointSegment c a b)) (min (pointBox a) (pointBox b))

/-- What the eye objects to in a drawing. -/
structure Eye where
  /-- The mean turning of an edge, in degrees: the sum of the angles by which it changes
  direction. -/
  turning : Float
  /-- The mean number of times an edge changes from bending one way to bending the other. -/
  inflections : Float
  /-- The length of the edges outside the box around the nodes (pixels). -/
  outside : Float
  /-- The least distance between an edge and a node it does not end at (pixels), looked for up
  to `reach`. -/
  nearest : Float
  /-- The edges that at some point run against the direction they began in, along the first
  (`true`) or the second coordinate: an edge of a layered drawing never turns back across the
  layers. -/
  turnedBack : Bool → Nat

/-- How far from an edge a node is looked for by `eye`. -/
def reach : Float := 64

/-- The measures of what the eye objects to, as `tools/graph-compare.py` computes them for
Graphviz's drawings (nodes bucketed on a grid of 64 pixels). -/
def eye (l : Layout) : Eye := Id.run do
  let none_ : Eye := { turning := 0, inflections := 0, outside := 0, nearest := reach,
                       turnedBack := fun _ => 0 }
  if l.nodes.isEmpty || l.edges.isEmpty then return none_
  let hull := l.nodes.foldl (fun b n => b.union n.box) (l.nodes.getD 0 default).box
  let cell : Float := 64
  let idx := fun (f : Float) => (f / cell).floor.toInt64.toInt
  let mut grid : Std.HashMap (Int × Int) (Array Nat) := {}
  for n in l.nodes do
    for cx in [0:(idx (n.box.x1 + reach) - idx (n.box.x0 - reach) + 1).toNat] do
      for cy in [0:(idx (n.box.y1 + reach) - idx (n.box.y0 - reach) + 1).toNat] do
        let key := (idx (n.box.x0 - reach) + cx, idx (n.box.y0 - reach) + cy)
        grid := grid.insert key ((grid.getD key #[]).push n.index)
  let mut turning : Float := 0
  let mut bends := 0
  let mut outside : Float := 0
  let mut nearest := reach
  let mut backX := 0
  let mut backY := 0
  for e in l.edges do
    let pts := edgePoints e
    let angles := turns pts
    turning := angles.foldl (fun s a => s + a.abs) turning
    bends := bends + inflections angles
    let first := pts.getD 0 ⟨0, 0⟩
    let last := pts.getD (pts.size - 1) ⟨0, 0⟩
    let mut bx := false
    let mut by_ := false
    for j in [1:pts.size] do
      let a := pts.getD (j - 1) ⟨0, 0⟩
      let b := pts.getD j ⟨0, 0⟩
      outside := outside + a.dist b - insideLength a b hull
      if (b.x - a.x) * (last.x - first.x) < -1e-6 then bx := true
      if (b.y - a.y) * (last.y - first.y) < -1e-6 then by_ := true
      if e.src == e.dst then continue
      let mut seen : Array Nat := #[]
      for cx in [0:(idx (max a.x b.x) - idx (min a.x b.x) + 1).toNat] do
        for cy in [0:(idx (max a.y b.y) - idx (min a.y b.y) + 1).toNat] do
          for i in grid.getD (idx (min a.x b.x) + cx, idx (min a.y b.y) + cy) #[] do
            if i != e.src && i != e.dst && !seen.contains i then
              seen := seen.push i
              nearest := min nearest (segmentBoxDistance a b (l.nodes.getD i default).box)
    if bx && e.src != e.dst then backX := backX + 1
    if by_ && e.src != e.dst then backY := backY + 1
  let count := l.edges.size.toFloat
  return { turning := turning / count, inflections := bends.toFloat / count, outside, nearest,
           turnedBack := fun x => if x then backX else backY }

/-- The measures of one layout. -/
structure Measures where
  /-- Crossing pairs of edges. -/
  crossings : Nat
  /-- Total edge length (pixels). -/
  length : Float
  /-- Area (square pixels). -/
  area : Float
  /-- Violations of the cluster rules. -/
  clusterViolations : Nat
  /-- Edges that pass a node they do not end at. -/
  clearanceViolations : Nat
  /-- Edges that enter a cluster holding neither of their ends. -/
  clusterEntries : Nat

/-- The measures of the default layout of `g`. -/
def measure (g : Graph) (l : Layout) : Measures :=
  { crossings := crossingPairs l, length := edgeLength l, area := area l,
    clusterViolations := (clusterProblems g l).size,
    clearanceViolations := ((clearanceProblems g l).filter (Graphs.has · "passes node")).size,
    clusterEntries := ((clearanceProblems g l).filter (Graphs.has · "enters cluster")).size }

/-- The Graphviz input for a graph with its clusters, with the same node sizes and gaps as the
layout (`Graphs.dotText` with `cluster` subgraphs, nested as the clusters are). -/
def dotText (g : Graph) (o : LayeredOptions) (st : Style) : String := Id.run do
  let t := ClusterTree.of g
  let mut out := "digraph G {\n  node [shape=box, fixedsize=true, label=\"\"];\n"
  out := out ++ s!"  nodesep={o.nodeGap / 72}; ranksep={o.layerGap / 72};\n"
  for i in [0:g.nodes.size] do
    let (w, h) := nodeSize st o (g.nodes.getD i default)
    out := out ++ s!"  n{i} [width={w / 72}, height={h / 72}];\n"
  -- clusters, children inside parents (a parent is listed before its children)
  let k := g.clusters.size
  let rec body (fuel c : Nat) : String :=
    match fuel with
    | 0 => ""
    | f + 1 =>
      let own := (Array.range g.nodes.size).filter (t.nodeCluster.getD · none == some c)
      let kids := (Array.range k).filter (t.parent.getD · none == some c)
      s!"subgraph cluster_{c} \{ label=\"{(g.clusters.getD c default).name}\"; " ++
        String.join (own.toList.map (s!"n{·}; ")) ++
        String.join (kids.toList.map (body f ·)) ++ "}\n"
  for c in [0:k] do
    if (t.parent.getD c none).isNone then out := out ++ "  " ++ body (k + 1) c
  for (_, e) in g.validEdges do
    out := out ++ s!"  n{e.src} -> n{e.dst};\n"
  return out ++ "}\n"

/-- A graph from the text of a `.graph` file: a line `n LENGTH SHAPE` for each node (a label of
that many letters; `e` for an ellipse, anything else for a rounded box), `e SRC DST` for each
edge, and `c LENGTH PARENT MEMBERS…` for each cluster (a title of that many letters, the number
of the cluster it is inside or `-1`, its nodes). Other lines are ignored. The real graphs
measured here are kept in this form: names removed, lengths kept. -/
def parseGraphFile (text : String) : Graph := Id.run do
  let mut nodes : Array Graph.Node := #[]
  let mut edges : Array Graph.Edge := #[]
  let mut clusters : Array Cluster := #[]
  for line in text.splitOn "\n" do
    match (line.splitOn " ").filter (· != "") with
    | ["n", len, shape] =>
      nodes := nodes.push { label := letters len.toNat!,
                            style := { shape := if shape == "e" then some .ellipse else none } }
    | ["e", a, b] => edges := edges.push { src := a.toNat!, dst := b.toNat! }
    | "c" :: len :: parent :: members =>
      clusters := clusters.push { name := letters len.toNat!, parent := parent.toNat?,
                                  members := members.toArray.map (·.toNat!) }
    | _ => pure ()
  return { nodes, edges, clusters }

/-- The graphs of the `.graph` files of a directory, by file name, in name order. -/
def fileGraphs (dir : System.FilePath) : IO (Array (String × Graph)) := do
  let entries := (← dir.readDir).filter (·.path.extension == some "graph")
  let sorted := entries.qsort fun a b => a.fileName < b.fileName
  sorted.mapM fun e => do
    return ((e.path.fileStem.getD e.fileName), parseGraphFile (← IO.FS.readFile e.path))

/-- Prints the measures of the graphs; with a directory, also writes the files of
`tools/graph-compare.py` there. -/
def reportGraphs (graphs : Array (String × Graph)) (dir? : Option String)
    (packed : Bool := false) (o : LayeredOptions := {}) : IO Unit := do
  if let some dir := dir? then IO.FS.createDirAll dir
  IO.println s!"load {← Graphs.loadAverage}"
  IO.println ("graph                  nodes edges   ms  crossings   length(px)   area(Mpx2) " ++
    "clu clr ent  turn infl  outside near back")
  for (name, g) in graphs do
    let t0 ← IO.monoNanosNow
    let l ← IO.lazyPure fun _ => if packed then g.layoutPacked o else g.layout o
    let ms ← Graphs.msSince t0
    let m := measure g l
    let v := eye l
    let pad := fun (s : String) (w : Nat) => String.ofList (List.replicate (w - s.length) ' ') ++ s
    IO.println s!"{name}{pad "" (22 - name.length)} {pad (toString g.nodes.size) 5} \
      {pad (toString g.edges.size) 5} {pad (toString ms) 4} {pad (toString m.crossings) 10} \
      {pad (toString m.length.round.toUInt64) 12} \
      {pad (toString (m.area / 1e6).round.toUInt64) 12} \
      {pad (toString m.clusterViolations) 3} {pad (toString m.clearanceViolations) 3} \
      {pad (toString m.clusterEntries) 3} {pad (fmtNum v.turning 1) 5} \
      {pad (fmtNum v.inflections 2) 4} {pad (toString v.outside.round.toUInt64) 8} \
      {pad (fmtNum v.nearest 1) 4} {pad (toString (v.turnedBack (o.direction == .leftToRight))) 4}"
    if let some dir := dir? then
      let dot := dotText g {} {}
      IO.FS.writeFile s!"{dir}/{name}.dot"
        (if packed then dot.replace "digraph G {\n" "digraph G {\n  pack=true;\n" else dot)
      IO.FS.writeFile s!"{dir}/{name}.layout" (Graphs.layoutText l)
      IO.FS.writeFile s!"{dir}/{name}.time" s!"{ms} {← Graphs.loadAverage}\n"
      IO.FS.writeFile s!"{dir}/{name}.svg" (l.toSvg {})

/-- Prints the measures of every graph of `graphs`; with a directory, also writes the files of
`tools/graph-compare.py` there. -/
def report (dir? : Option String) : IO Unit := reportGraphs graphs dir?

/-- The bounds the checks hold the measures to, by graph: crossings, edge length (pixels) and
area (square pixels), each about a tenth above the values measured when they were set. -/
def bounds : Array (String × Nat × Float × Float) :=
  #[("own-imports", 244, 107300, 4.8e6), ("project-imports", 116, 45000, 3.6e6),
    ("blueprint-a", 280, 66900, 3.6e6), ("blueprint-a-chapters", 291, 85400, 4.9e6),
    ("blueprint-a-nested", 354, 99100, 6.0e6), ("blueprint-b", 94, 39900, 3.6e6),
    ("blueprint-b-chapters", 117, 50800, 4.9e6), ("module-800", 8356, 1071500, 4.6e7),
    ("dense-dag", 827, 84300, 2.6e6), ("sparse-dag", 274, 62700, 6.0e6),
    ("tree", 0, 13400, 3.6e6), ("chain", 0, 7800, 6.0e5)]

/-- The graphs with clusters in which no edge may pass through a cluster that holds neither of
its ends. -/
def cleanClusters : Array String :=
  #["blueprint-a-chapters", "blueprint-a-nested", "blueprint-b-chapters"]

/-- A small graph whose clusters invite overlap: two clusters whose members sit in the same
layers, a node outside both between them in a middle layer, a nested cluster, a cluster with a
parent listed after it (taken as a top cluster) and a member that is not a node. -/
def awkwardClusters : Graph :=
  { nodes := (Array.range 9).map fun v => { label := s!"n{v}" },
    edges := #[(0, 1), (1, 2), (3, 4), (4, 5), (0, 4), (3, 1), (6, 7), (2, 8), (5, 8), (6, 1)].map
      fun (a, b) => { src := a, dst := b },
    clusters := #[{ name := "Left", members := #[0, 2] }, { name := "Right", members := #[3, 5] },
      { name := "Inner", members := #[1], parent := some 0 },
      { name := "Late", members := #[7, 99], parent := some 5 }] }

/-- The checks of the cluster rules and of the checkers themselves. -/
def clusterChecks : Array (String × Bool) :=
  let g := awkwardClusters
  let l := g.layout
  let t := ClusterTree.of g
  let into := fun (nb : NodeBox) => match l.clusters.find? (·.index == 0) with
    | some cb => { nb with box := ⟨cb.box.x0 + 1, cb.box.y0 + 1, cb.box.x0 + 5, cb.box.y0 + 5⟩ }
    | none => nb
  let moved : Layout := { l with nodes := l.nodes.modify 6 into }
  #[("clusters: a parent listed later is ignored", t.parent.getD 3 none == none),
    ("clusters: a node belongs to its deepest cluster", t.nodeCluster.getD 1 none == some 2),
    ("clusters: the nested cluster is held by its parent", t.holds 0 2 && !t.holds 1 2),
    ("clusters: the lowest common cluster", t.lca (some 2) (some 0) == some 0 &&
      t.lca (some 2) (some 1) == none),
    ("clusters: every cluster with nodes has a box", l.clusters.size == 4),
    ("clusters: boxes contain exactly their nodes and nest", (clusterProblems g l).isEmpty),
    ("clusters: no edge passes a node", ((clearanceProblems g l).filter
      (Graphs.has · "passes node")).isEmpty),
    ("clusters: a node moved into a box it does not belong to is reported",
      (clusterProblems g moved).any (Graphs.has · "overlaps node 6")),
    ("clusters: the same layout twice", g.toSvg == g.toSvg),
    ("clusters: left to right too", (clusterProblems g (g.layout { direction := .leftToRight
      })).isEmpty),
    ("segmentHitsBox: through, beside, touching",
      segmentHitsBox ⟨0, 5⟩ ⟨10, 5⟩ ⟨4, 0, 6, 10⟩ &&
      !segmentHitsBox ⟨0, 20⟩ ⟨10, 20⟩ ⟨4, 0, 6, 10⟩ &&
      segmentHitsBox ⟨6, 0⟩ ⟨6, 10⟩ ⟨4, 0, 6, 10⟩)]

/-- The quality checks (see the module docstring): every graph of `bounds` within its bounds,
and no graph with an edge that passes a node or a cluster box that breaks the cluster rules. -/
def checks : Array (String × Bool) := Id.run do
  let mut out : Array (String × Bool) := clusterChecks
  for (name, g) in graphs do
    if name == "module-3000" then continue
    let l := g.layout
    let m := measure g l
    out := out.push (s!"graph quality {name}: cluster boxes contain exactly their nodes and nest",
      m.clusterViolations == 0)
    out := out.push (s!"graph quality {name}: no edge passes a node it does not end at",
      m.clearanceViolations == 0)
    let v := eye l
    out := out.push (s!"graph quality {name}: every edge keeps three pixels from the nodes it \
      does not end at ({v.nearest})", v.nearest ≥ 3)
    out := out.push (s!"graph quality {name}: no edge turns back across the layers",
      v.turnedBack false == 0)
    if cleanClusters.contains name then
      out := out.push (s!"graph quality {name}: no edge passes through a cluster that holds \
        neither of its ends", m.clusterEntries == 0)
    if let some (_, c, len, a) := bounds.find? (·.1 == name) then
      out := out.push (s!"graph quality {name}: crossings {m.crossings} at most {c}",
        m.crossings ≤ c)
      out := out.push (s!"graph quality {name}: edge length within bound", m.length ≤ len)
      out := out.push (s!"graph quality {name}: area within bound", m.area ≤ a)
  return out

/-- What the recorded Graphviz measures of a graph were (`PILeanTest/graphs/dot-recorded.tsv`):
nodes, edges, crossings, edge length and area, and what the eye objects to (`Eye`). -/
structure Recorded where
  /-- The number of nodes. -/
  nodes : Nat
  /-- The number of edges. -/
  edges : Nat
  /-- Crossing pairs of edges. -/
  crossings : Nat
  /-- Total edge length (pixels). -/
  length : Float
  /-- Area (square pixels). -/
  area : Float
  /-- The mean turning of an edge (degrees). -/
  turning : Float
  /-- The mean number of inflections of an edge. -/
  inflections : Float
  /-- The length of the edges outside the box around the nodes (pixels). -/
  outside : Float
  /-- The least distance between an edge and a node it does not end at (pixels). -/
  nearest : Float

/-- A decimal number such as `12.5` (digits, at most one point). -/
def decimal? (s : String) : Option Float :=
  match s.splitOn "." with
  | [a] => a.toNat?.map (·.toFloat)
  | [a, b] => match a.toNat?, b.toNat? with
    | some x, some y => some (x.toFloat + y.toFloat / (10 : Float) ^ b.length.toFloat)
    | _, _ => none
  | _ => none

/-- The rows of `dot-recorded.tsv` (the text of the file) by graph name; lines that do not have
nine fields of numbers after the name, such as comments and the header, are ignored. -/
def parseRecorded (text : String) : Array (String × Recorded) := Id.run do
  let mut out := #[]
  for line in text.splitOn "\n" do
    match line.splitOn "\t" with
    | [name, n, e, c, len, a, turn, infl, outside, near] =>
      if let (some n, some e, some c, some len, some a, some turn, some infl, some outside,
          some near) := (n.toNat?, e.toNat?, c.toNat?, len.toNat?, a.toNat?, decimal? turn,
            decimal? infl, decimal? outside, decimal? near) then
        out := out.push (name, { nodes := n, edges := e, crossings := c, length := len.toFloat,
                                 area := a.toFloat, turning := turn, inflections := infl,
                                 outside, nearest := near })
    | _ => pure ()
  return out

/-- The most the crossings, the edge length, the mean turning of an edge and its mean number of
inflections may be, as multiples of Graphviz's recorded values, by graph (each about `0.1` above
the ratio measured when it was set; `0` where Graphviz's value is nothing to compare with: a
graph it draws without crossings may have none, and the turning and inflections are then held
to a degree and to a twentieth of an inflection for each edge). -/
def ratios : Array (String × Float × Float × Float × Float) :=
  #[("blueprint-67", 1.16, 1.01, 1.53, 1.66), ("blueprint-67-chapters", 0.93, 1.16, 1.65, 1.4),
    ("blueprint-a", 1.11, 0.95, 1.23, 1.05), ("blueprint-a-chapters", 0.96, 1.02, 1.57, 1.29),
    ("blueprint-a-nested", 1.09, 1.01, 1.63, 1.29), ("blueprint-b", 1.17, 1.27, 0.97, 2.8),
    ("blueprint-b-chapters", 0.71, 1.0, 1.2, 1.1), ("chain", 0, 1.24, 0, 0),
    ("dense-dag", 1.16, 0.81, 1.24, 1.82), ("module-800", 1.33, 1.09, 0.97, 0.92),
    ("own-imports", 1.14, 1.01, 1.15, 1.05), ("project-imports", 0.85, 0.99, 1.09, 0.7),
    ("sparse-dag", 1.03, 1.22, 0.76, 0.55), ("tree", 0, 1.38, 0, 0),
    ("code-site-c-largest-module", 0.12, 1.09, 0.27, 0.15),
    ("code-site-c-modules", 1.24, 1.13, 1.24, 1.28),
    ("code-site-c", 0.59, 1.14, 1.13, 0.93), ("neighbourhood-150", 0.87, 0.81, 1.15, 0.91),
    ("neighbourhood-290", 0.96, 0.89, 1.22, 1.09), ("neighbourhood-34", 1.02, 1.05, 1.33, 1.23),
    ("neighbourhood-46", 1.19, 1.0, 1.12, 0.77), ("neighbourhood-46b", 1.05, 1.25, 1.19, 0.95),
    ("neighbourhood-50", 1.06, 0.97, 1.19, 0.83), ("neighbourhood-star-401", 0, 1.11, 0.17, 0.15)]

/-- The graphs the checks against Graphviz leave out for the time they take: the largest of the
measured graphs. -/
def slowGraphs : Array String := #["module-3000", "code-site-c"]

/-- The checks against the recorded Graphviz measures: reads the `.graph` files and
`dot-recorded.tsv` of `PILeanTest/graphs` (no `dot` needed) and holds every graph (the built-in
ones and the files') to no cluster violation, no edge passing a node, and crossings and edge
length within `ratios` times Graphviz's; and the packed layout of the largest module without its
cluster (which holds every node, so that it cannot be packed with it) to a picture narrower than
the layered one. (The module has a node with 400 neighbours, which stand in one layer, so the
picture stays far wider than tall.) -/
def ioChecks : IO (Array (String × Bool)) := do
  let dir : System.FilePath := "PILeanTest" / "graphs"
  let recorded := parseRecorded (← IO.FS.readFile (dir / "dot-recorded.tsv"))
  let files ← fileGraphs dir
  let mut out : Array (String × Bool) :=
    #[(s!"graph files: {files.size} graphs and {recorded.size} recorded rows",
        files.size == 12 && recorded.size == 27)]
  for (name, g) in graphs ++ files do
    if slowGraphs.contains name then continue
    let l := g.layout
    let m := measure g l
    out := out.push (s!"graph files {name}: cluster boxes contain exactly their nodes and nest",
      m.clusterViolations == 0)
    out := out.push (s!"graph files {name}: no edge passes a node it does not end at",
      m.clearanceViolations == 0)
    match recorded.find? (·.1 == name), ratios.find? (·.1 == name) with
    | some (_, r), some (_, rc, rl, rt, ri) =>
      let v := eye l
      out := out.push (s!"graph files {name}: {g.nodes.size} nodes and {g.edges.size} edges as \
        recorded", r.nodes == g.nodes.size && r.edges == g.edges.size)
      out := out.push (s!"graph files {name}: crossings {m.crossings} at most {rc} times \
        Graphviz's {r.crossings}", m.crossings.toFloat ≤ rc * r.crossings.toFloat)
      out := out.push (s!"graph files {name}: edge length {m.length} at most {rl} times \
        Graphviz's {r.length}", m.length ≤ rl * r.length)
      out := out.push (s!"graph files {name}: an edge turns by {v.turning} degrees, at most \
        {rt} times Graphviz's {r.turning} and one more", v.turning ≤ rt * r.turning + 1)
      out := out.push (s!"graph files {name}: an edge has {v.inflections} inflections, at most \
        {ri} times Graphviz's {r.inflections} and a twentieth more",
        v.inflections ≤ ri * r.inflections + 0.05)
      out := out.push (s!"graph files {name}: every edge keeps three pixels from the nodes it \
        does not end at ({v.nearest}; Graphviz's come within {r.nearest})", v.nearest ≥ 3)
      out := out.push (s!"graph files {name}: no edge turns back across the layers",
        v.turnedBack false == 0)
    | _, _ => out := out.push (s!"graph files {name}: recorded measures and ratios present", false)
  if let some (_, g) := files.find? (·.1 == "code-site-c-largest-module") then
    -- the one cluster of the file holds every node, so its components cannot be told apart
    let whole := g.layoutPacked
    out := out.push (s!"graph files: the packed largest module, one cluster, is the layered \
      layout", whole.width == g.layout.width && whole.height == g.layout.height)
    let p := { g with clusters := #[] }.layoutPacked
    out := out.push (s!"graph files: the packed largest module without its cluster is {p.width} \
      by {p.height}, narrower than the layered {g.layout.width}", p.width < g.layout.width)
  return out

/-- Prints the violations of the cluster and clearance rules in the layout of the graph named
`name` (one of `graphs`). -/
def problems (name : String) : IO Unit := do
  match graphs.find? (·.1 == name) with
  | none => IO.eprintln s!"no graph {name}"
  | some (_, g) =>
    let l := g.layout
    for p in clusterProblems g l ++ clearanceProblems g l do IO.println p

end PILeanTest.GraphQuality
