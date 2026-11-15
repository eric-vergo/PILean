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
(`clusterProblems`) and of the edges' clearance (`clearanceProblems`), and the time taken.

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

/-- Prints the measures of every graph; with a directory, also writes the files of
`tools/graph-compare.py` there. -/
def report (dir? : Option String) : IO Unit := do
  if let some dir := dir? then IO.FS.createDirAll dir
  IO.println s!"load {← Graphs.loadAverage}"
  IO.println ("graph                  nodes edges   ms  crossings   length(px)   area(Mpx2) " ++
    "clu clr ent")
  for (name, g) in graphs do
    let t0 ← IO.monoNanosNow
    let l ← IO.lazyPure fun _ => g.layout
    let ms ← Graphs.msSince t0
    let m := measure g l
    let pad := fun (s : String) (w : Nat) => String.ofList (List.replicate (w - s.length) ' ') ++ s
    IO.println s!"{name}{pad "" (22 - name.length)} {pad (toString g.nodes.size) 5} \
      {pad (toString g.edges.size) 5} {pad (toString ms) 4} {pad (toString m.crossings) 10} \
      {pad (toString m.length.round.toUInt64) 12} \
      {pad (toString (m.area / 1e6).round.toUInt64) 12} \
      {pad (toString m.clusterViolations) 3} {pad (toString m.clearanceViolations) 3} \
      {pad (toString m.clusterEntries) 3}"
    if let some dir := dir? then
      IO.FS.writeFile s!"{dir}/{name}.dot" (dotText g {} {})
      IO.FS.writeFile s!"{dir}/{name}.layout" (Graphs.layoutText l)
      IO.FS.writeFile s!"{dir}/{name}.time" s!"{ms} {← Graphs.loadAverage}\n"
      IO.FS.writeFile s!"{dir}/{name}.svg" (g.toSvg)

/-- The bounds the checks hold the measures to, by graph: crossings, edge length (pixels) and
area (square pixels), each about a tenth above the values measured when they were set. -/
def bounds : Array (String × Nat × Float × Float) :=
  #[("own-imports", 255, 104000, 4.6e6), ("project-imports", 172, 46700, 2.4e6),
    ("blueprint-a", 345, 74200, 2.8e6), ("blueprint-a-chapters", 460, 147400, 4.0e6),
    ("blueprint-a-nested", 470, 187600, 6.0e6), ("blueprint-b", 112, 37700, 2.4e6),
    ("blueprint-b-chapters", 220, 88200, 5.3e6), ("module-800", 9380, 1.1e6, 3.0e7),
    ("dense-dag", 935, 90900, 2.5e6), ("sparse-dag", 390, 70400, 4.5e6),
    ("tree", 0, 13700, 2.4e6), ("chain", 0, 7900, 5.3e5)]

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
    if let some (_, c, len, a) := bounds.find? (·.1 == name) then
      out := out.push (s!"graph quality {name}: crossings {m.crossings} at most {c}",
        m.crossings ≤ c)
      out := out.push (s!"graph quality {name}: edge length within bound", m.length ≤ len)
      out := out.push (s!"graph quality {name}: area within bound", m.area ≤ a)
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
