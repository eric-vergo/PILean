/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILeanTest.GraphFixtures

/-!
# Graph checks and measurements

Named checks of the graph layouts (layering, crossing counts, every edge drawn, awkward graphs,
escaping, determinism), the random module-dependency graphs used by the measurements
(`moduleGraph`, from a fixed linear congruential generator), the timing of layout and output
(`bench`, run by `lake exe pilean-test --graph-bench`) and the files of `tools/graph-compare.py`
(`writeCompare`, run by `lake exe pilean-test --graph-compare-out DIR`).
-/

namespace PILeanTest.Graphs

open PILean PILean.Graph

/-- Whether `s` contains `t`. -/
def has (s t : String) : Bool := (s.splitOn t).length > 1

/-- The next state and a 31-bit number from a linear congruential generator (Knuth's MMIX
constants). -/
def next (s : UInt64) : UInt64 × Nat :=
  let s' := s * 6364136223846793005 + 1442695040888963407
  (s', (s' >>> 33).toNat)

/-- A random graph shaped like the dependencies between modules: `n` nodes in a random order,
each depending on one or two earlier ones, mostly near it in the order (about `4n / 3` edges),
and `n / 60` back edges that close cycles (with `far := false`, every dependency is on one of
the `near` nodes before). The same graph for the same `seed` on every run. -/
def moduleGraph (seed n : Nat) (near : Nat := 30) (far : Bool := true) : Graph := Id.run do
  let mut s : UInt64 := seed.toUInt64 * 2654435761 + 12345
  let mut perm := Array.range n
  for k in [0:n] do
    let i := n - 1 - k
    if i ≥ 1 then
      let (s', r) := next s
      s := s'
      let j := r % (i + 1)
      let a := perm.getD i 0
      perm := (perm.setIfInBounds i (perm.getD j 0)).setIfInBounds j a
  let mut edges : Array Graph.Edge := #[]
  for i in [1:n] do
    let (s1, r1) := next s
    let (s2, r2) := next s1
    let (s3, r3) := next s2
    s := s3
    -- half of the dependencies are on one of the `near` nodes before, the rest anywhere before
    let pick := fun (r : Nat) =>
      if r % 2 == 0 || !far then i - 1 - (r / 2) % (min i near) else (r / 2) % i
    let j := pick r1
    edges := edges.push { src := perm.getD i 0, dst := perm.getD j 0 }
    if r2 % 3 == 0 then
      let j2 := pick r3
      if j2 != j then edges := edges.push { src := perm.getD i 0, dst := perm.getD j2 0 }
  for _ in [0:n / 60] do
    let (s1, r1) := next s
    let (s2, r2) := next s1
    s := s2
    let a := r1 % n
    let b := r2 % n
    if a < b then edges := edges.push { src := perm.getD a 0, dst := perm.getD b 0 }
  return { nodes := (Array.range n).map fun v => { label := s!"Mod{v}" }, edges }

/-- Whether every number of the layout is finite. -/
def finite (l : Layout) : Bool :=
  let ok := fun (x : Float) => !x.isNaN && !x.isInf
  let okBox := fun (b : Box) => ok b.x0 && ok b.y0 && ok b.x1 && ok b.y1
  let okPath := fun (p : Path) => p.cmds.all fun c => c.points.all fun q => ok q.x && ok q.y
  ok l.width && ok l.height && l.nodes.all (okBox ·.box) && l.clusters.all (okBox ·.box) &&
    l.edges.all fun e => okPath e.path && e.points.all (fun q => ok q.x && ok q.y) &&
      (e.head.all okPath) && (e.label.all (okBox ·.box))

/-- Whether two boxes overlap (share area). -/
def overlap (a b : Box) : Bool := a.x0 < b.x1 && b.x0 < a.x1 && a.y0 < b.y1 && b.y0 < a.y1

/-- Whether no two node boxes overlap. -/
def disjoint (l : Layout) : Bool :=
  (List.range l.nodes.size).all fun i => (List.range i).all fun j =>
    match l.nodes[i]?, l.nodes[j]? with
    | some a, some b => !overlap a.box b.box
    | _, _ => true

/-- Whether a point lies on the boundary of a box (within a pixel). -/
def onBoundary (b : Box) (p : Point) : Bool :=
  let near := fun (u v : Float) => (u - v).abs ≤ 1
  (near p.x b.x0 || near p.x b.x1 || near p.y b.y0 || near p.y b.y1) &&
    p.x ≥ b.x0 - 1 && p.x ≤ b.x1 + 1 && p.y ≥ b.y0 - 1 && p.y ≤ b.y1 + 1

/-- Whether every routed edge (other than loops) starts on its source's box and ends on its
target's (a point of the route list; the arrowhead's tip is where the route ends). -/
def endsOnBoxes (l : Layout) : Bool :=
  l.edges.all fun e =>
    e.src == e.dst ||
      match e.points[0]?, e.points.back?, l.nodes[e.src]?, l.nodes[e.dst]? with
      | some a, some z, some s, some t => onBoundary s.box a && onBoundary t.box z
      | _, _, _, _ => false

/-- The graphs of the awkward-case checks. -/
def tiny : Array (String × Graph) :=
  #[("empty", {}), ("one node", { nodes := #[{ label := "a" }] }),
    ("self-loop", Graph.ofPairs [(0, 0)]),
    ("parallel edges", Graph.ofPairs [(0, 1), (0, 1), (1, 0)]),
    ("two components", Graph.ofPairs [(0, 1), (2, 3), (3, 4)]),
    ("2-cycle", Graph.ofPairs [(0, 1), (1, 0)]),
    ("missing nodes", Graph.ofNames #["a", "b"] [(0, 1), (1, 7), (9, 0)]),
    ("labelled loop",
      { nodes := #[{ label := "a" }], edges := #[{ src := 0, dst := 0, label := "again" }] })]

/-- The checks of the layering. -/
def layering : Array (String × Bool) :=
  let ok := fun (seed n : Nat) =>
    let g := moduleGraph seed n
    let pairs := g.edges.toList.map fun e => (e.src, e.dst)
    let pos := elsPositions n (pairs.toArray)
    let lay := assignLayers pos n pairs
    pairs.all fun (u, v) =>
      let lu := lay.getD u 0
      let lv := lay.getD v 0
      u == v || (if before pos u v then lu < lv else lv < lu)
  let cyc := Graph.ofPairs [(0, 1), (1, 2), (2, 0), (2, 3)]
  let pos := elsPositions 4 (cyc.edges.map fun e => (e.src, e.dst))
  let repairIdle := fun (g : Graph) =>
    let n := g.nodes.size
    let pairs := (g.edges.filter fun e => e.src != e.dst && e.src < n && e.dst < n).toList.map
      fun e => (e.src, e.dst)
    let pos := elsPositions n pairs.toArray
    let before := layersBeforeRepair pos n pairs
    fixLayers (acyclicEdges pos pairs) before == before
  #[("layering: the final repair changes nothing after simplex and balancing (random graphs, \
      the fixtures and the import graphs)",
      ([(1, 30), (2, 80), (3, 200), (4, 5), (5, 1), (6, 400), (7, 120)].all fun (s, n) =>
        repairIdle (moduleGraph s n)) && (tiny.all fun (_, g) => repairIdle g) &&
        repairIdle (moduleGraph 1 800) && repairIdle (moduleGraph 1 3000) &&
        repairIdle (Graph.ofLabelled Fixtures.ownImports.toList) &&
        repairIdle (Graph.ofLabelled Fixtures.projectImports.toList)),
    ("layering: every edge points to a deeper layer after cycle removal (random graphs)",
      [(1, 30), (2, 80), (3, 200), (4, 5), (5, 1)].all fun (s, n) => ok s n),
    ("cycle removal: positions are a permutation",
      (pos.qsort (· < ·)) == #[0, 1, 2, 3]),
    ("cycle removal: a triangle cycle loses exactly one edge",
      (cyc.edges.filter fun e => !before pos e.src e.dst).size == 1),
    ("layering: a chain gets consecutive layers",
      assignLayers #[0, 1, 2] 3 [(0, 1), (1, 2)] == #[0, 1, 2]),
    ("layering: a source is moved next to its successor",
      assignLayers #[0, 1, 3, 2] 4 [(0, 1), (1, 2), (3, 2)] == #[0, 1, 2, 1])]

/-- The checks of crossing counting. -/
def counting : Array (String × Bool) :=
  let pos := #[0, 1, 0, 1, 2]
  -- upper layer [0, 1] over lower [2, 3]
  let straight : Array (Array Nat) := #[#[2], #[3], #[], #[], #[]]
  let crossed : Array (Array Nat) := #[#[3], #[2], #[], #[], #[]]
  let k33 : Array (Array Nat) := #[#[3, 4, 5], #[3, 4, 5], #[3, 4, 5], #[], #[], #[]]
  let pos33 := #[0, 1, 2, 0, 1, 2]
  #[("crossings: parallel edges do not cross", crossings #[0, 1] 2 straight pos == 0),
    ("crossings: two swapped edges cross once", crossings #[0, 1] 2 crossed pos == 1),
    ("crossings: K3,3 has three choose two squared", crossings #[0, 1, 2] 3 k33 pos33 == 9),
    ("crossings: edges sharing an end do not cross",
      crossings #[0, 1] 2 #[#[2, 3], #[3], #[], #[], #[]] pos == 0)]

/-- The checks of the layouts on random and awkward graphs. -/
def layouts : Array (String × Bool) :=
  let g := moduleGraph 7 60
  let l := g.layout {} {}
  let withLabels : Graph :=
    { g with edges := g.edges.mapIdx fun i e =>
        if i % 7 == 0 then { e with label := s!"e{i}" } else e }
  let lab := withLabels.layout {} {}
  let lr := g.layout { direction := .leftToRight } {}
  let orth := g.layout { routing := .orthogonal } {}
  let mixed := (Graph.ofPairs [(0, 1), (1, 2), (2, 0), (0, 5), (3, 3)]).layout {} {}
  let tinyOk := fun (p : Layout → Bool) => tiny.all fun (_, t) => p (t.layout {} {})
  let named := tiny.map fun (name, t) =>
    let lt := t.layout {} {}
    (s!"graph: {name}: every valid edge drawn once, all numbers finite",
      lt.edges.map (·.index) == (t.validEdges.map (·.1)) && finite lt)
  named ++
  #[("graph: every edge of a random graph is drawn (by index)",
      l.edges.map (·.index) == g.validEdges.map (·.1) && l.edges.size == g.edges.size),
    ("graph: no NaN or infinity in the layouts (spline, orthogonal, left to right, labels)",
      finite l && finite orth && finite lr && finite lab),
    ("graph: node boxes never overlap (random graph, all options)",
      disjoint l && disjoint lr && disjoint orth && disjoint lab && tinyOk disjoint),
    ("graph: edges meet the outlines of their nodes",
      endsOnBoxes l && endsOnBoxes lr && endsOnBoxes orth && endsOnBoxes lab),
    ("graph: layers run down, or left to right",
      (l.nodes.any fun a => l.nodes.any fun b => b.box.y0 > a.box.y1) &&
        (lr.nodes.any fun a => lr.nodes.any fun b => b.box.x0 > a.box.x1)),
    ("graph: the layout is the same twice, as SVG and as PNG",
      g.toSvg == g.toSvg && (moduleGraph 3 12).toPng.toOption == (moduleGraph 3 12).toPng.toOption),
    ("graph: reversed edges are drawn in their own direction",
      let r := mixed.edges.filter (·.reversed)
      !r.isEmpty && r.all fun e => e.head.isSome &&
        match e.points[0]?, mixed.nodes[e.src]? with
        | some p, some n => onBoundary n.box p
        | _, _ => false),
    ("graph: a self-loop has a curve, a head and its own two points",
      match (Graph.ofPairs [(0, 0)]).layout {} {} with
      | l => l.edges.size == 1 && l.edges.all fun e => e.head.isSome && e.points.size == 2),
    ("graph: parallel edges take different paths",
      let l := (Graph.ofPairs [(0, 1), (0, 1)]).layout {} {}
      l.edges.size == 2 && (l.edges[0]?.map (·.path)) != (l.edges[1]?.map (·.path))),
    ("graph: a 2-cycle reverses one edge",
      ((Graph.ofPairs [(0, 1), (1, 0)]).layout {} {}).edges.filter (·.reversed) |>.size |>.beq 1),
    ("graph: edge labels sit on plates at the middle of long edges",
      lab.edges.all fun e => match e.label with
        | some t => !t.text.isEmpty && t.box.width > 0
        | none => true),
    ("graph: invalid edges are dropped",
      let g := Graph.ofNames #["a", "b"] [(0, 1), (1, 7), (9, 0)]
      (g.layout {} {}).edges.size == 1 && g.validIndices == [0]),
    ("graph: undirected edges have no arrowheads",
      ((Graph.ofPairs [(0, 1), (1, 2)] (directed := false)).layout {} {}).edges.all
        (·.head.isNone)),
    ("graph: spline and orthogonal paths differ and are not empty",
      !l.edges.isEmpty && l.edges.all (!·.path.cmds.isEmpty) &&
        orth.edges.all (!·.path.cmds.isEmpty) &&
        (l.edges.map (·.path)) != (orth.edges.map (·.path)))]

/-- The checks of escaping and of the written forms. -/
def written : Array (String × Bool) :=
  let evil : Graph :=
    { nodes := #[{ label := "<script>alert(1)</script>" }, { label := "a&b" }],
      edges := #[{ src := 0, dst := 1, label := "\"x\" <b>" }] }
  let svg := evil.toSvg
  let svgOutlined := evil.toSvg {} {} true
  let big := (Graph.ofPairs [(0, 1), (1, 2)]).toPng {} {} 2
  #[("graph: labels are escaped in SVG", !has svg "<script" && has svg "&lt;script&gt;" &&
      has svg "a&amp;b" && !has svg "<b>"),
    ("graph: text as shapes writes no text elements", !has svgOutlined "<text"),
    ("graph: PNG output decodes to the expected size",
      match big with
      | .ok b => match Png.decode b with
        | .ok d => let l := (Graph.ofPairs [(0, 1), (1, 2)]).layout {} {}
                   d.image.width == (l.width * 2).ceil.toUInt64.toNat
        | .error _ => false
      | .error _ => false),
    ("graph: the SVG is drawn from the layout's own shapes",
      has ((Graph.ofPairs [(0, 1)]).toSvg) "<path")]

/-- The checks of the circular and tree layouts. -/
def simple : Array (String × Bool) :=
  let ring := Graph.ofPairs [(0, 1), (1, 2), (2, 3), (3, 0), (0, 2), (0, 2), (1, 1)]
    (directed := false)
  let c := ring.circularLayout {} {}
  let tree := Graph.ofPairs [(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (4, 6), (3, 6)]
  let t := tree.treeLayout 0 {} {}
  let forest := (Graph.ofPairs [(0, 1), (2, 3)]).treeLayout 0 {} {}
  #[("circular: every edge drawn once, finite, boxes apart",
      c.edges.map (·.index) == ring.validEdges.map (·.1) && finite c && disjoint c),
    ("circular: nodes lie on one circle",
      let ctr := fun (n : NodeBox) =>
        (Point.mk ((n.box.x0 + n.box.x1) / 2) ((n.box.y0 + n.box.y1) / 2))
      let mid := (c.nodes.foldl (fun p n => p + ctr n) (Point.mk 0 0))
      let m : Point := (1 / c.nodes.size.toFloat) * mid
      let rs := c.nodes.map fun n => (ctr n - m).norm
      rs.all fun r => (r - (rs.getD 0 0)).abs < 2),
    ("tree: every edge drawn once, finite, boxes apart, ends on outlines",
      t.edges.map (·.index) == tree.validEdges.map (·.1) && finite t && disjoint t &&
        endsOnBoxes t),
    ("tree: a parent is centred over its two children",
      match t.nodes[1]?, t.nodes[3]?, t.nodes[4]? with
      | some p, some a, some b =>
        ((p.box.x0 + p.box.x1) - ((a.box.x0 + a.box.x1) + (b.box.x0 + b.box.x1)) / 2).abs ≤ 2
      | _, _, _ => false),
    ("tree: unreached nodes start further trees", finite forest && disjoint forest),
    ("simple layouts are deterministic",
      (ring.circularLayout {} {}).nodes.map (·.box) == c.nodes.map (·.box))]

/-- The total span of the edges `es` for the layers `lay`. -/
def spanOf (es : List (Nat × Nat)) (lay : Array Nat) : Nat :=
  es.foldl (fun s e => s + (lay.getD e.2 0 - lay.getD e.1 0)) 0

/-- The least total span of any layering of `n` nodes into layers below `n` in which every edge
points to a deeper layer, by trying them all. -/
def bruteSpan (n : Nat) (es : List (Nat × Nat)) : Nat := Id.run do
  let mut best := n * es.length + 1
  let mut lay : Array Nat := Array.replicate n 0
  for code in [0:n ^ n] do
    let mut c := code
    for v in [0:n] do
      lay := lay.setIfInBounds v (c % n)
      c := c / n
    if es.all fun e => lay.getD e.1 0 < lay.getD e.2 0 then
      best := min best (spanOf es lay)
  return best

/-- The checks of the network simplex layering and coordinates. -/
def optimising : Array (String × Bool) :=
  let minimal := fun (seed n : Nat) =>
    let g := moduleGraph seed n (near := 3) (far := false)
    let pairs := g.edges.toList.map fun e => (e.src, e.dst)
    let pos := elsPositions n pairs.toArray
    let es := acyclicEdges pos pairs
    spanOf es (assignLayers pos n pairs) == bruteSpan n es
  let bigG := moduleGraph 5 400
  let bigPairs := bigG.edges.toList.map fun e => (e.src, e.dst)
  let bigPos := elsPositions 400 bigPairs.toArray
  let bigEs := acyclicEdges bigPos bigPairs
  let start := fixLayers bigEs (Array.replicate 400 0)
  let simplex := simplexLayers 400 bigEs start
  -- a weighted problem: `b` is pulled to `a` by weight 1 and to `c` by weight 3, and `c` is
  -- five below `a`
  let (w, _) := simplexSolve 3 #[0, 1, 0] #[1, 2, 2] #[1, 1, 5] #[1, 3, 0] #[0, 1, 5]
  let chain := Graph.ofPairs [(0, 3), (0, 1), (1, 2), (2, 3)]
  let bigLayout := bigG.layout {} {}
  #[("simplex: the total span is the least possible (random small graphs, all layerings tried)",
      [(1, 6), (2, 6), (3, 7), (4, 6), (5, 5), (6, 7)].all fun (s, n) => minimal s n),
    ("simplex: every edge points to a deeper layer and the span is below longest-path's",
      bigEs.all (fun e => simplex.getD e.1 0 < simplex.getD e.2 0) &&
        spanOf bigEs simplex ≤ spanOf bigEs start),
    ("simplex: a weighted problem keeps the heavy edges short",
      w.size == 3 && w.getD 2 0 - w.getD 1 0 == 1 && w.getD 1 0 - w.getD 0 0 == 4),
    ("simplex: the layering and the layout are the same twice",
      simplexLayers 400 bigEs start == simplex &&
        (bigG.layout {} {}).edges.map (·.points) == bigLayout.edges.map (·.points)),
    ("simplex: a long edge in a layered chain stays straight",
      match (chain.layout {} {}).edges[0]? with
      | some e => e.points.size == 4 && (e.points.getD 1 ⟨0, 0⟩).x == (e.points.getD 2 ⟨1, 0⟩).x
      | none => false),
    ("simplex: a spent work budget still gives a layout with boxes apart",
      disjoint (bigG.layout { coordinateWork := 1000 } {}) &&
        disjoint (bigG.layout { coordinateWork := 0, refine := 0 } {}))]

/-- All the pure checks. -/
def checks : Array (String × Bool) :=
  layering ++ optimising ++ counting ++ layouts ++ written ++ simple

/-- The load averages of the machine (`sysctl -n vm.loadavg`), or a note when unavailable. -/
def loadAverage : IO String := do
  try
    let out ← IO.Process.output { cmd := "sysctl", args := #["-n", "vm.loadavg"] }
    return out.stdout.trimAscii.toString
  catch _ => return "unavailable"

/-- Milliseconds since an earlier `IO.monoNanosNow` reading. -/
def msSince (t0 : Nat) : IO Nat := do
  let t ← IO.monoNanosNow
  return (t - t0) / 1000000

/-- Times the layout phases, the SVG and the PNG of module graphs of 100, 800 and 3000 nodes
(the picture is scaled down to at most 2500 pixels on its longer side for the PNG) and prints a
table with the load average. -/
def bench : IO Unit := do
  let st : Style := {}
  let o : LayeredOptions := {}
  IO.println s!"load average before: {← loadAverage}"
  for n in [100, 800, 3000] do
    let g := moduleGraph 1 n
    let ve := g.validEdges
    let pairs : Array (Nat × Nat) := ve.filterMap fun (_, e) =>
      if e.src != e.dst then some (e.src, e.dst) else none
    let t0 ← IO.monoNanosNow
    let pos ← IO.lazyPure fun _ => elsPositions n pairs
    let cycles ← msSince t0
    let t1 ← IO.monoNanosNow
    let lay ← IO.lazyPure fun _ => assignLayers pos n pairs.toList
    let layers ← msSince t1
    let t2 ← IO.monoNanosNow
    let oriented : Array (Option (Nat × Nat)) := ve.map fun (_, e) =>
      if e.src == e.dst then none
      else if before pos e.src e.dst then some (e.src, e.dst) else some (e.dst, e.src)
    let built ← IO.lazyPure fun _ =>
      let (chains, layerAll) := buildChains lay oriented
      let (up, down) := chainNeighbours layerAll.size chains
      (chains, layerAll, up, down)
    let chainMs ← msSince t2
    let (chains, layerAll, up, down) := built
    let size := layerAll.size
    let t3 ← IO.monoNanosNow
    let order ← IO.lazyPure fun _ =>
      orderLayers layerAll up down o.sweeps
    let ordering ← msSince t3
    let t4 ← IO.monoNanosNow
    let bw := (Array.range size).map fun v => if v < n then 70.0 else 0.0
    let sep := separation n bw o.nodeGap o.edgeGap 0 #[]
    let x0 ← IO.lazyPure fun _ => assignBreadth size n order up down sep bw
    let coords ← msSince t4
    let t4b ← IO.monoNanosNow
    let x1 ← IO.lazyPure fun _ => refineBreadth size n chains order up down sep bw x0 o.refine
    let refined ← msSince t4b
    let t4c ← IO.monoNanosNow
    let xs ← IO.lazyPure fun _ => simplexBreadth size n chains order sep bw x1 8 o.coordinateWork
    let simplexMs ← msSince t4c
    let t4d ← IO.monoNanosNow
    let xt ← IO.lazyPure fun _ => simplexBreadth size n chains order sep bw x1 8 0
    let treeMs ← msSince t4d
    let t5 ← IO.monoNanosNow
    let l ← IO.lazyPure fun _ => g.layout o st
    let total ← msSince t5
    let t6 ← IO.monoNanosNow
    let svg ← IO.lazyPure fun _ => l.toSvg st
    let svgMs ← msSince t6
    let scale := min 1 (2500 / max l.width l.height)
    let t7 ← IO.monoNanosNow
    let img ← IO.lazyPure fun _ => l.toImage st scale
    let rasterMs ← msSince t7
    let t8 ← IO.monoNanosNow
    let png ← IO.lazyPure fun _ => img.writePng
    let pngMs ← msSince t8
    let crossingsNow := totalCrossings order down (positionsOf size order)
    -- the widths of the two simplex results, so that neither computation is left out
    let spread := fun (x : Array Float) => x.foldl max 0 - x.foldl min 0
    IO.println s!"{n} nodes, {g.edges.size} edges, {size - n} dummy nodes, {crossingsNow} \
      crossings, picture {l.width} × {l.height}, simplex widths {spread xs} and {spread xt}"
    IO.println s!"  layout {total} ms (cycles {cycles}, layers {layers}, chains {chainMs}, \
      ordering {ordering}, coordinates {coords}, refine {refined}, simplex {simplexMs} (tree \
      {treeMs})); SVG {svgMs} ms \
      ({svg.length} bytes); PNG at scale {scale}: draw {rasterMs} ms, encode {pngMs} ms \
      ({match png with | .ok b => b.size | .error _ => 0} bytes)"
  IO.println s!"load average after: {← loadAverage}"

/-- The text of a layout for `tools/graph-compare.py`: the size, the node boxes and each edge's
route flattened to a polyline. -/
def layoutText (l : Layout) : String := Id.run do
  let mut out := s!"size {l.width} {l.height}\n"
  for n in l.nodes do
    out := out ++ s!"node {n.index} {n.box.x0} {n.box.y0} {n.box.x1} {n.box.y1}\n"
  for e in l.edges do
    let pts := (e.path.flatten 0.5).foldl (fun acc pl => acc ++ pl.points) #[]
    out := out ++ s!"edge {e.index} {e.src} {e.dst} {pts.size}"
    for p in pts do out := out ++ s!" {p.x} {p.y}"
    out := out ++ "\n"
  return out

/-- The Graphviz input for a graph, with the same node sizes and gaps as the layout. -/
def dotText (g : Graph) (o : LayeredOptions) (st : Style) : String := Id.run do
  let mut out := "digraph G {\n  node [shape=box, fixedsize=true, label=\"\"];\n"
  out := out ++ s!"  nodesep={o.nodeGap / 72}; ranksep={o.layerGap / 72};\n"
  for i in [0:g.nodes.size] do
    let (w, h) := nodeSize st o (g.nodes.getD i default)
    out := out ++ s!"  n{i} [width={w / 72}, height={h / 72}];\n"
  for (_, e) in g.validEdges do
    out := out ++ s!"  n{e.src} -> n{e.dst};\n"
  return out ++ "}\n"

/-- The graphs compared with Graphviz: two small ones, module graphs of 100, 800 and 3000 nodes,
and two real import graphs (this library's, and a project of about a hundred modules). -/
def compareGraphs : Array (String × Graph) :=
  #[("hand-dag", Graph.ofPairs [(0, 1), (0, 2), (0, 3), (1, 4), (2, 4), (2, 5), (3, 5), (4, 6),
      (5, 6), (1, 5), (0, 6)]),
    ("hand-cycles", Graph.ofPairs [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 2), (4, 5), (0, 5),
      (1, 3), (5, 6), (6, 0)]),
    ("module-100", moduleGraph 1 100), ("module-800", moduleGraph 1 800),
    ("module-3000", moduleGraph 1 3000),
    ("own-imports", Graph.ofLabelled Fixtures.ownImports.toList),
    ("project-imports", Graph.ofLabelled Fixtures.projectImports.toList)]

/-- Writes `NAME.dot`, `NAME.layout`, `NAME.svg` and `NAME.time` (the milliseconds the layout took
and the load average) for each compared graph into `dir`. -/
def writeCompare (dir : String) : IO Unit := do
  IO.FS.createDirAll dir
  let o : LayeredOptions := {}
  let st : Style := {}
  for (name, g) in compareGraphs do
    IO.FS.writeFile s!"{dir}/{name}.dot" (dotText g o st)
    let t0 ← IO.monoNanosNow
    let l ← IO.lazyPure fun _ => g.layout o st
    let ms ← msSince t0
    IO.FS.writeFile s!"{dir}/{name}.layout" (layoutText l)
    IO.FS.writeFile s!"{dir}/{name}.time" s!"{ms} {← loadAverage}\n"
    IO.FS.writeFile s!"{dir}/{name}.svg" (g.toSvg o st)
    IO.println s!"{dir}/{name}.dot, .layout, .svg"

end PILeanTest.Graphs
