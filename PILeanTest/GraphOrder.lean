/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILeanTest.Graphs

/-!
# Checks of the crossing reduction, component packing, mirrored layouts and the web SVG

Named checks of `PILean.Graph.Ordering` (`crossBothWays`, `siftLayer`, `shuffle`,
`initialLayersSeeded`, `orderLayers`), `PILean.Graph.Pack` (`components`, `layoutPacked`,
`Layout.mirror`), `Graph.Node.size` and `PILean.Graph.Web` (`sansWidth`, `Layout.toWebSvg`).
The crossing counts are checked against a count of every pair of edges, on small instances from
a fixed generator.
-/

namespace PILeanTest.GraphOrder

open PILean PILean.Graph

/-- `n` numbers below `bound` from the generator at state `s`, with the state after them. -/
def draws (s : UInt64) (n bound : Nat) : Array Nat × UInt64 := Id.run do
  let mut s := s
  let mut out := #[]
  for _ in [0:n] do
    let (s', r) := Graphs.next s
    s := s'
    out := out.push (r % bound)
  return (out, s)

/-- The pairs of edges `(a, b)`, positions in two adjacent layers, that cross. -/
def crossingPairs (edges : Array (Nat × Nat)) : Nat := Id.run do
  let mut n := 0
  for i in [0:edges.size] do
    for j in [i + 1:edges.size] do
      let (a, b) := edges.getD i (0, 0)
      let (c, d) := edges.getD j (0, 0)
      if (a < c && d < b) || (c < a && b < d) then n := n + 1
  return n

/-- A layered graph from the generator: `sizes` nodes in each layer (the nodes numbered from the
top layer down) and about `density` edges per node into the layer below. Returns the layer of
every node, the neighbours above and below of every node. -/
def layered (seed : Nat) (sizes : Array Nat) (density : Nat) :
    Array Nat × Array (Array Nat) × Array (Array Nat) := Id.run do
  let total := sizes.foldl (· + ·) 0
  let mut layerAll : Array Nat := #[]
  let mut start : Array Nat := #[]
  for i in [0:sizes.size] do
    start := start.push layerAll.size
    for _ in [0:sizes.getD i 0] do layerAll := layerAll.push i
  let mut up : Array (Array Nat) := Array.replicate total #[]
  let mut down : Array (Array Nat) := Array.replicate total #[]
  let mut s : UInt64 := seed.toUInt64 * 2654435761 + 99
  for i in [0:sizes.size - 1] do
    for k in [0:sizes.getD i 0] do
      let u := start.getD i 0 + k
      let (rs, s') := draws s density (sizes.getD (i + 1) 1)
      s := s'
      for r in rs do
        let v := start.getD (i + 1) 0 + r
        unless (down.getD u #[]).contains v do
          down := down.modify u (·.push v)
          up := up.modify v (·.push u)
  return (layerAll, up, down)

/-- The nodes of every layer, in node order. -/
def layersOf (layerAll : Array Nat) : Array (Array Nat) :=
  let count := layerAll.foldl (fun m l => max m (l + 1)) 0
  (Array.range layerAll.size).foldl (fun ls v => ls.modify (layerAll.getD v 0) (·.push v))
    (Array.replicate count #[])

/-- The crossings of the whole order counted over every pair of edges of adjacent layers. -/
def bruteTotal (order : Array (Array Nat)) (down : Array (Array Nat)) : Nat := Id.run do
  let pos := positionsOf (order.foldl (fun s l => s + l.size) 0) order
  let mut total := 0
  for i in [0:order.size - 1] do
    let edges := (order.getD i #[]).foldl (fun es u =>
      es ++ ((down.getD u #[]).map fun v => (pos.getD u 0, pos.getD v 0))) #[]
    total := total + crossingPairs edges
  return total

/-- Whether `b` holds the same elements as `a`, each as often. -/
def samePerm (a b : Array Nat) : Bool :=
  a.size == b.size && (a.qsort (· < ·)) == (b.qsort (· < ·))

/-- Sorted arrays of positions from the generator. -/
def sortedDraws (s : UInt64) (n bound : Nat) : Array Nat × UInt64 :=
  let (xs, s) := draws s n bound
  (xs.qsort (· < ·), s)

/-- `crossBothWays` against a count of every pair, on `cases` generated pairs of neighbour
positions. -/
def crossBothWaysOk (cases : Nat) : Bool := Id.run do
  let mut s : UInt64 := 12345
  let mut ok := true
  for _ in [0:cases] do
    let (ns, s1) := draws s 2 7
    let (a, s2) := sortedDraws s1 (ns.getD 0 0) 8
    let (b, s3) := sortedDraws s2 (ns.getD 1 0) 8
    s := s3
    let mut uLeft := 0
    let mut vLeft := 0
    for x in a do
      for y in b do
        if y < x then uLeft := uLeft + 1
        if x < y then vLeft := vLeft + 1
    if crossBothWays a b != (uLeft, vLeft) then ok := false
  return ok

/-- A three-layer instance from the generator: the layers, their neighbours, and the middle layer
shuffled. Returns the order and the neighbours. -/
def instanceOf (seed : Nat) (three : Bool) :
    Array (Array Nat) × Array (Array Nat) × Array (Array Nat) :=
  let sizes := if three then #[3 + seed % 3, 4 + seed % 4, 3 + seed % 2] else #[3 + seed % 3,
    4 + seed % 4]
  let (layerAll, up, down) := layered seed sizes (1 + seed % 3)
  let order := layersOf layerAll
  let (mid, _) := shuffle (order.getD 1 #[]) (seed.toUInt64 + 5)
  (order.setIfInBounds 1 mid, up, down)

/-- What `siftLayer` does on the middle layer of the instance `seed`: whether it returns a
permutation, never more crossings than it was given, no change when it reports none better, and
fewer crossings when it reports a better one. -/
def siftOk (seed : Nat) (three : Bool) : Bool :=
  let (order, up, down) := instanceOf seed three
  let size := order.foldl (fun s l => s + l.size) 0
  let pos := positionsOf size order
  let sorted := fun (nbr : Array (Array Nat)) (v : Nat) =>
    ((nbr.getD v #[]).map fun u => pos.getD u 0).qsort (· < ·)
  let (r, better) := siftLayer (order.getD 1 #[]) (sorted up) (sorted down)
  let after := order.setIfInBounds 1 r
  let before := bruteTotal order down
  let now := bruteTotal after down
  samePerm r (order.getD 1 #[]) && now ≤ before && (better || r == order.getD 1 #[]) &&
    (!better || now < before)

/-- Whether `orderLayers` and `initialLayersSeeded` hold on the layered graph `seed`: every node
once in its own layer, a permutation per layer, and the same on a second call. -/
def orderOk (seed : Nat) : Bool :=
  let sizes := #[2 + seed % 4, 3 + seed % 5, 3 + seed % 3, 2 + seed % 4]
  let (layerAll, up, down) := layered seed sizes (1 + seed % 3)
  let layers := layersOf layerAll
  let seeded := initialLayersSeeded layerAll up down seed
  let ordered := orderLayers layerAll up down 8
  let perLayer := fun (o : Array (Array Nat)) =>
    o.size == layers.size && (Array.range layers.size).all fun i =>
      samePerm (o.getD i #[]) (layers.getD i #[])
  perLayer seeded && perLayer ordered && seeded == initialLayersSeeded layerAll up down seed &&
    ordered == orderLayers layerAll up down 8 &&
    -- the crossings of the result are those of the best of the plain starts
    bruteTotal ordered down ≤ bruteTotal (initialLayers layerAll up down) down

/-- Whether a layout lists a box for every node of `g`, of the size of `nodeSize`. -/
def boxesOfSize (g : Graph) (l : Layout) : Bool :=
  l.nodes.size == g.nodes.size && (Array.range g.nodes.size).all fun i =>
    let (w, h) := nodeSize {} {} (g.nodes.getD i default)
    let b := (l.nodes.getD i default).box
    (b.width - w).abs < 1e-6 && (b.height - h).abs < 1e-6 && (l.nodes.getD i default).index == i

/-- Whether no two node boxes of the layout overlap. -/
def noOverlaps (l : Layout) : Bool :=
  (Array.range l.nodes.size).all fun i => (Array.range i).all fun j =>
    !Graphs.overlap (l.nodes.getD i default).box (l.nodes.getD j default).box

/-- A graph of three components (the first with a cluster, the second with a nested cluster pair),
an isolated node, and an edge to a node that does not exist. -/
def several : Graph :=
  { nodes := (Array.range 12).map fun v => { label := s!"node {v}" },
    edges := #[(0, 1), (1, 2), (3, 4), (3, 5), (4, 6), (7, 8), (0, 99), (8, 9)].map
      fun (a, b) => { src := a, dst := b },
    clusters := #[{ name := "First", members := #[0, 1] },
      { name := "Second", members := #[3, 4] },
      { name := "Inside", members := #[5], parent := some 1 },
      { name := "Third", members := #[7, 8] }] }

/-- The graph of `n` components of two nodes each. -/
def pairs (n : Nat) : Graph :=
  { nodes := (Array.range (2 * n)).map fun v => { label := s!"p{v}" },
    edges := (Array.range n).map fun k => { src := 2 * k, dst := 2 * k + 1 } }

/-- The positions of the box of node `i` in `l` (corners). -/
def boxOf (l : Layout) (i : Nat) : Box := (l.nodes.getD i default).box

/-- Whether two boxes agree to within `1e-6`. -/
def sameBox (a b : Box) : Bool :=
  (a.x0 - b.x0).abs < 1e-6 && (a.y0 - b.y0).abs < 1e-6 && (a.x1 - b.x1).abs < 1e-6 &&
    (a.y1 - b.y1).abs < 1e-6

/-- How often `t` occurs in `s`. -/
def count (s t : String) : Nat := (s.splitOn t).length - 1

/-- A hostile string for text positions. -/
def hostile : String := "\"<>&'</script>javascript:alert(1)<img onerror=x>"

/-- Nodes of every shape, dashed or not, with hostile strings where a caller's text goes. -/
def webNodes : Array WebNode :=
  #[{ id := "n0", classes := "a b", name := hostile, tooltip := hostile,
      lines := #[hostile, "second"], shape := .box, dash := "4 2" },
    { id := "n1", shape := .round, lines := #["x"], fill := "\"><script>alert(1)</script>",
      stroke := "red\" onclick=\"alert(1)", ink := "'" },
    { id := "n2", classes := "c\" onload=\"alert(1)", shape := .ellipse, lines := #["e"] },
    { id := "n3", classes := "d", shape := .tab, name := "tab", dash := "1" },
    { id := "n4<>&\"'", lines := #[hostile], name := "q" }]

/-- A graph with clusters and a layout for it, five nodes of the shapes above. -/
def webGraph : Graph :=
  { nodes := (Array.range 5).map fun v => { label := s!"n{v}", size := some (60, 24) },
    edges := #[(0, 1), (1, 2), (2, 3), (0, 4), (3, 4)].map fun (a, b) => { src := a, dst := b },
    clusters := #[{ name := hostile, members := #[0, 1] }] }

/-- The web SVG of `webGraph`. -/
def webSvg : String :=
  webGraph.layout.toWebSvg webNodes #[{ classes := "e\" onload=\"x", dash := "3 3" }]
    { classes := "w\" onload=\"x", attrs := #[("data-x", "\"<>&")] }

/-- What `isInert` says of the web SVG of a node whose `id` is `s`. -/
def inertWithId (s : String) : Bool :=
  Svg.isInert (webGraph.layout.toWebSvg #[{ id := s }] #[])

/-- The web SVG of a node with `javascript:` and `data:` in the places where text goes. -/
def textOnly : String :=
  let js := "javascript:alert(1)"
  let n : WebNode := { name := js, tooltip := js, lines := #[js, "data:text/html,x"] }
  webGraph.layout.toWebSvg #[n] #[]

/-- The checks of this module. -/
def checks : Array (String × Bool) :=
  let range := fun (n : Nat) => Array.range n
  let lay := several.layout
  let pk := several.layoutPacked
  let connected : Graph := Graph.ofPairs [(0, 1), (1, 2), (0, 2), (2, 3)]
  let mirrored := pk.mirror true
  let sideways := pk.mirror false
  let many := (pairs 30).layoutPacked
  let sizes : Graph :=
    { nodes := #[{ label := "a", size := some (100, 40) },
        { label := "b", size := some (101.3, 25) },
        { label := "c", size := some (1, 1) }, { label := "d" }],
      edges := #[{ src := 0, dst := 1 }, { src := 2, dst := 3 }] }
  let shelf := shelves #[(100, 50), (60, 80), (60, 40), (30, 80)] 10 1
  #[("crossBothWays: agrees with a count of every pair on 60 cases", crossBothWaysOk 60),
    ("crossBothWays: nothing against an empty list",
      crossBothWays #[] #[1, 2] == (0, 0) && crossBothWays #[1, 2] #[] == (0, 0)),
    ("crossBothWays: equal positions do not cross",
      crossBothWays #[3] #[3] == (0, 0) && crossBothWays #[1] #[2] == (0, 1) &&
        crossBothWays #[2] #[1] == (1, 0)),
    ("siftLayer: two layers: a permutation, never worse, as reported (30 instances)",
      (range 30).all (siftOk · false)),
    ("siftLayer: three layers: a permutation, never worse, as reported (30 instances)",
      (range 30).all (siftOk · true)),
    ("siftLayer: sifts a layer that has crossings clear",
      let order : Array (Array Nat) := #[#[0, 1, 2], #[3, 4, 5]]
      let down : Array (Array Nat) := #[#[5], #[4], #[3], #[], #[], #[]]
      let up : Array (Array Nat) := #[#[], #[], #[], #[2], #[1], #[0]]
      let pos := positionsOf 6 order
      let sorted := fun (nbr : Array (Array Nat)) (v : Nat) =>
        ((nbr.getD v #[]).map fun u => pos.getD u 0).qsort (· < ·)
      let (r, better) := siftLayer #[3, 4, 5] (sorted up) (sorted down)
      better && bruteTotal #[#[0, 1, 2], r] down == 0),
    ("shuffle: a permutation, the same on every call, for sizes 0 to 20",
      (range 21).all fun n =>
        let xs := range n
        let (a, s) := shuffle xs (n.toUInt64 * 7 + 1)
        samePerm a xs && (shuffle xs (n.toUInt64 * 7 + 1)).1 == a && (n < 2 || s != n.toUInt64)),
    ("shuffle: different seeds give different orders",
      (shuffle (range 12) 1).1 != (shuffle (range 12) 2).1),
    ("nextRandom: below 2^31 and the same on every call",
      let (s, r) := nextRandom 42
      r < 2147483648 && nextRandom 42 == (s, r) && s != 42),
    ("initialLayersSeeded: every node once, in its own layer; the same on every call",
      (range 20).all fun seed =>
        let (layerAll, up, down) := layered seed #[3, 4, 4, 2] 2
        let r := initialLayersSeeded layerAll up down seed
        r.size == 4 && (range 4).all (fun i => samePerm (r.getD i #[]) ((layersOf layerAll).getD i
          #[])) && r == initialLayersSeeded layerAll up down seed),
    ("initialLayersSeeded: other seeds reorder",
      let (layerAll, up, down) := layered 1 #[1, 10, 10] 2
      (range 8).any fun k => initialLayersSeeded layerAll up down k !=
        initialLayersSeeded layerAll up down 0),
    ("orderLayers: a permutation per layer, deterministic, no worse than the first start",
      (range 25).all orderOk),
    ("extraStarts: as many as the work allows, at most the asked",
      extraStarts 100 24 == 24 && extraStarts 100000 24 == 6 && extraStarts 0 5 == 5 &&
        extraStarts 10000000 24 == 0),
    ("components: two components",
      components (Graph.ofPairs [(0, 1), (2, 3)]) == #[0, 0, 1, 1]),
    ("components: an isolated node is its own component",
      components (Graph.ofNames #["a", "b", "c"] [(0, 1)]) == #[0, 0, 1]),
    ("components: numbered by the first node of each",
      components (Graph.ofPairs [(0, 3), (1, 2)]) == #[0, 1, 1, 0]),
    ("components: a cluster joins its members",
      let g := Graph.ofPairs [(0, 1), (2, 3)]
      components { g with clusters := #[{ name := "C", members := #[0, 2] }] } == #[0, 0, 0, 0]),
    ("components: nested clusters join the members of the top cluster",
      let g := Graph.ofPairs [(0, 1), (2, 3), (4, 5)]
      let nested := #[({ name := "A", members := #[0] } : Graph.Cluster),
        { name := "B", members := #[2], parent := some 0 },
        { name := "C", members := #[4] }]
      components { g with clusters := nested } == #[0, 0, 0, 0, 1, 1] &&
        components { g with clusters := nested.modify 1 ({ · with members := #[2, 4] }) } ==
          #[0, 0, 0, 0, 0, 0]),
    ("components: an edge to a node that does not exist joins nothing",
      components { nodes := #[{ label := "a" }, { label := "b" }],
                   edges := #[{ src := 0, dst := 5 }] } == #[0, 1]),
    ("components: no nodes, no components", components {} == #[]),
    ("component: the nodes kept, the edges between them, the clusters with their members",
      let (sub, origin) := component several #[3, 4, 5, 6]
      sub.nodes.size == 4 && origin == #[2, 3, 4] && sub.edges.size == 3 &&
        sub.clusters.map (·.members) == #[#[], #[0, 1], #[2], #[]]),
    ("shelves: no two boxes overlap, the first of the tallest at the origin",
      (range 4).all fun i => (range i).all fun j =>
        let (x, y) := shelf.getD i (0, 0)
        let (u, v) := shelf.getD j (0, 0)
        let size := fun (k : Nat) => #[(100, 50), (60, 80), (60, 40), (30, 80)].getD k (0, 0)
        !(x < u + (size j).1 && u < x + (size i).1 && y < v + (size j).2 && v < y + (size i).2)),
    ("shelves: no boxes, no places", (shelves #[] 10 1.6).size == 0),
    ("layoutPacked: a box of the size of nodeSize for every node", boxesOfSize several pk),
    ("layoutPacked: no two node boxes overlap", noOverlaps pk),
    ("layoutPacked: the edges are the valid edges, by index and in order",
      pk.edges.map (·.index) == several.validEdges.map (·.1) &&
        (pk.edges.zip several.validEdges).all fun (r, (_, e)) => r.src == e.src && r.dst == e.dst),
    ("layoutPacked: a graph of one component has the layout of layout",
      connected.layoutPacked.toSvg {} == connected.toSvg),
    ("layoutPacked: the same twice",
      several.layoutPacked.toSvg {} == several.layoutPacked.toSvg {}),
    ("layoutPacked: cluster boxes hold exactly their nodes and nest",
      (clusterProblems several pk).isEmpty && pk.clusters.size == 4),
    ("layoutPacked: no edge passes a node",
      ((clearanceProblems several pk).filter (Graphs.has · "passes node")).isEmpty),
    ("layoutPacked: the components stand in rows, wider than tall by less than the layout",
      decide (pk.width < lay.width)),
    ("layoutPacked: thirty components of two nodes make a picture of ordinary proportions",
      many.width < 4 * many.height && (pairs 30).layout.width > 2 * many.width),
    ("layoutPacked: left to right too",
      let l := several.layoutPacked { direction := .leftToRight }
      noOverlaps l && (clusterProblems several l).isEmpty),
    ("mirror: twice gives the same node boxes, the same size",
      let twice := (mirrored.mirror true)
      (range 12).all (fun i => sameBox (boxOf pk i) (boxOf twice i)) &&
        twice.width == pk.width && twice.height == pk.height &&
        mirrored.width == pk.width && mirrored.height == pk.height),
    ("mirror: upside down flips every box in the picture, left to right too",
      (range 12).all (fun i =>
        let b := boxOf pk i
        let m := boxOf mirrored i
        let s := boxOf sideways i
        (m.y0 - (pk.height - b.y1)).abs < 1e-6 && (m.x0 - b.x0).abs < 1e-6 &&
          (s.x0 - (pk.width - b.x1)).abs < 1e-6 && (s.y0 - b.y0).abs < 1e-6 &&
          (m.width - b.width).abs < 1e-6 && (s.height - b.height).abs < 1e-6)),
    ("mirror: the routes keep their ends on the nodes they join",
      mirrored.edges.size == pk.edges.size &&
        ((clearanceProblems several mirrored).filter (Graphs.has · "passes node")).isEmpty),
    ("Node.size: the box has the size given, made even",
      let l := sizes.layout
      let b := fun (i : Nat) => boxOf l i
      (b 0).width == 100 && (b 0).height == 40 && (b 1).width == 102 && (b 1).height == 26 &&
        (b 2).width == 2 && (b 2).height == 2 && (b 3).width > 2 && boxesOfSize sizes l &&
        boxesOfSize sizes sizes.layoutPacked),
    ("sansWidth: nothing for an empty text, additive over concatenation",
      sansWidth "" 10 == 0 &&
        ["", "a", "Hello", "iii", "Wm. Q", "é", "文字"].all fun a =>
          ["", "b", "World", " -_", "i"].all fun b =>
            (sansWidth (a ++ b) 12 - (sansWidth a 12 + sansWidth b 12)).abs < 1e-9),
    ("sansWidth: the width of Hello in Helvetica's metrics",
      (sansWidth "Hello" 10 - 22.78).abs < 1e-9 && (sansWidth "iii" 1000 - 666).abs < 1e-9),
    ("toWebSvg: the output is inert with clusters, dashes, every shape and hostile strings",
      Svg.isInert webSvg),
    ("toWebSvg: hostile text is escaped in elements and attributes",
      !Graphs.has webSvg "<script" && !Graphs.has webSvg "</script>" &&
        !Graphs.has webSvg "<img" && !Graphs.has webSvg "\" onclick=\"" &&
        !Graphs.has webSvg "\" onload=\"" && Graphs.has webSvg "&lt;/script&gt;" &&
        Graphs.has webSvg "&quot;"),
    ("toWebSvg: every node id once, one node group per node",
      (range 4).all (fun i => count webSvg s!"id=\"n{i}\"" == 1) &&
        count webSvg "id=\"n4&lt;&gt;&amp;&quot;&#39;\"" == 1 &&
        count webSvg "class=\"node\"" + count webSvg "class=\"node " == 5 &&
        count webSvg "<title>" == 5 && count webSvg "<desc>" == 1),
    ("toWebSvg: a path per edge, a group per cluster, an ellipse, a dashed outline, the heads",
      count webSvg "class=\"edge " + count webSvg "class=\"edge\"" == 5 &&
        count webSvg "<g class=\"cluster\">" == 1 && count webSvg "<ellipse" == 1 &&
        Graphs.has webSvg "stroke-dasharray=\"4 2\"" && count webSvg "<g class=\"heads\"" == 1),
    ("toWebSvg: the same twice",
      webSvg == webGraph.layout.toWebSvg webNodes #[{ classes := "e\" onload=\"x", dash := "3 3" }]
        { classes := "w\" onload=\"x", attrs := #[("data-x", "\"<>&")] }),
    ("toWebSvg: javascript: in text positions is accepted by isInert", Svg.isInert textOnly),
    ("toWebSvg: isInert refuses javascript: in an id, which is an attribute value",
      !inertWithId "javascript:alert(1)" && inertWithId "javascript"),
    ("toWebSvg: nodes without entries get the defaults",
      let s := webGraph.layout.toWebSvg #[] #[]
      Svg.isInert s && count s "class=\"node\"" == 5 && !Graphs.has s "id="),
    ("toWebSvg: the element has the layout's size",
      let l := webGraph.layout
      Graphs.has (webGraph.layout.toWebSvg #[] #[]) s!"width=\"{fmtNum l.width 0}\""),
    ("tabPath: starts above the box, closed",
      let p := tabPath ⟨0, 10, 100, 40⟩
      p.cmds.size == 7)]

end PILeanTest.GraphOrder
