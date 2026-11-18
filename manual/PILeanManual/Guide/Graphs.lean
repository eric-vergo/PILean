/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILean
import PILean.Trust.Attr
import PILeanVersoManual
import PILeanManual.Meta
import PILeanManual.Pictures

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open PILeanVerso.Manual
open PILeanManual

#doc (Manual) "Graphs and Layout" =>
%%%
tag := "graphs"
%%%

```lean -show
namespace PILeanManual.Graphs
open PILean PILean.Trust
```

# Graphs as Values
%%%
tag := "graph-model"
%%%

A {name}`PILean.Graph` is labelled nodes (numbered by their position), edges between node
numbers (each with an optional label, directed or not), optional nested clusters (named groups of
nodes drawn in a box) and a flag saying whether the graph is directed. Builders take lists:
{name}`PILean.Graph.ofLabelled` (pairs of names), {name}`PILean.Graph.ofNames` (names and pairs of
numbers), {name}`PILean.Graph.ofPairs` (pairs of numbers) and {name}`PILean.Graph.ofRelation`
(a list and a relation on it).

```lean (name := graphEx)
def deps : Graph := Graph.ofLabelled [("Main", "Parser"), ("Main", "Eval"),
  ("Parser", "Lexer"), ("Eval", "Parser"), ("Eval", "Values"), ("Values", "Lexer")]

#eval deps.nodes.map (·.label)
#eval deps.edges.map fun e => (e.src, e.dst)
#eval deps.toSvg.length
```

```leanResult graphEx
```

What the layouts do with odd input: an edge that names a node outside `nodes` is dropped
({name}`PILean.Graph.validEdges` keeps the others, each with its position); a self-loop is kept and
drawn as a small loop beside its node; parallel edges are kept and drawn side by side; a node
listed by several clusters belongs to the deepest of them, and a cluster's `parent` must come
before it in `clusters`.

A graph is a figure as it is (the layered layout in the light style), or through
{name}`PILean.Trust.GraphFigure`, which adds layout options, a style and the scale of the PNG:

```lean
/-- The modules of a small interpreter and their imports. -/
@[figure]
def depsFigure : GraphFigure := { graph := deps }
```

:::figure PILeanManual.Graphs.depsFigure (alt := "Five boxes in layers: Main at the top; Eval below it; Parser and Values below Eval; Lexer at the bottom. Arrows from Main to Parser and Eval, Eval to Parser and Values, Parser and Values to Lexer.") (width := "40%")
:::

# The Layered Layout
%%%
tag := "graph-layered"
%%%

{name}`PILean.Graph.layout` draws a graph in layers, the method of Sugiyama, Tagawa and Toda as
refined by Gansner, Koutsofios, North and Vo, in phases whose work is bounded by the input:

1. *Cycle removal.* The edges that point backwards in a greedy order (Eades, Lin and Smyth) are
   reversed for the layout and drawn in their own direction; self-loops are set aside.
2. *Layers.* The layers of least total edge span, by network simplex, balanced; layers wider than
   `maxLayerWidth` are split into rows; then a repair pass ({name}`PILean.Graph.fixLayers`) moves
   a node down until every edge points to a deeper layer. A graph with clusters is layered from
   the inside out, so that every cluster keeps a block of layers to itself. When an edge has a
   label, the layers are doubled so that the label has a layer of its own.
3. *Crossing reduction.* Long edges become chains of dummy nodes; weighted-median sweeps with
   transposition run from several starting orders, and each search ends with sifting (Matuszewski,
   Schönfeld and Molitor); crossings are counted with a Fenwick tree.
4. *Coordinates.* Brandes and Köpf's four alignments, balanced, refined, then improved by network
   simplex on the weighted horizontal length of the edges, within a bound on the work.
5. *Edges.* Each edge is the shortest route through the free space beside the nodes of the layers
   it crosses, drawn as one curve that rounds the bends of that route and stays clear of the boxes
   and cluster sides beside it; or horizontal and vertical segments with rounded corners
   (`routing := .orthogonal`). Directed edges end in an arrowhead at the target's outline; labels
   sit on plates of the page colour.

Everything is deterministic: every tie is decided by node and edge numbers, and the starts of the
crossing reduction, which run at the same time, are compared as if they had run one after the
other, so the result does not depend on the number of processors. The options are the fields of
{name}`PILean.Graph.LayeredOptions` (direction, gaps, routing, the work budgets, node sizes, …):

```lean
/-- A small build graph with edge labels, laid out from left to right. -/
def build : Graph :=
  { nodes := #["source", "parse", "check", "lower", "emit", "report"].map fun s => { label := s }
    edges := #[{ src := 0, dst := 1 }, { src := 1, dst := 2, label := "syntax" },
      { src := 1, dst := 3 }, { src := 2, dst := 3, label := "types" }, { src := 3, dst := 4 },
      { src := 2, dst := 5 }, { src := 4, dst := 5 }] }

/-- The build graph from left to right, its edges as orthogonal segments. -/
@[figure]
def buildFigure : GraphFigure :=
  { graph := build, options := { direction := .leftToRight, routing := .orthogonal } }
```

:::figure PILeanManual.Graphs.buildFigure (alt := "Six boxes laid out from left to right: source, parse, check, lower, emit and report, joined by arrows made of horizontal and vertical segments with rounded corners; the edges from parse to check and from check to lower carry the labels 'syntax' and 'types'.")
:::

## Clusters
%%%
tag := "graph-clusters"
%%%

A cluster's nodes stand together in every layer between two borders, so that its box holds
exactly its nodes; nested clusters stand inside their parent's block. Where an edge would still
pass through a cluster that holds neither of its ends, the layers are found again with the two
kept one above the other, up to `clusterRounds` times, and the attempt with the fewest such edges
is kept.

```lean
/-- Two clusters, one inside the other, and a node outside both. -/
def nested : Graph :=
  { nodes := #["app", "ui", "views", "state", "core", "util", "tests"].map fun s =>
      { label := s }
    edges := #[{ src := 0, dst := 1 }, { src := 1, dst := 2 }, { src := 1, dst := 3 },
      { src := 2, dst := 4 }, { src := 3, dst := 4 }, { src := 4, dst := 5 },
      { src := 6, dst := 4 }, { src := 6, dst := 2 }]
    clusters := #[{ name := "front end", members := #[1] },
      { name := "widgets", members := #[2, 3], parent := some 0 },
      { name := "library", members := #[4, 5] }] }

/-- The graph with its clusters. -/
@[figure]
def nestedFigure : GraphFigure := { graph := nested }
```

:::figure PILeanManual.Graphs.nestedFigure (alt := "Seven nodes: app and tests outside any cluster; a box 'front end' holding ui and, inside it, a box 'widgets' holding views and state; a box 'library' below holding core and util. Arrows lead down from app through the front end into the library, and from tests to core and views.") (width := "60%")
:::

Two checks on the finished geometry list every violation: {name}`PILean.Graph.clusterProblems`
(every cluster box holds exactly its nodes and no part of another node's box; boxes nest or are
apart) and {name}`PILean.Graph.clearanceProblems` (no edge comes within two pixels of a node it
does not end at; an edge between nodes outside a cluster does not enter its box):

```lean (name := checksEx)
#eval Graph.clusterProblems nested (nested.layout {} Style.light)
#eval Graph.clearanceProblems nested (nested.layout {} Style.light)
```

```leanResult checksEx
```

## Proved and Tested
%%%
tag := "graph-proved"
%%%

Proved, from Lean's three standard axioms only: after cycle removal every edge points to a deeper
layer ({name}`PILean.Graph.assignLayers_lt`, and for the layerings of graphs with clusters and with
wide layers split {name}`PILean.Graph.assignNested_lt` and {name}`PILean.Graph.assignWide_lt`):
this holds by construction, because the layering ends with the repair pass, and the theorems are
about that pass. The routed edges of {name}`PILean.Graph.layout` are exactly the valid input
edges, in order, each once ({name}`PILean.Graph.layout_edges_complete`), each with that edge's own
ends ({name}`PILean.Graph.layout_edge_endpoints`).

Tested, not proved: where the nodes stand and how the routes run; that a route stays in its room
and is the shortest, that its curve stays in its zones and that no edge turns back across the
layers (checked on random cases and every measured graph, each check with a planted fault it must
report); that network simplex finds the layers on its own, without the repair pass (a test checks
on random graphs, the fixtures and the import graphs that the repair changes nothing there); the
sifting and seeded starts, the packing of components, mirrored layouts and the SVG for web pages.
The coordinates are floating point.

## Limits and Bounds
%%%
tag := "graph-limits"
%%%

The layout's work is bounded by the numbers of nodes and edges and by two work budgets,
`layerWork` (the layering) and `coordinateWork` (the coordinates: when it is used up, the best
assignment so far is kept), with a cap on the nodes of the layered graph, dummy nodes included
(`maxLayoutNodes`). The extra starts of the crossing reduction have a budget too, so a large graph
gets none, and sifting is skipped above a number of node pairs. Packing components
({name}`PILean.Graph.layoutPacked`) cannot make a drawing narrower than its widest component.

## Compared with Graphviz
%%%
tag := "graph-compare"
%%%

`docs/DESIGN.md` ("Graph layout", "Measured") compares the layered layout with Graphviz's `dot`
on the repository's graphs: crossings, edge length, area, the turning and inflections of an edge,
the nearest node to an edge, edges entering a foreign cluster, and time. The measures are computed
from the finished layouts by `lake exe pilean-test --graph-quality` and `--graph-quality-files`;
Graphviz's numbers are the recorded ones of Graphviz 16.1.0
(`PILeanTest/graphs/dot-recorded.tsv`), times are one run each with the machine under load. The
document's own summary of the table, in its words:

> Without clusters the drawings have about as many crossings as `dot`'s (0.75 to 1.23 times),
> shorter edges on most graphs (0.69 to 1.14 times; the tree 1.21, because the ends are spread
> along the node's side) and a smaller or similar area. \[…\] No edge comes nearer than 3.5 pixels
> to a node it does not end at, where `dot`'s edges touch or cross such nodes on most graphs.
> With clusters, layered from the inside out, the blueprint graphs have fewer crossings and
> shorter edges than `dot`'s (0.60 to 0.98 and 0.88 to 0.90 times) and no edge through a cluster
> it does not end in, at the cost of more turning (75 and 100 degrees an edge against 52 and 66:
> an edge goes round a cluster where `dot`'s goes through it) and of drawings that are about as
> tall as wide where `dot`'s are wide strips.

and on time:

> PILean takes one to two times as long as `dot` on most graphs without clusters (45 ms against
> 27 on blueprint A, 0.8 s against 0.4 s on the 800-node module graph) and up to seven times on
> the dense neighbourhoods (1.1 s against 0.16 s for 290 nodes), with the starts of the crossing
> reduction on several processors.

The full table, the graphs it was measured on, and what would close the remaining gaps are in
that document.

# Other Layouts
%%%
tag := "graph-simple"
%%%

{name}`PILean.Graph.circularLayout` puts the nodes on a circle in node order, the first at the
top, clockwise, with straight edges (parallel edges bent apart); {name}`PILean.Graph.treeLayout`
draws a rooted tree one level per depth, each parent centred over its children. Both need no
search (their work is linear in the nodes and edges), use the sizes and gaps of
{name}`PILean.Graph.LayeredOptions`, and give the same {name}`PILean.Graph.Layout`, so the same
drawing code applies.

```lean
/-- The cycle of eight nodes with its four long diagonals, undirected. -/
def ring : Graph :=
  Graph.ofPairs ((List.range 8).map (fun i => (i, (i + 1) % 8)) ++
    (List.range 4).map fun i => (i, i + 4)) (directed := false)

/-- The ring on a circle. -/
@[figure]
def ringFigure : PILeanManual.LaidOut := ⟨fun st => ring.circularLayout {} st⟩

/-- A binary tree of depth three. -/
def tree : Graph := Graph.ofPairs ((List.range 14).map fun i => ((i) / 2, i + 1))

/-- The tree, root at the top. -/
@[figure]
def treeFigure : PILeanManual.LaidOut := ⟨fun st => tree.treeLayout 0 {} st⟩
```

:::figure PILeanManual.Graphs.ringFigure (alt := "Eight numbered nodes on a circle, 0 at the top, each joined to its neighbours and to the node opposite.") (width := "40%")
:::

:::figure PILeanManual.Graphs.treeFigure (alt := "A binary tree with root 0, children 1 and 2, then 3 to 6, then 7 to 14 on the bottom level.") (width := "70%")
:::

# DOT In and Out
%%%
tag := "graph-dot"
%%%

{name}`PILean.Graph.layoutDot` reads the DOT that a program would hand to `dot -Tdot` (graphs and
digraphs, defaults, chains of edges, nested `cluster` subgraphs, labels, shapes, colours,
`rankdir`), lays the graph out, and writes laid-out DOT in Graphviz's conventions. The input is
untrusted and bounded ({name}`PILean.Graph.Dot.Limits`: bytes, nodes and edges, nesting,
attributes per item, string length); ports, HTML strings and subgraphs as edge ends are refused
with a message.

```lean (name := dotEx)
#eval (Graph.layoutDot "digraph { a -> b -> c; a -> c }").map fun out =>
  (out.splitOn "\n").take 3
#eval (Graph.layoutDot "digraph { a:p1 -> b }").map (·.length)
```

```leanResult dotEx
```

# Graphs in Web Pages
%%%
tag := "graph-web"
%%%

{name}`PILean.Graph.Layout.toWebSvg` writes a layout as one SVG element to be put into a page and
styled there: a group with class `node`, `edge` or `cluster` for each item, with the ids,
classes, titles and descriptions the caller gives, the colours as presentation attributes a
stylesheet can override, and the text as SVG text in the page's font (so the caller sizes the
nodes for it, with {name}`PILean.Graph.sansWidth` as the measure). What the caller passes is
escaped as text or as an attribute value, and the output carries no script, link, style attribute
or event handler. ({name}`PILean.Svg.isInert` refuses `javascript:` and `data:` inside any
attribute value, so an `id` that contains one makes the check fail, although the escaped text
would do no harm.) It is tested, not proved.
