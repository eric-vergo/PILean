/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Color
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Graphs of nodes and edges

A `Graph` is a value: labelled nodes (numbered by their position in `nodes`), edges between node
numbers, optional clusters (named groups of nodes) and a flag for the whole graph telling
whether its edges are directed. The layouts (`PILean.Graph.Layered`, `PILean.Graph.Simple`) turn
it into boxes and curves and `PILean.Graph.Draw` draws those on the vector canvas.

## Validation

* An edge that names a node outside `nodes` is dropped by every layout (`Graph.validEdges`
  keeps the others, each with its position in `edges`); nothing else is changed.
* A self-loop is kept and drawn as a small loop beside its node.
* Parallel edges (several edges between the same nodes, in either direction) are kept and
  drawn side by side.
* Cluster members outside `nodes` are ignored.

## Main definitions

* `Graph`, `Graph.Node`, `Graph.Edge`, `Graph.Cluster`, `Graph.NodeShape`, `Graph.NodeStyle`.
* `Graph.ofPairs`, `Graph.ofNames`, `Graph.ofLabelled`: builders from lists of pairs.
* `Graph.validEdges`, `Graph.validIndices`.
-/

namespace PILean

namespace Graph

/-- The outline of a node. -/
inductive NodeShape where
  /-- A rectangle with square corners. -/
  | box
  /-- A rectangle with rounded corners (the default). -/
  | round
  /-- An ellipse. -/
  | ellipse
  deriving BEq, Inhabited, Repr

/-- Overrides of a node's look; `none` takes the value from the style. -/
structure NodeStyle where
  /-- The fill colour. -/
  fill : Option Rgba := none
  /-- The outline colour. -/
  stroke : Option Rgba := none
  /-- The outline shape. -/
  shape : Option NodeShape := none
  deriving Inhabited

/-- A node. -/
structure Node where
  /-- The text in the node. -/
  label : String
  /-- Overrides of the look. -/
  style : NodeStyle := {}
  deriving Inhabited

/-- An edge between two nodes (by number). -/
structure Edge where
  /-- The node the edge starts at. -/
  src : Nat
  /-- The node the edge ends at. -/
  dst : Nat
  /-- The text on the edge (nothing when empty). -/
  label : String := ""
  /-- Whether the edge points from `src` to `dst` (it shows an arrowhead when the graph is
  directed too). -/
  directed : Bool := true
  deriving Inhabited

/-- A named group of nodes. -/
structure Cluster where
  /-- The title. -/
  name : String
  /-- The numbers of the member nodes. -/
  members : Array Nat
  deriving Inhabited

end Graph

/-- A graph: nodes, edges and clusters (see the module docstring). -/
structure Graph where
  /-- The nodes; a node's number is its position. -/
  nodes : Array Graph.Node := #[]
  /-- The edges, between node numbers. -/
  edges : Array Graph.Edge := #[]
  /-- The clusters: groups of nodes drawn together in a labelled box. -/
  clusters : Array Graph.Cluster := #[]
  /-- Whether the graph's edges are directed (drawn with arrowheads); an edge is drawn with an
  arrowhead when both the graph and the edge are directed. -/
  directed : Bool := true
  deriving Inhabited

namespace Graph

/-- The graph with nodes `0, …, n - 1` (the largest number in `pairs` decides `n`) labelled by
their numbers and one edge per pair. -/
def ofPairs (pairs : List (Nat × Nat)) (directed : Bool := true) : Graph :=
  let n := pairs.foldl (fun m (a, b) => max m (max a b + 1)) 0
  { nodes := (Array.range n).map fun i => { label := toString i },
    edges := pairs.toArray.map fun (a, b) => { src := a, dst := b, directed },
    directed }

/-- The graph whose nodes carry the given labels and whose edges are the pairs of node
numbers. -/
def ofNames (names : Array String) (pairs : List (Nat × Nat)) (directed : Bool := true) :
    Graph :=
  { nodes := names.map fun s => { label := s },
    edges := pairs.toArray.map fun (a, b) => { src := a, dst := b, directed },
    directed }

/-- The graph with one node per distinct name in `pairs` (numbered by first appearance) and one
edge per pair. -/
def ofLabelled (pairs : List (String × String)) (directed : Bool := true) : Graph := Id.run do
  let mut idx : Std.HashMap String Nat := {}
  let mut names : Array String := #[]
  let mut es : Array Edge := #[]
  for (a, b) in pairs do
    for s in [a, b] do
      if !idx.contains s then
        idx := idx.insert s names.size
        names := names.push s
    es := es.push { src := idx.getD a 0, dst := idx.getD b 0, directed }
  return { nodes := names.map fun s => { label := s }, edges := es, directed }

/-- The edges paired with their positions in `edges`. -/
def indexedEdges (g : Graph) : Array (Nat × Edge) :=
  g.edges.mapIdx fun i e => (i, e)

/-- The edges whose two ends are nodes of the graph, each with its position in `edges`, in
order. -/
def validEdges (g : Graph) : Array (Nat × Edge) :=
  g.indexedEdges.filter fun (_, e) => e.src < g.nodes.size && e.dst < g.nodes.size

/-- The positions in `edges` of the edges that are kept. -/
def validIndices (g : Graph) : List Nat := (g.validEdges.map (·.1)).toList

end Graph

end PILean
