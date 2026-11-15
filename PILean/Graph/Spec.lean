/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Graph.Proofs
import PILean.Graph.Draw

/-!
# Graphs with an exact specification

`Graph.ofRelation nodes r label` is the graph of a relation `r` on a finite list of nodes: one
node per list entry (numbered by position, labelled by `label`) and one edge `(i, j)` for each
pair of positions whose entries are related, in the order of `i`, then `j`. The edge list is
`relationPairs nodes r`.

* `ofRelation_node_labels`, `ofRelation_nodes_size`: the nodes are exactly the input nodes, in
  order.
* `mem_relationPairs`, `relationPairs_nodup`, `ofRelation_edge_pairs`: the edges are exactly the
  related pairs, each once.
* `layout_edge_endpoints`: for any graph, the routes of the layered layout are the valid edges
  with their ends, in order, one route per edge.
* `ofRelation_layout_edges`: the routes drawn for `Graph.ofRelation nodes r label` are exactly
  the pairs of `relationPairs nodes r`, in order, each once, route `i` having index `i`.
* `ofNames_layout_edges`: the same for a graph made from an edge list with `Graph.ofNames`
  whose pairs all name nodes.

A long edge (one that spans more than one layer) is routed through dummy nodes inside the
layout; it is still *one* route of the layout (`RoutedEdge`), whose `points` include the dummy
points. So the drawn edges are the graph's edges one for one, whatever the layering does.
`Layout.draw` draws `l.edges.map (·.draw st)` (`Layout.draw_edges`), so the edges in the picture
are the routes of the layout.

Not proved: where the boxes and curves lie (layer assignment, ordering, coordinates, curves are
tested for quality: no overlaps, edges leave and enter the right boxes), and the node labels'
rendering. `Graph.ofLabelled` (which numbers names by first appearance with a hash map) is
tested, not proved. Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace PILean

namespace Graph

/-- Whether the entries at positions `i` and `j` of `nodes` exist and are related by `r`. -/
def relHolds {α : Type} (nodes : List α) (r : α → α → Bool) (i j : Nat) : Bool :=
  match nodes[i]?, nodes[j]? with
  | some a, some b => r a b
  | _, _ => false

/-- The pairs of positions of related nodes, in the order of the first position, then the
second. -/
def relationPairs {α : Type} (nodes : List α) (r : α → α → Bool) : List (Nat × Nat) :=
  (List.range nodes.length).flatMap fun i =>
    ((List.range nodes.length).filter fun j => relHolds nodes r i j).map fun j => (i, j)

/-- The graph of the relation `r` on the list `nodes`: node `i` is labelled `label nodes[i]`,
and there is one edge `i → j` for every pair of positions with `r nodes[i] nodes[j]`. -/
def ofRelation {α : Type} (nodes : List α) (r : α → α → Bool) (label : α → String)
    (directed : Bool := true) : Graph :=
  { nodes := (nodes.map fun a => ({ label := label a } : Graph.Node)).toArray,
    edges := ((relationPairs nodes r).map fun (i, j) =>
      ({ src := i, dst := j, directed } : Graph.Edge)).toArray,
    directed }

/-- The nodes of `ofRelation` are the input nodes' labels, in order. -/
theorem ofRelation_node_labels {α : Type} (nodes : List α) (r : α → α → Bool)
    (label : α → String) (directed : Bool) :
    ((ofRelation nodes r label directed).nodes.toList.map (·.label)) = nodes.map label := by
  simp [ofRelation, Function.comp_def]

/-- There is one node for each input node. -/
theorem ofRelation_nodes_size {α : Type} (nodes : List α) (r : α → α → Bool)
    (label : α → String) (directed : Bool) :
    (ofRelation nodes r label directed).nodes.size = nodes.length := by
  simp [ofRelation]

/-- A pair of positions is an edge exactly when both name input nodes and those are related. -/
theorem mem_relationPairs {α : Type} (nodes : List α) (r : α → α → Bool) (i j : Nat) :
    (i, j) ∈ relationPairs nodes r ↔
      ∃ a b, nodes[i]? = some a ∧ nodes[j]? = some b ∧ r a b = true := by
  simp only [relationPairs, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi', j', ⟨hj', hr⟩, rfl, rfl⟩
    unfold relHolds at hr
    split at hr
    · rename_i a b ha hb
      exact ⟨a, b, ha, hb, hr⟩
    · simp at hr
  · rintro ⟨a, b, ha, hb, hab⟩
    have hi : i < nodes.length := (List.getElem?_eq_some_iff.1 ha).1
    have hj : j < nodes.length := (List.getElem?_eq_some_iff.1 hb).1
    exact ⟨i, hi, j, ⟨hj, by simp [relHolds, ha, hb, hab]⟩, rfl, rfl⟩

/-- Each pair is an edge once. -/
theorem relationPairs_nodup {α : Type} (nodes : List α) (r : α → α → Bool) :
    (relationPairs nodes r).Nodup := by
  unfold relationPairs
  rw [List.nodup_iff_pairwise_ne, List.pairwise_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact (List.nodup_range.sublist List.filter_sublist).imp fun h h' => h (by simpa using h')
  · refine List.pairwise_lt_range.imp fun {i i'} hlt => ?_
    intro p hp p' hp'
    simp only [List.mem_map] at hp hp'
    obtain ⟨j, _, rfl⟩ := hp
    obtain ⟨j', _, rfl⟩ := hp'
    intro h
    simp only [Prod.mk.injEq] at h
    omega

/-- The edges of `ofRelation`, as pairs of node numbers, are exactly `relationPairs`, in
order. -/
theorem ofRelation_edge_pairs {α : Type} (nodes : List α) (r : α → α → Bool)
    (label : α → String) (directed : Bool) :
    (ofRelation nodes r label directed).edges.toList.map (fun e => (e.src, e.dst)) =
      relationPairs nodes r := by
  simp [ofRelation, Function.comp_def]

/-- Every edge of `ofRelation` joins two nodes. -/
theorem ofRelation_edges_valid {α : Type} (nodes : List α) (r : α → α → Bool)
    (label : α → String) (directed : Bool) :
    ∀ e ∈ (ofRelation nodes r label directed).edges,
      e.src < (ofRelation nodes r label directed).nodes.size ∧
      e.dst < (ofRelation nodes r label directed).nodes.size := by
  intro e he
  simp only [ofRelation, List.mem_toArray, List.mem_map, List.size_toArray] at he ⊢
  obtain ⟨⟨i, j⟩, hp, rfl⟩ := he
  obtain ⟨a, b, ha, hb, _⟩ := (mem_relationPairs nodes r i j).1 hp
  simpa using ⟨(List.getElem?_eq_some_iff.1 ha).1, (List.getElem?_eq_some_iff.1 hb).1⟩

/-! ### The layout's routes -/

/-- A route has the ends of the edge it was made for. -/
theorem routeOne_ends (pl : Plan) (k i : Nat) (e : Graph.Edge) :
    (routeOne pl k i e).src = e.src ∧ (routeOne pl k i e).dst = e.dst := by
  simp only [routeOne]
  split <;> exact ⟨rfl, rfl⟩

/-- Fitting a layout keeps the ends of its routes. -/
theorem fit_ends (l : Layout) (margin : Float) :
    (l.fit margin).edges.map (fun e => (e.index, e.src, e.dst)) =
      l.edges.map (fun e => (e.index, e.src, e.dst)) := by
  unfold Layout.fit
  split <;> simp [Layout.translate, Array.map_map, Function.comp_def]

/-- The routes of the layered layout are the valid edges with their ends, in order: one route
for each valid edge, by index. A long edge is one route whose `points` pass through its dummy
nodes. -/
theorem layout_edge_endpoints (g : Graph) (o : LayeredOptions) (st : Style) :
    (g.layout o st).edges.map (fun e => (e.index, e.src, e.dst)) =
      g.validEdges.map (fun (i, e) => (i, e.src, e.dst)) := by
  unfold layout
  rw [fit_ends]
  unfold layoutRaw
  simp only [routeAll]
  apply Array.ext
  · simp
  · intro i h1 h2
    simp [routeOne_index, (routeOne_ends _ _ _ _).1, (routeOne_ends _ _ _ _).2]

/-- The layout draws its edges as the shapes of its routes. -/
theorem Layout.draw_edges (l : Layout) (st : Style) :
    l.draw st = .group (#[.path (Canvas.rect 0 0 l.width l.height) (some (.solid st.background))
      none] ++ l.clusters.map (·.draw st) ++ l.edges.map (·.draw st) ++
      l.nodes.map (·.draw st)) := rfl

/-- The picture of a graph is the drawing of its layered layout. -/
theorem draw_eq (g : Graph) (o : LayeredOptions) (st : Style) :
    g.draw o st = (g.layout o st).draw st := rfl

/-- When every edge joins two nodes, the routes of the layered layout are the edges, in order:
route `i` has index `i` and the ends of `edges[i]`. -/
theorem layout_edges_of_valid (g : Graph) (o : LayeredOptions) (st : Style)
    (hv : ∀ e ∈ g.edges, e.src < g.nodes.size ∧ e.dst < g.nodes.size) :
    (g.layout o st).edges.toList.map (fun e => (e.index, e.src, e.dst)) =
      (List.range g.edges.size).zip (g.edges.toList.map fun e => (e.src, e.dst)) := by
  have h := layout_edge_endpoints g o st
  have hl := congrArg Array.toList h
  simp only [Array.toList_map] at hl
  rw [hl]
  have hve : g.validEdges = g.indexedEdges := by
    unfold validEdges
    apply Array.filter_eq_self.2
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
    have hi' : i < g.edges.size := by simpa [indexedEdges] using hi
    have := hv g.edges[i] (Array.getElem_mem hi')
    simpa [indexedEdges] using this
  rw [hve]
  apply List.ext_getElem
  · simp [indexedEdges]
  · intro i h1 h2
    simp [indexedEdges]

/-- The routes drawn for the graph of a relation are exactly the related pairs of nodes, in
order, each once: route `i` has index `i` and the ends of the `i`-th pair of `relationPairs`. -/
theorem ofRelation_layout_edges {α : Type} (nodes : List α) (r : α → α → Bool)
    (label : α → String) (directed : Bool) (o : LayeredOptions) (st : Style) :
    ((ofRelation nodes r label directed).layout o st).edges.toList.map
        (fun e => (e.index, e.src, e.dst)) =
      (List.range (relationPairs nodes r).length).zip (relationPairs nodes r) := by
  rw [layout_edges_of_valid _ o st (ofRelation_edges_valid nodes r label directed),
    ofRelation_edge_pairs]
  simp [ofRelation]

/-- The routes drawn for a graph made from an edge list with `Graph.ofNames`, when every pair
names two nodes, are exactly the pairs of the list, in order: route `i` has index `i` and the
ends of the `i`-th pair. -/
theorem ofNames_layout_edges (names : Array String) (pairs : List (Nat × Nat)) (directed : Bool)
    (hv : ∀ p ∈ pairs, p.1 < names.size ∧ p.2 < names.size) (o : LayeredOptions) (st : Style) :
    ((ofNames names pairs directed).layout o st).edges.toList.map
        (fun e => (e.index, e.src, e.dst)) =
      (List.range pairs.length).zip pairs := by
  rw [layout_edges_of_valid]
  · simp [ofNames, Function.comp_def]
  · intro e he
    simp only [ofNames, List.map_toArray, List.mem_toArray,
      List.mem_map] at he
    obtain ⟨p, hp, rfl⟩ := he
    simpa [ofNames] using hv p hp

/-- The hypotheses can be met: the 2-cycle relation on two nodes has exactly the edges
`(0, 1)` and `(1, 0)`. -/
example : relationPairs [1, 2] (fun a b => a != b) = [(0, 1), (1, 0)] := by decide

/-- The hypotheses of `ofNames_layout_edges` can be met. -/
example : ∀ p ∈ ([(0, 1), (1, 2)] : List (Nat × Nat)),
    p.1 < (#["a", "b", "c"] : Array String).size ∧ p.2 < (#["a", "b", "c"] : Array String).size := by
  decide

end Graph

end PILean
