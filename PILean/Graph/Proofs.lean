/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Graph.Layered

/-!
# Properties of the layered layout

* `fixLayers_lt`: relaxing edges in an order in which no later edge ends where an earlier one
  starts puts every target on a deeper layer than its source, from any starting layers.
* `assignLayers_lt`: for the function the layout calls, every edge of `acyclicEdges` (every
  non-loop edge turned to point from the node that comes first) has `layer src < layer dst`.
  `assignLayers_lt_input` states it for the input edges.
* `layout_edge_indices`, `layout_edges_nodup`, `layout_edges_complete`: the edges of the
  layered layout are exactly the valid input edges, each once, by index.
-/

namespace PILean.Graph

/-- Relaxing edges that are in order (no later edge ends where an earlier one starts), between
distinct nodes in range, leaves every edge's target on a deeper layer than its source. -/
theorem fixLayers_lt (es : List (Nat × Nat)) (layer : Array Nat)
    (hb : ∀ e ∈ es, e.1 < layer.size ∧ e.2 < layer.size) (hne : ∀ e ∈ es, e.1 ≠ e.2)
    (hord : es.Pairwise fun e e' => e'.2 ≠ e.1) :
    ∀ e ∈ es, (fixLayers es layer).getD e.1 0 < (fixLayers es layer).getD e.2 0 := by
  sorry

/-- The acyclic edges are in range, are not loops, and are in order for `fixLayers`. -/
theorem acyclicEdges_ok (pos : Array Nat) (n : Nat) (edges : List (Nat × Nat))
    (hb : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) :
    (∀ e ∈ acyclicEdges pos edges, e.1 < n ∧ e.2 < n) ∧
    (∀ e ∈ acyclicEdges pos edges, e.1 ≠ e.2) ∧
    (acyclicEdges pos edges).Pairwise fun e e' => e'.2 ≠ e.1 := by
  sorry

/-- After `assignLayers`, every acyclic edge points to a deeper layer. -/
theorem assignLayers_lt (pos : Array Nat) (n : Nat) (edges : List (Nat × Nat))
    (hb : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) :
    ∀ e ∈ acyclicEdges pos edges,
      (assignLayers pos n edges).getD e.1 0 < (assignLayers pos n edges).getD e.2 0 := by
  sorry

/-- For every input edge between distinct nodes, the layer of the node that comes first is
smaller than the layer of the other. -/
theorem assignLayers_lt_input (pos : Array Nat) (n : Nat) (edges : List (Nat × Nat))
    (hb : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) :
    ∀ e ∈ edges, e.1 ≠ e.2 →
      (if before pos e.1 e.2 then
        (assignLayers pos n edges).getD e.1 0 < (assignLayers pos n edges).getD e.2 0
      else (assignLayers pos n edges).getD e.2 0 < (assignLayers pos n edges).getD e.1 0) := by
  sorry

/-- The routes of the layered layout are the valid edges, in order, by index. -/
theorem layout_edge_indices (g : Graph) (o : LayeredOptions) (st : Style) :
    (g.layout o st).edges.map (·.index) = g.validEdges.map (·.1) := by
  sorry

/-- No edge is drawn twice. -/
theorem layout_edges_nodup (g : Graph) (o : LayeredOptions) (st : Style) :
    ((g.layout o st).edges.toList.map (·.index)).Nodup := by
  sorry

/-- Every edge whose ends are nodes of the graph is drawn exactly once. -/
theorem layout_edges_complete (g : Graph) (o : LayeredOptions) (st : Style) (i : Nat)
    (e : Graph.Edge) (hi : g.edges[i]? = some e) (hv : e.src < g.nodes.size ∧ e.dst < g.nodes.size) :
    ((g.layout o st).edges.toList.map (·.index)).count i = 1 := by
  sorry

/-- The hypotheses of `fixLayers_lt` can be met: a chain of three nodes. -/
example : (∀ e ∈ [(0, 1), (1, 2)], e.1 < (#[0, 0, 0] : Array Nat).size ∧
      e.2 < (#[0, 0, 0] : Array Nat).size) ∧ (∀ e ∈ [(0, 1), (1, 2)], e.1 ≠ e.2) ∧
    [(0, 1), (1, 2)].Pairwise (fun e e' : Nat × Nat => e'.2 ≠ e.1) := by
  decide

/-- The hypothesis of `assignLayers_lt` can be met: the edges of a triangle with a back edge are
in range. -/
example : ∀ e ∈ ([(0, 1), (1, 2), (2, 0)] : List (Nat × Nat)), e.1 < 3 ∧ e.2 < 3 := by decide

/-- The statement about edges has a graph to apply to: both edges of a 2-cycle are valid. -/
example : (Graph.ofPairs [(0, 1), (1, 0)]).validIndices = [0, 1] := by decide +kernel

end PILean.Graph
