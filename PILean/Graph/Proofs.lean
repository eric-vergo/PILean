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

/-- The entry `j` after modifying entry `i`. -/
theorem getD_modify (a : Array Nat) (i j : Nat) (f : Nat → Nat) :
    (a.modify i f).getD j 0 = if i = j ∧ i < a.size then f (a.getD i 0) else a.getD j 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases h : i = j
  · subst h
    by_cases h2 : i < a.size
    · simp [h2]
    · simp [h2]
  · simp [h]

/-- Relaxing does not change the number of nodes. -/
theorem size_relax (l : Array Nat) (e : Nat × Nat) : (relax l e).size = l.size := by
  simp [relax]

/-- Relaxing edges does not change the number of nodes. -/
theorem fixLayers_size (es : List (Nat × Nat)) (l : Array Nat) :
    (fixLayers es l).size = l.size := by
  induction es generalizing l with
  | nil => rfl
  | cons e es ih => simp only [fixLayers, List.foldl_cons] at ih ⊢; rw [ih, size_relax]

/-- Relaxing edges only raises layers. -/
theorem fixLayers_ge (es : List (Nat × Nat)) (l : Array Nat) (i : Nat) :
    l.getD i 0 ≤ (fixLayers es l).getD i 0 := by
  induction es generalizing l with
  | nil => exact Nat.le_refl _
  | cons e es ih =>
    simp only [fixLayers, List.foldl_cons] at ih ⊢
    refine Nat.le_trans ?_ (ih _)
    simp only [relax, getD_modify]
    split
    · rename_i h
      obtain ⟨rfl, _⟩ := h
      exact Nat.le_max_left _ _
    · exact Nat.le_refl _

/-- A node that no edge of the list ends at keeps its layer. -/
theorem fixLayers_same (es : List (Nat × Nat)) (l : Array Nat) (i : Nat)
    (h : ∀ e ∈ es, e.2 ≠ i) : (fixLayers es l).getD i 0 = l.getD i 0 := by
  induction es generalizing l with
  | nil => rfl
  | cons e es ih =>
    simp only [fixLayers, List.foldl_cons] at ih ⊢
    rw [ih _ (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]
    simp only [relax, getD_modify]
    have : e.2 ≠ i := h e (List.mem_cons_self ..)
    simp [this]

/-- Relaxing edges that are in order (no later edge ends where an earlier one starts), between
distinct nodes in range, leaves every edge's target on a deeper layer than its source. -/
theorem fixLayers_lt (es : List (Nat × Nat)) (layer : Array Nat)
    (hb : ∀ e ∈ es, e.1 < layer.size ∧ e.2 < layer.size) (hne : ∀ e ∈ es, e.1 ≠ e.2)
    (hord : es.Pairwise fun e e' => e'.2 ≠ e.1) :
    ∀ e ∈ es, (fixLayers es layer).getD e.1 0 < (fixLayers es layer).getD e.2 0 := by
  induction es generalizing layer with
  | nil => intro e he; cases he
  | cons e es ih =>
    intro x hx
    rw [List.pairwise_cons] at hord
    have hrel : (relax layer e).size = layer.size := size_relax layer e
    have key : ∀ x ∈ es, (fixLayers es (relax layer e)).getD x.1 0 <
        (fixLayers es (relax layer e)).getD x.2 0 :=
      ih (relax layer e) (fun y hy => by rw [hrel]; exact hb y (List.mem_cons_of_mem _ hy))
        (fun y hy => hne y (List.mem_cons_of_mem _ hy)) hord.2
    have hf : fixLayers (e :: es) layer = fixLayers es (relax layer e) := rfl
    rw [hf]
    rcases List.mem_cons.1 hx with rfl | hx
    · have h1 := fixLayers_same es (relax layer x) x.1 (fun e' he' => hord.1 e' he')
      have h2 := fixLayers_ge es (relax layer x) x.2
      have hbx := hb x (List.mem_cons_self ..)
      have hnx := hne x (List.mem_cons_self ..)
      have h3 : (relax layer x).getD x.2 0 = max (layer.getD x.2 0) (layer.getD x.1 0 + 1) := by
        simp only [relax, getD_modify, hbx.2, and_self, ↓reduceIte]
      have h4 : (relax layer x).getD x.1 0 = layer.getD x.1 0 := by
        simp only [relax, getD_modify, Ne.symm hnx, false_and, ↓reduceIte]
      rw [h1, h4]
      have : layer.getD x.1 0 + 1 ≤ (relax layer x).getD x.2 0 := by
        rw [h3]; exact Nat.le_max_right _ _
      omega
    · exact key x hx

/-- The order that `acyclicEdges` sorts by: the source of the first does not come after the
source of the second. -/
def srcLe (pos : Array Nat) (a b : Nat × Nat) : Bool := !before pos b.1 a.1

/-- `before` in terms of positions. -/
theorem before_iff (pos : Array Nat) (a b : Nat) :
    before pos a b = true ↔
      pos.getD a 0 < pos.getD b 0 ∨ (pos.getD a 0 = pos.getD b 0 ∧ a < b) := by
  simp [before]

/-- Orienting an edge between distinct nodes makes it point from the node that comes first. -/
theorem orient_before (pos : Array Nat) (p : Nat × Nat) (h : p.1 ≠ p.2) :
    before pos (orient pos p).1 (orient pos p).2 = true := by
  unfold orient
  by_cases hb : before pos p.1 p.2 = true
  · simp [hb]
  · have hb' : before pos p.1 p.2 = false := by simpa using hb
    simp only [hb', Bool.false_eq_true, ↓reduceIte]
    rw [Bool.eq_false_iff, Ne, before_iff] at hb'
    rw [before_iff]
    omega

/-- The acyclic edges are in range, are not loops, and are in order for `fixLayers`. -/
theorem acyclicEdges_ok (pos : Array Nat) (n : Nat) (edges : List (Nat × Nat))
    (hb : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) :
    (∀ e ∈ acyclicEdges pos edges, e.1 < n ∧ e.2 < n) ∧
    (∀ e ∈ acyclicEdges pos edges, e.1 ≠ e.2) ∧
    (acyclicEdges pos edges).Pairwise fun e e' => e'.2 ≠ e.1 := by
  have mem : ∀ e, e ∈ acyclicEdges pos edges ↔
      ∃ p ∈ edges, p.1 ≠ p.2 ∧ orient pos p = e := by
    intro e
    simp only [acyclicEdges, List.mem_mergeSort, List.mem_map, List.mem_filter, bne_iff_ne,
      ne_eq]
    constructor
    · rintro ⟨p, ⟨hp, hne⟩, rfl⟩; exact ⟨p, hp, hne, rfl⟩
    · rintro ⟨p, hp, hne, rfl⟩; exact ⟨p, ⟨hp, hne⟩, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨p, hp, hne, rfl⟩ := (mem e).1 he
    have := hb p hp
    unfold orient; split <;> simp_all
  · intro e he
    obtain ⟨p, hp, hne, rfl⟩ := (mem e).1 he
    unfold orient; split <;> simp_all [Ne.symm]
  · have sorted : (acyclicEdges pos edges).Pairwise fun a b => srcLe pos a b = true := by
      unfold acyclicEdges
      refine List.pairwise_mergeSort (le := srcLe pos) ?_ ?_ _
      · intro a b c h1 h2
        simp only [srcLe, Bool.not_eq_true'] at *
        rw [Bool.eq_false_iff, Ne, before_iff] at *
        omega
      · intro a b
        simp only [srcLe, Bool.or_eq_true, Bool.not_eq_true'] 
        by_cases h : before pos b.1 a.1 = true
        · by_cases h' : before pos a.1 b.1 = true
          · rw [before_iff] at h h'; omega
          · right; simpa using h'
        · left; simpa using h
    refine sorted.imp_of_mem ?_
    intro a b ha hb hle h2
    obtain ⟨p, hp, hne, rfl⟩ := (mem a).1 ha
    obtain ⟨q, hq, hne', rfl⟩ := (mem b).1 hb
    have hq' := orient_before pos q hne'
    simp only [srcLe, Bool.not_eq_true'] at hle
    rw [h2] at hq'
    rw [hq'] at hle
    exact absurd hle (by simp)

/-- The layers after the guard of `assignLayers` have the size of the graph. -/
theorem assignLayers_start_size (n : Nat) (es : List (Nat × Nat)) :
    (let l0 := fixLayers es (Array.replicate n 0)
     let l1 := promote n es l0
     (if l1.size = n then l1 else l0)).size = n := by
  dsimp only
  by_cases h : (promote n es (fixLayers es (Array.replicate n 0))).size = n
  · simp [h]
  · simp [h, fixLayers_size]

/-- After `assignLayers`, every acyclic edge points to a deeper layer. -/
theorem assignLayers_lt (pos : Array Nat) (n : Nat) (edges : List (Nat × Nat))
    (hb : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) :
    ∀ e ∈ acyclicEdges pos edges,
      (assignLayers pos n edges).getD e.1 0 < (assignLayers pos n edges).getD e.2 0 := by
  obtain ⟨h1, h2, h3⟩ := acyclicEdges_ok pos n edges hb
  unfold assignLayers
  simp only
  refine fixLayers_lt _ _ ?_ h2 h3
  intro e he
  rw [assignLayers_start_size n (acyclicEdges pos edges)]
  exact h1 e he

/-- For every input edge between distinct nodes, the layer of the node that comes first is
smaller than the layer of the other. -/
theorem assignLayers_lt_input (pos : Array Nat) (n : Nat) (edges : List (Nat × Nat))
    (hb : ∀ e ∈ edges, e.1 < n ∧ e.2 < n) :
    ∀ e ∈ edges, e.1 ≠ e.2 →
      (if before pos e.1 e.2 then
        (assignLayers pos n edges).getD e.1 0 < (assignLayers pos n edges).getD e.2 0
      else (assignLayers pos n edges).getD e.2 0 < (assignLayers pos n edges).getD e.1 0) := by
  intro e he hne
  have key := assignLayers_lt pos n edges hb (orient pos e) (by
    simp only [acyclicEdges, List.mem_mergeSort, List.mem_map, List.mem_filter, bne_iff_ne,
      ne_eq]
    exact ⟨e, ⟨he, hne⟩, rfl⟩)
  unfold orient at key
  split at key
  · rename_i h; simp only [h]; exact key
  · rename_i h; simp only [h]; exact key

/-- The index of a route is the index it was made for. -/
theorem routeOne_index (pl : Plan) (k i : Nat) (e : Graph.Edge) :
    (routeOne pl k i e).index = i := by
  simp only [routeOne]
  split <;> rfl

/-- The routes carry the indices of the edges they were made for. -/
theorem routeAll_index (pl : Plan) (ve : Array (Nat × Graph.Edge)) :
    (routeAll pl ve).map (·.index) = ve.map (·.1) := by
  apply Array.ext
  · simp [routeAll]
  · intro i h1 h2
    simp [routeAll, routeOne_index]

/-- Fitting a layout to its margins keeps its edges' indices. -/
theorem fit_indices (l : Layout) (margin : Float) :
    (l.fit margin).edges.map (·.index) = l.edges.map (·.index) := by
  unfold Layout.fit
  split <;> simp [Layout.translate, Array.map_map, Function.comp_def]

/-- The routes of the layered layout are the valid edges, in order, by index. -/
theorem layout_edge_indices (g : Graph) (o : LayeredOptions) (st : Style) :
    (g.layout o st).edges.map (·.index) = g.validEdges.map (·.1) := by
  unfold layout
  rw [fit_indices]
  exact routeAll_index _ _

/-- The positions of all edges in order. -/
theorem indexedEdges_map (g : Graph) :
    g.indexedEdges.toList.map (·.1) = List.range g.edges.size := by
  apply List.ext_getElem
  · simp [Graph.indexedEdges]
  · intro i h1 h2
    simp [Graph.indexedEdges]

/-- No edge is drawn twice. -/
theorem layout_edges_nodup (g : Graph) (o : LayeredOptions) (st : Style) :
    ((g.layout o st).edges.toList.map (·.index)).Nodup := by
  have h := congrArg Array.toList (layout_edge_indices g o st)
  simp only [Array.toList_map] at h
  rw [h]
  have hs : (g.validEdges.toList.map (·.1)).Sublist (g.indexedEdges.toList.map (·.1)) := by
    unfold Graph.validEdges
    rw [Array.toList_filter]
    exact (List.filter_sublist).map _
  rw [indexedEdges_map] at hs
  exact (List.nodup_range).sublist hs

/-- Every edge whose ends are nodes of the graph is drawn exactly once. -/
theorem layout_edges_complete (g : Graph) (o : LayeredOptions) (st : Style) (i : Nat)
    (e : Graph.Edge) (hi : g.edges[i]? = some e)
    (hv : e.src < g.nodes.size ∧ e.dst < g.nodes.size) :
    ((g.layout o st).edges.toList.map (·.index)).count i = 1 := by
  have hnd := layout_edges_nodup g o st
  have h := congrArg Array.toList (layout_edge_indices g o st)
  simp only [Array.toList_map] at h
  generalize (g.layout o st).edges.toList.map (·.index) = L at hnd h ⊢
  subst h
  obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.1 hi
  have hmem : (i, e) ∈ g.validEdges := by
    unfold Graph.validEdges
    rw [Array.mem_filter]
    refine ⟨?_, by simp [hv]⟩
    rw [Array.mem_iff_getElem]
    exact ⟨i, by simpa [Graph.indexedEdges] using hlt, by simp [Graph.indexedEdges, hget]⟩
  exact hnd.count_of_mem (List.mem_map.2 ⟨(i, e), Array.mem_toList_iff.2 hmem, rfl⟩)

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
