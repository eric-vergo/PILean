/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.Young.SemistandardTableau
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Cover
import PILean.Diagram.Hasse
import PILean.Diagram.Path
import PILean.Diagram.Perm
import PILean.Diagram.SetSystem
import PILean.Diagram.Young

/-!
# Diagrams of Mathlib's combinatorial objects

For each kind of `PILean.Diagram` whose object Mathlib has, a function from Mathlib's object to the
kind's data and a theorem that what the diagram draws is that object, stated with Mathlib's own
definitions:

* `FinGraph.ofSimpleGraph`: a drawn pair `(a, b)` is exactly `a < b` with `G.Adj a b`;
  `FinGraph.ofDigraph`: a drawn pair is exactly `G.Adj a b`.
* `FinPoset.ofOrder`, for an enumeration `e : Fin n ≃ α` of a partial order: a drawn edge
  `(a, b)` is exactly a cover `e a ⋖ e b` (`CovBy`), and the data is a partial order.
* `YoungShape.ofYoungDiagram`: cell `(i, j)` is drawn exactly when it is a cell of `μ`
  (`YoungDiagram.cells`); `YoungShape.ofPartition`: the row lengths are the parts.
* `Tableau.ofSSYT`: the shape's cells are the cells of `μ` and the entry written in each is
  `T i j`.
* `FinPerm.ofPerm`: the value at `i` is `σ i`, the cycle diagram's arrows are exactly `a → σ a`,
  the inversions (the wiring diagram's crossings) exactly the pairs `a < b` with `σ b < σ a`.
* `LatticePath.ofDyckWord`: step `k` rises exactly when letter `k` is `U`, and the word is a Dyck
  word in the sense of `LatticePath.isDyck`.
* `SetSystem.ofFinsets`: element `x` is in set `s` exactly when `x ∈ S_s`, so in a Venn diagram it
  is written inside circle `s` exactly when `x ∈ S_s`.

The theorems are about the exact data and marks; how they are drawn (floating point, text, the
rasteriser, colours) is the tested code of the core.
-/

namespace PILean.Diagram

/-! ### Graphs -/

namespace FinGraph

/-- The undirected graph of a simple graph on `Fin n` with decidable adjacency. -/
def ofSimpleGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (names : Array String := #[]) : FinGraph :=
  ⟨n, fun i j => decide (G.Adj i j), false, true, names⟩

/-- The pairs drawn for a simple graph are exactly its edges, each once as `(a, b)` with
`a < b`. -/
theorem ofSimpleGraph_mem_edgePairs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (names : Array String) (a b : Fin n) :
    ((a : ℕ), (b : ℕ)) ∈ (ofSimpleGraph G names).edgePairs ↔ a < b ∧ G.Adj a b := by
  rw [mem_edgePairs]
  simp only [ofSimpleGraph, drawn, Bool.false_eq_true, ↓reduceIte, Fin.eta, Bool.and_eq_true,
    decide_eq_true_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨-, -, hle, hadj⟩
    have h : G.Adj a b := hadj.elim id fun h => G.adj_symm h
    exact ⟨lt_of_le_of_ne hle (G.ne_of_adj h), h⟩
  · rintro ⟨hlt, h⟩
    exact ⟨a.2, b.2, hlt.le, Or.inl h⟩

/-- The directed graph of a digraph on `Fin n` with decidable adjacency. -/
def ofDigraph {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj] (names : Array String := #[]) :
    FinGraph :=
  ⟨n, fun i j => decide (G.Adj i j), true, true, names⟩

/-- The pairs drawn for a digraph are exactly its arcs, loops included. -/
theorem ofDigraph_mem_edgePairs {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj]
    (names : Array String) (a b : Fin n) :
    ((a : ℕ), (b : ℕ)) ∈ (ofDigraph G names).edgePairs ↔ G.Adj a b := by
  rw [mem_edgePairs]
  simp [ofDigraph, drawn]

end FinGraph

/-! ### Orders -/

namespace FinPoset

variable {α : Type*} [PartialOrder α] [DecidableLE α] {n : ℕ}

/-- The finite order of a partial order enumerated by `e`: element `i` is `e i`. -/
def ofOrder (e : Fin n ≃ α) (names : Array String := #[]) : FinPoset :=
  ⟨n, fun i j => decide (e i ≤ e j), names⟩

/-- The strict relation of `ofOrder e` is `<` on the enumerated elements. -/
theorem ofOrder_lt (e : Fin n ≃ α) (names : Array String) (i j : Fin n) :
    (ofOrder e names).lt i j = true ↔ e i < e j := by
  change (decide (e i ≤ e j) && !(i == j)) = true ↔ _
  rw [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
    lt_iff_le_and_ne, e.injective.ne_iff]

/-- The covering relation of `ofOrder e` is Mathlib's `CovBy` on the enumerated elements. -/
theorem ofOrder_covers (e : Fin n ≃ α) (names : Array String) (i j : Fin n) :
    (ofOrder e names).covers i j = true ↔ e i ⋖ e j := by
  unfold covers
  rw [Bool.and_eq_true, ofOrder_lt, Bool.not_eq_true', List.any_eq_false]
  constructor
  · rintro ⟨hlt, hno⟩
    refine ⟨hlt, fun c hic hcj => ?_⟩
    have h := hno (e.symm c) (List.mem_finRange _)
    rw [Bool.and_eq_true] at h
    exact h ⟨(ofOrder_lt e names i (e.symm c)).2 (by simpa using hic),
      (ofOrder_lt e names (e.symm c) j).2 (by simpa using hcj)⟩
  · rintro ⟨hlt, hno⟩
    refine ⟨hlt, fun k _ h => ?_⟩
    rw [Bool.and_eq_true] at h
    exact hno ((ofOrder_lt e names i k).1 h.1) ((ofOrder_lt e names k j).1 h.2)

/-- A pair is drawn in the Hasse diagram of `ofOrder e` exactly when it is a cover. -/
theorem ofOrder_mem_coverPairs (e : Fin n ≃ α) (names : Array String) (a b : Fin n) :
    ((a : ℕ), (b : ℕ)) ∈ (ofOrder e names).coverPairs ↔ e a ⋖ e b := by
  rw [mem_coverPairs]
  exact ⟨fun ⟨_, _, h⟩ => (ofOrder_covers e names a b).1 h,
    fun h => ⟨a.2, b.2, (ofOrder_covers e names a b).2 h⟩⟩

/-- `ofOrder e` is a partial order. -/
theorem ofOrder_isPartialOrder (e : Fin n ≃ α) (names : Array String) :
    (ofOrder e names).IsPartialOrder where
  refl i := by
    change decide (e i ≤ e i) = true
    exact decide_eq_true le_rfl
  antisymm i j h h' := by
    change decide (e i ≤ e j) = true at h
    change decide (e j ≤ e i) = true at h'
    rw [decide_eq_true_eq] at h h'
    exact e.injective (le_antisymm h h')
  trans i j k h h' := by
    change decide (e i ≤ e j) = true at h
    change decide (e j ≤ e k) = true at h'
    change decide (e i ≤ e k) = true
    rw [decide_eq_true_eq] at h h' ⊢
    exact h.trans h'

end FinPoset

/-! ### Young diagrams and tableaux -/

/-- Cell `(i, j)` of the row lengths of a Young diagram is exactly a cell of the diagram. -/
theorem mem_cellList_rowLens (μ : YoungDiagram) (i j : ℕ) :
    (i, j) ∈ cellList μ.rowLens ↔ (i, j) ∈ μ := by
  rw [mem_cellList]
  constructor
  · rintro ⟨hi, hj⟩
    rw [YoungDiagram.get_rowLens] at hj
    exact YoungDiagram.mem_iff_lt_rowLen.2 hj
  · intro h
    have hi : i < μ.rowLens.length := by
      rw [YoungDiagram.length_rowLens]
      exact YoungDiagram.mem_iff_lt_colLen.1 (μ.up_left_mem le_rfl (Nat.zero_le j) h)
    exact ⟨hi, by rw [YoungDiagram.get_rowLens]; exact YoungDiagram.mem_iff_lt_rowLen.1 h⟩

namespace YoungShape

/-- The shape of a Young diagram: its row lengths. -/
def ofYoungDiagram (μ : YoungDiagram) (c : Convention := .english) : YoungShape :=
  ⟨μ.rowLens, c⟩

/-- The cells drawn for a Young diagram are exactly its cells (`YoungDiagram.cells`). -/
theorem ofYoungDiagram_cells (μ : YoungDiagram) (c : Convention) (i j : ℕ) :
    (i, j) ∈ (ofYoungDiagram μ c).draw.cells ↔ (i, j) ∈ μ.cells := by
  rw [((ofYoungDiagram μ c).draw_faithful).1]
  exact mem_cellList_rowLens μ i j

/-- The shape of a partition: its parts in decreasing order. -/
def ofPartition {m : ℕ} (p : Nat.Partition m) (c : Convention := .english) : YoungShape :=
  ⟨p.parts.sort (· ≥ ·), c⟩

/-- The row lengths of a partition's shape are its parts. -/
theorem ofPartition_rows {m : ℕ} (p : Nat.Partition m) (c : Convention) :
    ((ofPartition p c).rows : Multiset ℕ) = p.parts :=
  Multiset.sort_eq _ _

end YoungShape

namespace Tableau

/-- The tableau of a semistandard Young tableau: row `i` holds `T i j` for the cells `(i, j)` of
the row. -/
def ofSSYT {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (c : Convention := .english) :
    Tableau :=
  ⟨(List.range μ.rowLens.length).map fun i => (List.range (μ.rowLens.getD i 0)).map fun j => T i j,
    c⟩

/-- The shape of the tableau of `T` is the row lengths of `μ`. -/
theorem ofSSYT_shape {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (c : Convention) :
    (ofSSYT T c).shape = μ.rowLens := by
  apply List.ext_getElem
  · simp [ofSSYT, shape]
  · intro i h₁ h₂
    have hi : i < μ.rowLens.length := by simpa [ofSSYT, shape] using h₁
    simp [ofSSYT, shape, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- The cells drawn for `T` are exactly the cells of `μ`. -/
theorem ofSSYT_cells {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (c : Convention)
    (i j : ℕ) : (i, j) ∈ (ofSSYT T c).draw.cells ↔ (i, j) ∈ μ := by
  rw [((ofSSYT T c).draw_faithful).1, ofSSYT_shape]
  exact mem_cellList_rowLens μ i j

/-- The entry of the tableau of `T` at a cell of `μ` is `T i j`. -/
theorem ofSSYT_entry {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (c : Convention)
    {i j : ℕ} (h : (i, j) ∈ μ) : (ofSSYT T c).entry i j = T i j := by
  obtain ⟨hi, hj⟩ := (mem_cellList_rowLens μ i j).2 h |> (mem_cellList _ _ _).1
  have hi' : i < μ.colLen 0 := by rwa [← YoungDiagram.length_rowLens]
  rw [YoungDiagram.get_rowLens] at hj
  simp [entry, ofSSYT, List.getD_eq_getElem?_getD, List.getElem?_range hi',
    List.getElem?_eq_getElem hi, List.getElem?_range hj]

/-- The entries written in the diagram of `T` are `T i j` at the cells `(i, j)` of `μ`. -/
theorem ofSSYT_entries {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (c : Convention)
    (i j : ℕ) (s : String) :
    ((i, j), s) ∈ (ofSSYT T c).draw.entries ↔ (i, j) ∈ μ ∧ s = toString (T i j) := by
  rw [((ofSSYT T c).draw_faithful).2.1, entryTexts, List.mem_map]
  constructor
  · rintro ⟨⟨i', j'⟩, hc, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
    rw [ofSSYT_shape, mem_cellList_rowLens] at hc
    exact ⟨hc, by simp [ofSSYT_entry T c hc]⟩
  · rintro ⟨h, rfl⟩
    exact ⟨(i, j), by rw [ofSSYT_shape, mem_cellList_rowLens]; exact h,
      by simp [ofSSYT_entry T c h]⟩

end Tableau

/-! ### Permutations -/

namespace FinPerm

variable {n : ℕ}

/-- A permutation of `Fin n` in one-line notation, written from 1. -/
def ofPerm (σ : Equiv.Perm (Fin n)) : FinPerm := ⟨(List.finRange n).map fun i => (σ i : ℕ), 1⟩

/-- The size of `ofPerm σ` is `n`. -/
theorem ofPerm_n (σ : Equiv.Perm (Fin n)) : (ofPerm σ).n = n := by simp [ofPerm, FinPerm.n]

/-- The value of `ofPerm σ` at `i` is `σ i`. -/
theorem ofPerm_apply (σ : Equiv.Perm (Fin n)) (i : Fin n) : (ofPerm σ).apply i = σ i := by
  simp [ofPerm, apply, List.getD_eq_getElem?_getD]

/-- The cycle diagram of `σ` draws an arrow `a → b` exactly when `σ a = b`. -/
theorem ofPerm_cycles_edges (σ : Equiv.Perm (Fin n)) (a b : Fin n) :
    ((a : ℕ), (b : ℕ)) ∈ (ofPerm σ).cycles.edges ↔ σ a = b := by
  rw [mem_cycles_edges, ofPerm_n, ofPerm_apply, Fin.val_inj]
  exact ⟨fun h => h.2.2, fun h => ⟨a.2, b.2, h⟩⟩

/-- The inversions of `ofPerm σ`, which are the crossings of its wiring diagram, are exactly the
pairs `a < b` with `σ b < σ a`. -/
theorem ofPerm_mem_inversions (σ : Equiv.Perm (Fin n)) (a b : Fin n) :
    ((a : ℕ), (b : ℕ)) ∈ (ofPerm σ).inversions ↔ a < b ∧ σ b < σ a := by
  rw [mem_inversions, ofPerm_n, ofPerm_apply, ofPerm_apply]
  simp only [Fin.lt_def]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, b.2, h.2⟩⟩

/-- The crossings of the wiring diagram of `ofPerm σ` are exactly the inversions of `σ`. -/
theorem ofPerm_crossings (σ : Equiv.Perm (Fin n)) (a b : Fin n) :
    ((a : ℕ), (b : ℕ)) ∈ crossingPairs (ofPerm σ).wiring.strands ↔ a < b ∧ σ b < σ a := by
  rw [wiring_crossings, ofPerm_mem_inversions]

end FinPerm

/-! ### Dyck paths -/

namespace LatticePath

/-- The word of up (`true`) and down steps of a list of Dyck steps. -/
def dyckBits (l : List DyckStep) : List Bool := l.map (· = DyckStep.U)

/-- The ups of the word are the `U`s of the list. -/
theorem count_true_dyckBits (l : List DyckStep) : (dyckBits l).count true = l.count .U := by
  induction l with
  | nil => rfl
  | cons s l ih => cases s <;> simp_all [dyckBits]

/-- The downs of the word are the `D`s of the list. -/
theorem count_false_dyckBits (l : List DyckStep) : (dyckBits l).count false = l.count .D := by
  induction l with
  | nil => rfl
  | cons s l ih => cases s <;> simp_all [dyckBits]

/-- The path of a Dyck word: `U` an up step `(1, 1)`, `D` a down step `(1, -1)`. -/
def ofDyckWord (w : DyckWord) : LatticePath := ofDyck (dyckBits w.toList)

/-- The word of a Dyck word is a Dyck word in the sense of `isDyck`. -/
theorem isDyck_dyckBits (w : DyckWord) : isDyck (dyckBits w.toList) = true := by
  simp only [isDyck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨fun k _ => ?_, ?_⟩
  · have e : (dyckBits w.toList).take k = dyckBits (w.toList.take k) := by
      simp [dyckBits, List.map_take]
    rw [e, count_true_dyckBits, count_false_dyckBits]
    exact w.count_D_le_count_U k
  · rw [count_true_dyckBits, count_false_dyckBits, w.count_U_eq_count_D]

/-- Step `k` of the path of a Dyck word rises exactly when letter `k` is `U`. -/
theorem ofDyckWord_step_rises (w : DyckWord) (k : ℕ) (h : k < w.toList.length) :
    ((ofDyckWord w).point (k + 1)).2 = ((ofDyckWord w).point k).2 + 1 ↔ w.toList[k] = .U := by
  rw [ofDyckWord, ofDyck_step_rises _ _ (by simpa [dyckBits] using h)]
  simp [dyckBits]

end LatticePath

/-! ### Set systems -/

namespace SetSystem

variable {n : ℕ}

/-- The set system of finsets of `Fin n`: set `s` is the list of the elements of `S s`. -/
def ofFinsets (sets : List (Finset (Fin n))) (names : Array String := #[])
    (setNames : Array String := #[]) : SetSystem :=
  ⟨n, sets.map fun s => ((List.finRange n).filter (· ∈ s)).map Fin.val, names, setNames⟩

/-- Element `x` is in set `k` of `ofFinsets sets` exactly when `x ∈ sets[k]`. -/
theorem ofFinsets_mem (sets : List (Finset (Fin n))) (names setNames : Array String) (x : Fin n)
    (k : ℕ) (hk : k < sets.length) :
    (ofFinsets sets names setNames).mem x k = true ↔ x ∈ sets[k] := by
  simp only [mem, ofFinsets, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some, List.contains_iff_mem,
    List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  exact ⟨fun ⟨y, hy, he⟩ => Fin.val_inj.1 he ▸ hy, fun h => ⟨x, h, rfl⟩⟩

/-- In the Venn diagram of one to three finsets whose regions fit, element `x` is written inside
circle `k` exactly when `x ∈ sets[k]`. -/
theorem ofFinsets_venn_inside (sets : List (Finset (Fin n))) (names setNames : Array String)
    (hk : 1 ≤ sets.length ∧ sets.length ≤ 3) (hfit : (ofFinsets sets names setNames).fits = true)
    {x : Fin n} {m : ℕ} {p : QPoint}
    (hx : ((x : ℕ), m, p) ∈ (ofFinsets sets names setNames).venn.members)
    {k : ℕ} (hk' : k < sets.length) :
    inside ((vennCentres sets.length).getD k (0, 0)) p = true ↔ x ∈ sets[k] := by
  have := (ofFinsets sets names setNames).venn_inside (by simpa [ofFinsets] using hk) hfit hx
    (s := k) (by simpa [ofFinsets] using hk')
  simp only [ofFinsets, List.length_map] at this
  rw [this, ← ofFinsets_mem sets names setNames x k hk']
  rfl

end SetSystem

end PILean.Diagram
