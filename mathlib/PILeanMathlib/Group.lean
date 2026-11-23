/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Cover
import PILean.Diagram.Group
import PILean.Diagram.Hasse

/-!
# Diagrams of finite groups bound to Mathlib

* `FinMagma.ofMul e`: the table of the multiplication of `G` through an enumeration
  `e : Fin n ≃ G`. Its cell `(a, b)` holds `e.symm (e a * e b)` (`ofMul_mul`); it is a group by
  `FinMagma.isGroup` for a `Group` (`ofMul_isGroup`); it is commutative, which on the drawing is
  the symmetry of the table about its diagonal, exactly when `G`'s multiplication is
  (`ofMul_isCommutative_iff`); its centre (`FinMagma.centre`, the elements whose row equals their
  column) is `Subgroup.center G` (`mem_centre_ofMul`).
* The arrows of the Cayley graph of `ofMul e` are `g → g * s` for `G`'s multiplication
  (`ofMul_cayleyArrows`).
* `FinPoset.mem_coverPairs_of_equiv`: when a finite order's relation is `≤` of a partial order
  through an enumeration, its Hasse diagram's edges are exactly the covers `⋖`; this is how a
  lattice of subgroups (`Subgroup G`) is drawn.
-/

namespace PILean.Diagram

namespace FinMagma

variable {G : Type*} {n : ℕ}

/-- The table of the multiplication of `G` enumerated by `e`: element `a` is `e a`. -/
abbrev ofMul [Mul G] (e : Fin n ≃ G) (names : Array String := #[]) : FinMagma :=
  ⟨n, fun a b => e.symm (e a * e b), names⟩

/-- Cell `(a, b)` of the table of `ofMul e` holds the element `e a * e b`. -/
theorem ofMul_mul [Mul G] (e : Fin n ≃ G) (names : Array String) (a b : Fin n) :
    e ((ofMul e names).mul a b) = e a * e b := by
  simp

/-- The table of a group is a group in the sense of `FinMagma.isGroup`. -/
theorem ofMul_isGroup [Group G] (e : Fin n ≃ G) (names : Array String) :
    (ofMul e names).isGroup = true := by
  have hid : ∀ x : Fin n, (ofMul e names).isIdentity x = true ↔ e x = 1 := by
    intro x
    simp only [isIdentity, ofMul, List.all_eq_true, List.mem_finRange, true_implies,
      Bool.and_eq_true, beq_iff_eq]
    constructor
    · intro h
      have := (h (e.symm 1)).2
      rw [Equiv.symm_apply_eq] at this
      simpa using this
    · intro h a
      simp [h]
  unfold isGroup
  simp only [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · simp [isAssoc, ofMul, mul_assoc]
  · cases hfind : (ofMul e names).identity? with
    | none =>
      exfalso
      rw [identity?, List.find?_eq_none] at hfind
      exact absurd ((hid (e.symm 1)).2 (by simp)) (by simpa using hfind (e.symm 1))
    | some x =>
      have hx : e x = 1 := (hid x).1 (List.find?_some hfind)
      simp only [List.all_eq_true, List.mem_finRange, true_implies, List.any_eq_true,
        Bool.and_eq_true, beq_iff_eq]
      intro a
      refine ⟨e.symm (e a)⁻¹, ?_, ?_, ?_⟩ <;> simp [Equiv.symm_apply_eq, hx]

/-- The table of `ofMul e` is symmetric about its diagonal exactly when `G`'s multiplication is
commutative. -/
theorem ofMul_isCommutative_iff [Mul G] (e : Fin n ≃ G) (names : Array String) :
    (ofMul e names).isCommutative = true ↔ ∀ x y : G, x * y = y * x := by
  simp only [isCommutative, ofMul, List.all_eq_true, List.mem_finRange, true_implies,
    beq_iff_eq, EmbeddingLike.apply_eq_iff_eq]
  refine ⟨fun h x y => ?_, fun h a b => h _ _⟩
  simpa using h (e.symm x) (e.symm y)

/-- The elements of the centre of the table are those of `Subgroup.center G`. -/
theorem mem_centre_ofMul [Group G] (e : Fin n ≃ G) (names : Array String) (a : Fin n) :
    a.val ∈ (ofMul e names).centre ↔ e a ∈ Subgroup.center G := by
  simp only [centre, ofMul, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    List.all_eq_true, true_implies, beq_iff_eq, EmbeddingLike.apply_eq_iff_eq,
    Subgroup.mem_center_iff]
  constructor
  · rintro ⟨b, hb, hab⟩
    obtain rfl : b = a := Fin.ext hab
    intro g
    simpa using (hb (e.symm g)).symm
  · intro h
    exact ⟨a, fun b => (h (e b)).symm, rfl⟩

/-- The entry written in cell `(a, b)` of a faithful table of `ofMul e` is the name of the
element `e a * e b`. -/
theorem ofMul_entries [Mul G] (e : Fin n ≃ G) (names : Array String) {d : Diagram}
    (h : (ofMul e names).FaithfulTable d) (a b : Fin n) (s : String) :
    (((a : ℕ), (b : ℕ)), s) ∈ d.entries ↔ s = (ofMul e names).name (e.symm (e a * e b)) := by
  rw [entries_table h]
  exact ⟨fun ⟨_, _, hs⟩ => hs, fun hs => ⟨a.2, b.2, hs⟩⟩

/-- The arrows of the Cayley graph of `ofMul e` for the generators `gens` join `g` to the
element `e g * e s` for a generator `s`, in that generator's colour. -/
theorem ofMul_cayleyArrows [Mul G] (e : Fin n ≃ G) (names : Array String)
    (gens : List (Fin n)) (a : CDArrow) (ha : a ∈ (ofMul e names).cayleyArrows gens) :
    ∃ c s g, gens[c]? = some s ∧ a.ink = .series c false ∧ a.src = g.val ∧
      a.tgt = (e.symm (e g * e s)).val := by
  obtain ⟨c, s, g, hs, hi, hsrc, htgt, -⟩ := ((ofMul e names).mem_cayleyArrows gens a).1 ha
  exact ⟨c, s, g, hs, hi, hsrc, htgt⟩

end FinMagma

namespace FinPoset

/-- When the relation of `P` is `≤` of a partial order through the enumeration `e`, the edges of
its Hasse diagram are exactly the covers `e a ⋖ e b`. -/
theorem mem_coverPairs_of_equiv {α : Type*} [PartialOrder α] (P : FinPoset) (e : Fin P.n ≃ α)
    (hle : ∀ i j, P.le i j = true ↔ e i ≤ e j) (a b : Fin P.n) :
    ((a : ℕ), (b : ℕ)) ∈ P.coverPairs ↔ e a ⋖ e b := by
  have hlt : ∀ i j, P.lt i j = true ↔ e i < e j := by
    intro i j
    simp only [lt, Bool.and_eq_true, hle, lt_iff_le_and_ne, e.injective.ne_iff]
    simp [bne_iff_ne]
  have hcov : ∀ i j, P.covers i j = true ↔ e i ⋖ e j := by
    intro i j
    unfold covers
    rw [Bool.and_eq_true, hlt, Bool.not_eq_true', List.any_eq_false]
    constructor
    · rintro ⟨hij, hno⟩
      refine ⟨hij, fun c hic hcj => ?_⟩
      have h := hno (e.symm c) (List.mem_finRange _)
      rw [Bool.and_eq_true] at h
      exact h ⟨(hlt i (e.symm c)).2 (by simpa using hic), (hlt (e.symm c) j).2 (by simpa using hcj)⟩
    · rintro ⟨hij, hno⟩
      refine ⟨hij, fun k _ h => ?_⟩
      rw [Bool.and_eq_true] at h
      exact hno ((hlt i k).1 h.1) ((hlt k j).1 h.2)
  rw [mem_coverPairs]
  exact ⟨fun ⟨_, _, h⟩ => (hcov a b).1 h, fun h => ⟨a.2, b.2, (hcov a b).2 h⟩⟩

end FinPoset

end PILean.Diagram
