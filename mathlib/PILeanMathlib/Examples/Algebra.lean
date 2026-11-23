/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import PILeanMathlib.Category
import PILeanMathlib.Group
import PILeanMathlib.Examples.AlgebraFigures

/-!
# Figures of algebra tied to Mathlib's objects: the theorems

Each figure of `PILeanMathlib.Examples.AlgebraFigures` is linked by `figure_proves` to a theorem
that states, with Mathlib's definitions, what it draws.

## Main results

* `d4TableFigure_spec`: cell `(a, b)` of the table holds the name of `d4 a * d4 b` in
  `DihedralGroup 4`; the table is a group; it is not symmetric, since the group is not
  commutative; and the elements whose row equals their column are those of
  `Subgroup.center (DihedralGroup 4)`, which are `1` and `r 2`.
* `d4CayleyFigure_spec`: every drawn arrow joins `g` to `g * r` or `g * s`.
* `d4SubgroupsFigure_spec`: the drawn elements are the subgroups of `DihedralGroup 4`, each once,
  an edge joins `H` to `K` exactly when `H ⋖ K`, and a dot is in colour exactly when its
  subgroup is normal.
* `commSqFigure_spec`: the drawn square is a `CommSq` of the reductions `ZMod 12 → ZMod 6 → ZMod 2`
  and `ZMod 12 → ZMod 4 → ZMod 2` in the category of types.
* `shortExactFigure_spec`: for every short complex `S` of a preadditive category with a zero
  object, the marks of the drawing hold of `S` and `S` is exact exactly when `S.ShortExact`.
-/

open CategoryTheory PILean PILean.Diagram

namespace PILeanMathlib.Examples

/-! ### The dihedral group of order 8 -/

/-- Element number `k` of the dihedral group of order 8: `r k` for `k < 4`, `sr (k - 4)` after. -/
def d4 (k : Fin 8) : DihedralGroup 4 :=
  if k.val < 4 then .r (k.val : ZMod 4) else .sr ((k.val - 4 : ℕ) : ZMod 4)

/-- The number of an element of the dihedral group of order 8. -/
def d4Index : DihedralGroup 4 → Fin 8
  | .r i => ⟨i.val, by have := i.val_lt; omega⟩
  | .sr i => ⟨4 + i.val, by have := i.val_lt; omega⟩

/-- The numbering of the dihedral group of order 8. -/
def d4Equiv : Fin 8 ≃ DihedralGroup 4 where
  toFun := d4
  invFun := d4Index
  left_inv := by decide
  right_inv := by decide

/-- The table of the figure is the multiplication of `DihedralGroup 4`. -/
theorem d4Table_eq : d4Table = FinMagma.ofMul d4Equiv d4Names := by
  have h : ∀ a b : Fin 8, d4Mul a b = d4Equiv.symm (d4Equiv a * d4Equiv b) := by decide
  simp only [d4Table, FinMagma.ofMul, FinMagma.mk.injEq, heq_eq_eq, and_true, true_and]
  funext a b
  exact h a b

/-- **The Cayley table of the dihedral group of order 8.** The figure draws the table of
`d4Table` faithfully; the entry written in cell `(a, b)` is the name of `d4 a * d4 b`; the table
is a group; it is not symmetric about its diagonal, since `DihedralGroup 4` is not commutative;
and the elements whose row and column agree are those of the centre of `DihedralGroup 4`,
which are `1` and `r 2`. -/
theorem d4TableFigure_spec :
    d4Table.FaithfulTable d4TableFigure ∧
    (∀ (a b : Fin 8) (s : String), (((a : ℕ), (b : ℕ)), s) ∈ d4TableFigure.entries ↔
      s = d4Table.name (d4Equiv.symm (d4Equiv a * d4Equiv b))) ∧
    d4Table.isGroup = true ∧ d4Table.isCommutative = false ∧
    ¬ (∀ x y : DihedralGroup 4, x * y = y * x) ∧
    (∀ a : Fin 8, a.val ∈ d4Table.centre ↔ d4Equiv a ∈ Subgroup.center (DihedralGroup 4)) ∧
    d4Table.centre = [0, 2] := by
  have hf : d4Table.FaithfulTable d4TableFigure := by
    have := d4Table.tableFigure_faithful (by decide)
    exact this
  refine ⟨hf, fun a b s => ?_, ?_, by decide +kernel, ?_, fun a => ?_, by decide +kernel⟩
  · have hf' : (FinMagma.ofMul d4Equiv d4Names).FaithfulTable d4TableFigure := d4Table_eq ▸ hf
    rw [d4Table_eq]
    exact FinMagma.ofMul_entries d4Equiv d4Names hf' a b s
  · rw [d4Table_eq]
    exact FinMagma.ofMul_isGroup _ _
  · rw [← FinMagma.ofMul_isCommutative_iff d4Equiv d4Names, ← d4Table_eq]
    decide +kernel
  · rw [d4Table_eq]
    exact FinMagma.mem_centre_ofMul _ _ a

figure_proves d4TableFigure d4TableFigure_spec

/-- **The Cayley graph of the dihedral group of order 8.** Every arrow the figure draws, from
element `i` to element `j`, has `d4 j = d4 i * r 1` or `d4 j = d4 i * sr 0`; there are twelve,
eight for `r` and one line for each of the four pairs `{g, g s}`. -/
theorem d4CayleyFigure_spec :
    (∀ k i j, (k, i, j) ∈ d4CayleyFigure.arrows →
      ∃ (hi : i < 8) (hj : j < 8), d4 ⟨j, hj⟩ = d4 ⟨i, hi⟩ * .r 1 ∨
        d4 ⟨j, hj⟩ = d4 ⟨i, hi⟩ * .sr 0) ∧
    d4CayleyFigure.arrows.length = 12 := by
  have e : d4CayleyFigure.arrows = (d4Table.cayley d4Generators d4Positions).arrowTriples := by
    have h := CommDiagram.builder_faithful (d4Table.cayley d4Generators d4Positions)
      (by decide +kernel)
    rw [← h.1]
    unfold d4CayleyFigure FinMagma.cayleyFigure
    rw [Diagram.capped_of (by decide +kernel)]
    rfl
  refine ⟨fun k i j hk => ?_, by rw [e]; decide +kernel⟩
  rw [e] at hk
  simp only [CommDiagram.arrowTriples, List.mem_map, Prod.mk.injEq] at hk
  obtain ⟨⟨a, k'⟩, ha, -, rfl, rfl⟩ := hk
  have ha' : a ∈ d4Table.cayleyArrows d4Generators := by
    obtain ⟨-, h⟩ := List.mem_zipIdx' ha
    rw [h]
    exact List.getElem_mem _
  dsimp only
  obtain ⟨c, s, g, hs, -, hsrc, htgt, -⟩ := (d4Table.mem_cayleyArrows d4Generators a).1 ha'
  have hmul : ∀ a b : Fin 8, d4 (d4Mul a b) = d4 a * d4 b := by decide
  refine ⟨hsrc ▸ g.2, htgt ▸ (d4Table.mul g s).2, ?_⟩
  have hg : ∀ h, d4 ⟨a.src, h⟩ = d4 g := fun h => congrArg d4 (Fin.ext hsrc)
  have ht : ∀ h, d4 ⟨a.tgt, h⟩ = d4 g * d4 s := fun h =>
    (congrArg d4 (Fin.ext htgt)).trans (hmul g s)
  rw [hg, ht]
  have hs' : s = ⟨1, by decide⟩ ∨ s = ⟨4, by decide⟩ := by
    simp only [d4Generators] at hs
    match c, hs with
    | 0, hs => simp at hs; exact .inl hs.symm
    | 1, hs => simp at hs; exact .inr hs.symm
  rcases hs' with rfl | rfl
  · exact .inl rfl
  · exact .inr rfl

figure_proves d4CayleyFigure d4CayleyFigure_spec

/-! ### The subgroups of the dihedral group of order 8 -/

/-- Whether element `x` belongs to subgroup number `m`: bit `d4Index x` of its mask. -/
def inMask (m : Fin 10) (x : DihedralGroup 4) : Bool :=
  (d4SubgroupMasks.getD m 0).testBit (d4Index x)

/-- The subgroup number `m` of the figure. -/
def d4Sub (m : Fin 10) : Subgroup (DihedralGroup 4) where
  carrier := {x | inMask m x = true}
  one_mem' := by revert m; decide
  mul_mem' := by
    have h : ∀ m : Fin 10, ∀ a b : DihedralGroup 4, inMask m a = true → inMask m b = true →
      inMask m (a * b) = true := by decide
    exact fun {a b} => h m a b
  inv_mem' := by
    have h : ∀ m : Fin 10, ∀ a : DihedralGroup 4, inMask m a = true → inMask m a⁻¹ = true := by
      decide
    exact fun {a} => h m a

/-- A set of elements given by its indicator on the numbers, containing `1` and closed under
multiplication. -/
def closedIndicator (b : Fin 8 → Bool) : Bool :=
  b 0 && (List.finRange 8).all fun x => (List.finRange 8).all fun y =>
    !(b x && b y) || b (d4Index (d4 x * d4 y))

/-- Every indicator of a set containing `1` and closed under multiplication is the mask of one of
the ten subgroups. -/
theorem closedIndicator_mask : ∀ b : Fin 8 → Bool, closedIndicator b = true →
    ∃ m : Fin 10, ∀ k : Fin 8, b k = (d4SubgroupMasks.getD m 0).testBit k := by
  decide +kernel

/-- The ten subgroups are all the subgroups of `DihedralGroup 4`, each once. -/
theorem d4Sub_bijective : Function.Bijective d4Sub := by
  constructor
  · intro i j h
    have key : ∀ i j : Fin 10, (∀ x, inMask i x = inMask j x) → i = j := by decide
    refine key i j fun x => ?_
    have := SetLike.ext_iff.1 h x
    simp only [d4Sub, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
      Set.mem_ofPred_eq] at this
    exact Bool.eq_iff_iff.2 this
  · intro H
    classical
    let b : Fin 8 → Bool := fun k => decide (d4 k ∈ H)
    have hb : closedIndicator b = true := by
      simp only [closedIndicator, b, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        List.mem_finRange, true_implies, Bool.or_eq_true, Bool.not_eq_true',
        Bool.and_eq_false_imp]
      refine ⟨by simp [d4], fun x y => ?_⟩
      by_cases hx : d4 x ∈ H
      · by_cases hy : d4 y ∈ H
        · right
          have : d4 (d4Index (d4 x * d4 y)) = d4 x * d4 y := d4Equiv.apply_symm_apply _
          simpa [this] using H.mul_mem hx hy
        · left; simp [hx, hy]
      · left; simp [hx]
    obtain ⟨m, hm⟩ := closedIndicator_mask b hb
    refine ⟨m, SetLike.ext fun x => ?_⟩
    have h1 := hm (d4Index x)
    have h2 : d4 (d4Index x) = x := d4Equiv.apply_symm_apply x
    simp only [b, h2] at h1
    simp only [d4Sub, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq,
      inMask]
    rw [← h1, decide_eq_true_iff]

/-- The enumeration of the subgroups. -/
noncomputable def d4SubEquiv : Fin 10 ≃ Subgroup (DihedralGroup 4) :=
  Equiv.ofBijective d4Sub d4Sub_bijective

/-- The figure's order is inclusion of subgroups. -/
theorem d4Subgroups_le (i j : Fin 10) : d4Subgroups.le i j = true ↔ d4Sub i ≤ d4Sub j := by
  have key : ∀ i j : Fin 10, (d4SubgroupMasks.getD i 0 &&& d4SubgroupMasks.getD j 0 ==
      d4SubgroupMasks.getD i 0) = true ↔ ∀ x, inMask i x = true → inMask j x = true := by decide
  exact (key i j).trans Iff.rfl

/-- Subgroup number `m` is normal exactly when the figure marks it. -/
theorem d4Sub_normal (m : Fin 10) : (d4Sub m).Normal ↔ d4Normal.getD m false = true := by
  have key : ∀ m : Fin 10, (∀ n, inMask m n = true → ∀ g : DihedralGroup 4,
      inMask m (g * n * g⁻¹) = true) ↔ d4Normal.getD m false = true := by decide
  rw [← key]
  exact ⟨fun h n hn g => h.conj_mem n hn g, fun h => ⟨fun n hn g => h n hn g⟩⟩

/-- **The lattice of subgroups of the dihedral group of order 8.** The drawn elements are the
subgroups of `DihedralGroup 4`, each exactly once (`d4Sub` is a bijection onto
`Subgroup (DihedralGroup 4)`); an edge joins `a` to `b` exactly when `d4Sub a ⋖ d4Sub b` in the
lattice of subgroups; and the dot of a subgroup is drawn in accent 1 exactly when the subgroup is
normal. -/
theorem d4SubgroupsFigure_spec :
    Function.Bijective d4Sub ∧
    (∀ a b : Fin 10, ((a : ℕ), (b : ℕ)) ∈ d4SubgroupsFigure.edges ↔ d4Sub a ⋖ d4Sub b) ∧
    (∀ (a : Fin 10) (m : Mark) (p : QPoint), m ∈ d4SubgroupsFigure.marks →
      m.part = .vertex a → m.shape = .dot p → (m.ink = .accent 1 ↔ (d4Sub a).Normal)) := by
  have h := d4Subgroups.builder_faithful (by decide)
  refine ⟨d4Sub_bijective, fun a b => ?_, fun a m p hm hp hs => ?_⟩
  · rw [show d4SubgroupsFigure.edges = d4Subgroups.figure.edges from rfl, h.1]
    exact FinPoset.mem_coverPairs_of_equiv d4Subgroups d4SubEquiv d4Subgroups_le a b
  · have := FinGraph.ink_of_faithful h hm hp hs
    rw [this, d4Sub_normal]
    simp only [FinGraph.dotInk, FinPoset.toFinGraph, d4Subgroups]
    by_cases hn : d4Normal.getD a false = true <;> simp [hn]

figure_proves d4SubgroupsFigure d4SubgroupsFigure_spec

/-! ### A commutative square of types -/

/-- Reduction from `ZMod a` to `ZMod b`, as a function of types. -/
def reduce (a b : ℕ) [NeZero a] : ZMod a → ZMod b := fun x => (x.val : ZMod b)

/-- **A commutative square in the category of types.** The figure draws the square of the four
reductions `ZMod 12 → ZMod 6`, `ZMod 12 → ZMod 4`, `ZMod 6 → ZMod 2`, `ZMod 4 → ZMod 2` with its
claim; the square commutes in the sense of the drawing (`CommDiagram.Realisation.Commutes`) for
those maps as morphisms of `Type`, which is `CommSq` of Mathlib. -/
theorem commSqFigure_spec :
    squareDiagram = CommDiagram.square squareObjects squareLabels ∧
    squareDiagram.Faithful squareDiagram.layout commSqFigure ∧
    commSqFigure.arrows = [(0, 0, 1), (1, 0, 2), (2, 1, 3), (3, 2, 3)] ∧
    (CommDiagram.squareRealisation squareObjects squareLabels (TypeCat.ofHom (reduce 12 6))
      (TypeCat.ofHom (reduce 12 4)) (TypeCat.ofHom (reduce 6 2))
      (TypeCat.ofHom (reduce 4 2))).Commutes ∧
    CommSq (TypeCat.ofHom (reduce 12 6)) (TypeCat.ofHom (reduce 12 4))
      (TypeCat.ofHom (reduce 6 2)) (TypeCat.ofHom (reduce 4 2)) := by
  have hsq : CommSq (TypeCat.ofHom (reduce 12 6)) (TypeCat.ofHom (reduce 12 4))
      (TypeCat.ofHom (reduce 6 2)) (TypeCat.ofHom (reduce 4 2)) := by
    constructor
    ext x
    change reduce 6 2 (reduce 12 6 x) = reduce 4 2 (reduce 12 4 x)
    revert x
    decide
  have h := squareDiagram.builder_faithful (by decide)
  refine ⟨rfl, h, ?_, (CommDiagram.square_commutes_iff _ _ _ _ _ _).2 hsq, hsq⟩
  rw [show commSqFigure.arrows = squareDiagram.figure.arrows from rfl, h.1]
  decide

figure_proves commSqFigure commSqFigure_spec

/-! ### A short exact sequence -/

/-- **The drawing of a short exact sequence.** The figure draws `0 → A ↣ B ↠ C → 0`, left to
right, with its arrows written out; and for every short complex `S` of a preadditive category with
a zero object, realised on the drawing (`S.f` for `f`, `S.g` for `g`), the marks `↣` and `↠` hold
(`S.f` is a monomorphism, `S.g` an epimorphism) and `S` is exact exactly when `S` is short exact
in Mathlib's sense. -/
theorem shortExactFigure_spec :
    shortExactDiagram = CommDiagram.shortExact #["A", "B", "C"] "f" "g" ∧
    shortExactDiagram.Faithful shortExactDiagram.layout shortExactFigure ∧
    shortExactFigure.arrows = [(0, 0, 1), (1, 1, 2), (2, 2, 3), (3, 3, 4)] ∧
    ∀ (C : Type) [Category C] [Preadditive C] [Limits.HasZeroObject C]
      (S : ShortComplex C),
      (CommDiagram.shortExactRealisation #["A", "B", "C"] "f" "g" S).StylesHold ∧ S.Exact ↔
        S.ShortExact := by
  have h := shortExactDiagram.builder_faithful (by decide)
  refine ⟨rfl, h, ?_, fun C _ _ _ S => CommDiagram.shortExact_iff _ _ _ S⟩
  rw [show shortExactFigure.arrows = shortExactDiagram.figure.arrows from rfl, h.1]
  decide

figure_proves shortExactFigure shortExactFigure_spec

end PILeanMathlib.Examples
