/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Mathlib.Data.ZMod.Basic
import PILeanMathlib.Lattice
import PILeanTest.Explorers

/-!
# The proved explorers against Mathlib

The two explorers of `PILeanTest.Explorers` are families over a grid of two parameters, each
linked to a theorem of the core quantified over the grid. Here the same families are bound to
Mathlib's objects, frame by frame:

* `cayleyExplorer_zmod`: at every point `(n, a)` of the grid, the arrows the frame draws join `s`
  to `t` exactly when `s` and `t` are elements of `ZMod n` (numbers below `n`) with `t = s + a` in
  `ZMod n`, each pair once when `2 a = 0` in `ZMod n`.
* `latticeExplorer_span`: at every point `(x, y)` of the grid, a point is drawn exactly when it is
  in `Submodule.span ℤ {(1, 0), (x, y)}` and in the window `[-3, 3] × [-2, 2]`, and no point is
  drawn twice.

Both statements name the explorer, so they are linked by `figure_proves` as well.
-/

open PILean PILean.Diagram PILeanTest.Explorers

namespace PILeanMathlib.Examples

/-- **The Cayley graphs in `ZMod n`.** At every point `(n, a)` of the explorer's grid (which the
statement takes from the explorer itself), the frame draws an arrow from `s` to `t` exactly when
`s < n`, `t < n`, `t = s + a` in `ZMod n`, and, when `2 a = 0` in `ZMod n` (the generator is an
involution, its pairs drawn as lines), `s < t`. -/
theorem cayleyExplorer_zmod :
    cayleyExplorer = Explorer.family₂ moduli generators cayleyFrame ∧
    ∀ n ∈ moduli.values, ∀ a ∈ generators.values, ∀ s t : ℕ,
      (s, t) ∈ (cayleyDiagram n a).arrows.map (fun x => (x.2.1, x.2.2)) ↔
        s < n ∧ t < n ∧ (t : ZMod n) = s + a ∧ (((2 * a : ℕ) : ZMod n) = 0 → s < t) := by
  obtain ⟨hx, -, -, -, -, -, h⟩ := cayleyExplorer_spec
  refine ⟨hx, fun n hn a ha s t => ?_⟩
  have hn0 : 0 < n := by simp only [moduli] at hn; revert hn; decide +revert
  rw [(h n hn a ha).2.2]
  simp only [cayleyPairs, List.mem_filterMap, List.mem_range]
  have hz : ((2 * a : ℕ) : ZMod n) = 0 ↔ (2 * a) % n = 0 := by
    rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
  constructor
  · rintro ⟨g, hg, he⟩
    split at he
    · cases he
    · rename_i hc
      cases he
      refine ⟨hg, Nat.mod_lt _ hn0, by rw [ZMod.natCast_mod]; push_cast; ring, fun h2 => ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not, not_lt, not_and, not_le] at hc
      exact hc (hz.1 h2)
  · rintro ⟨hs, ht, he, hinv⟩
    have htm : t = (s + a) % n := by
      rw [← Nat.mod_eq_of_lt ht]
      exact (ZMod.natCast_eq_natCast_iff' t (s + a) n).1 (by push_cast; exact he)
    refine ⟨s, hs, ?_⟩
    have hc : ¬((2 * a % n == 0 && !decide (s < (s + a) % n)) = true) := by
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not, not_lt, not_and, not_le]
      intro h2
      have := hinv (hz.2 h2)
      rw [htm] at this
      exact this
    simp only [hc, htm, Bool.false_eq_true, ite_false]

figure_proves cayleyExplorer cayleyExplorer_zmod

/-- **The lattices in Mathlib's terms.** At every point `(x, y)` of the explorer's grid, a point
`p` of the plane is drawn (at some position, in some colour) exactly when it is in
`Submodule.span ℤ {(1, 0), (x, y)}` and in the window `[-3, 3] × [-2, 2]`, and no point is drawn
twice. -/
theorem latticeExplorer_span :
    latticeExplorer = Explorer.family₂ periodX periodY latticeFrame ∧
    ∀ x ∈ periodX.values, ∀ y ∈ periodY.values,
      (∀ p : ℚ × ℚ, (∃ i col, (i, p, col) ∈ (latticeDiagram x y).dots) ↔
        p ∈ Submodule.span ℤ {((1 : ℚ), (0 : ℚ)), (x, y)} ∧
          -3 ≤ p.1 ∧ p.1 ≤ 3 ∧ -2 ≤ p.2 ∧ p.2 ≤ 2) ∧
      ((latticeDiagram x y).dots.map (·.2.1)).Nodup := by
  obtain ⟨hx, -, -, -, -, -, h⟩ := latticeExplorer_spec
  refine ⟨hx, fun x hxm y hym => ?_⟩
  obtain ⟨-, hdet, hf, -⟩ := h x hxm y hym
  refine ⟨fun p => ?_, (lattice x y).nodup_dots hdet hf⟩
  rw [(lattice x y).mem_dots_iff hdet hf]
  simp only [PlaneLattice.inWindow, lattice, Bool.and_eq_true]
  norm_num [and_assoc]
  exact fun _ => ⟨fun ⟨a, b, c, d⟩ => ⟨of_decide_eq_true a, of_decide_eq_true b,
    of_decide_eq_true c, of_decide_eq_true d⟩, fun ⟨a, b, c, d⟩ => ⟨decide_eq_true a,
    decide_eq_true b, decide_eq_true c, decide_eq_true d⟩⟩

figure_proves latticeExplorer latticeExplorer_span

end PILeanMathlib.Examples
