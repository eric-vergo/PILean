/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Cover
import Mathlib.Data.Finset.Card
import PILeanMathlib.Combinatorics
import PILeanMathlib.Examples.CombinatoricsFigures

/-!
# Combinatorial figures tied to Mathlib's objects: the theorems

Each figure of `PILeanMathlib.Examples.CombinatoricsFigures` is linked by `figure_proves` to a
theorem that states, with Mathlib's definitions, what its drawn parts are.

## Main results

* `divisorsFigure_spec`: the elements are `Nat.divisors 60`, and an edge joins `a` to `b` exactly
  when `a ∣ b` and `b / a` is prime (the covers of the divisor lattice).
* `subsetsFigure_spec`: an edge joins `a` to `b` exactly when `subset a ⋖ subset b` (`CovBy`) in
  `Finset (Fin 3)`.
* `petersenFigure_spec`: the edges are those of `petersenGraph : SimpleGraph (Fin 10)`, the
  disjointness graph of the 2-subsets of `Fin 5`.
* `youngFigure_spec`, `highestWeightFigure_spec`: the cells are those of a `YoungDiagram`, the
  entries those of `SemistandardYoungTableau.highestWeight`.
* `cyclesFigure_spec`, `wiringFigure_spec`: the arrows are `a → σ a` and the crossings the
  inversions of `σ = swap 0 3 * swap 2 4`, whose sign is `(-1)` to their number.
* `dyckFigure_spec`: the path of a `DyckWord`, rising exactly at its `U`s.
* `vennFigure_spec`: each number is written inside the circle of each `Finset` exactly when it
  belongs to it.
-/

open PILean PILean.Diagram

namespace PILeanMathlib.Examples

/-! ### The divisors of 60 -/

/-- The figure draws the divisors of 60 (`Nat.divisors 60`), and an edge from `a` up to `b`
exactly when `a ∣ b` and `b / a` is prime: the covering relation of divisibility. Divisibility on
them is a partial order, so the transitive closure of the edges is strict divisibility
(`FinPoset.transGen_covers_iff`). -/
theorem divisorsFigure_spec :
    divisors60.toFinset = Nat.divisors 60 ∧ divisorOrder.IsPartialOrder ∧
    ∀ a b : Fin 12, ((a : ℕ), (b : ℕ)) ∈ divisorsFigure.edges ↔
      divisors60[a]! ∣ divisors60[b]! ∧ (divisors60[b]! / divisors60[a]!).Prime := by
  have h := divisorOrder.builder_faithful (by decide)
  refine ⟨by decide, ⟨by decide, by decide, by decide⟩, ?_⟩
  rw [show divisorsFigure.edges = divisorOrder.figure.edges from rfl, h.1]
  decide

figure_proves divisorsFigure divisorsFigure_spec

/-! ### Subsets of a 3-set -/

/-- The subset of `Fin 3` of a bit mask. -/
def subset (i : Fin 8) : Finset (Fin 3) := Finset.univ.filter fun k => i.val.testBit k

/-- `subset` enumerates `Finset (Fin 3)`. -/
noncomputable def subsetEquiv : Fin 8 ≃ Finset (Fin 3) := Equiv.ofBijective subset (by decide)

/-- The figure's order is inclusion of the enumerated subsets. -/
theorem subsetOrder_eq : subsetOrder = FinPoset.ofOrder subsetEquiv subsetOrder.names := by
  simp only [subsetOrder, FinPoset.ofOrder, FinPoset.mk.injEq, heq_eq_eq, and_true, true_and]
  funext i j
  revert i j
  decide

/-- The figure draws an edge from `a` up to `b` exactly when `subset a ⋖ subset b` in
`Finset (Fin 3)`, Mathlib's covering relation (one element more). -/
theorem subsetsFigure_spec (a b : Fin 8) :
    ((a : ℕ), (b : ℕ)) ∈ subsetsFigure.edges ↔ subset a ⋖ subset b := by
  have h := subsetOrder.builder_faithful (by decide)
  rw [show subsetsFigure.edges = subsetOrder.figure.edges from rfl, h.1]
  have := FinPoset.ofOrder_mem_coverPairs subsetEquiv subsetOrder.names a b
  rw [← subsetOrder_eq] at this
  exact this

figure_proves subsetsFigure subsetsFigure_spec

/-! ### The Petersen graph -/

/-- The 2-subsets of `Fin 5`, in lexicographic order. -/
def pair (i : Fin 10) : Finset (Fin 5) :=
  let (a, b) := pairs5.getD i.val (0, 0)
  {⟨a % 5, Nat.mod_lt _ (by omega)⟩, ⟨b % 5, Nat.mod_lt _ (by omega)⟩}

/-- The Petersen graph: the Kneser graph `K(5, 2)`, two 2-subsets of `Fin 5` adjacent when they
are disjoint. -/
def petersenGraph : SimpleGraph (Fin 10) where
  Adj i j := i ≠ j ∧ Disjoint (pair i) (pair j)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel petersenGraph.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ Disjoint (pair i) (pair j)))

/-- The figure's graph is the simple graph `petersenGraph`. -/
theorem kneserGraph_eq : kneserGraph = FinGraph.ofSimpleGraph petersenGraph kneserGraph.names := by
  simp only [kneserGraph, FinGraph.ofSimpleGraph, FinGraph.mk.injEq, heq_eq_eq, and_true,
    true_and]
  funext i j
  revert i j
  decide

/-- The figure draws exactly the edges of `petersenGraph`, each once as `(a, b)` with `a < b`. -/
theorem petersenFigure_spec (a b : Fin 10) :
    ((a : ℕ), (b : ℕ)) ∈ petersenFigure.edges ↔ a < b ∧ petersenGraph.Adj a b := by
  rw [show petersenFigure.edges = (kneserGraph.draw kneserLayout).edges from rfl,
    (kneserGraph.draw_faithful kneserLayout).1, kneserGraph_eq,
    FinGraph.ofSimpleGraph_mem_edgePairs]

figure_proves petersenFigure petersenFigure_spec

/-! ### A Young diagram and a tableau -/

/-- The Young diagram of the partition `(5, 3, 3, 1)` of 12. -/
def young5331 : YoungDiagram := YoungDiagram.ofRowLens [5, 3, 3, 1] (by decide)

/-- The figure draws exactly the cells of `young5331` (`YoungDiagram.cells`). -/
theorem youngFigure_spec (i j : ℕ) : (i, j) ∈ youngFigure.cells ↔ (i, j) ∈ young5331.cells := by
  have e : young5331.rowLens = [5, 3, 3, 1] :=
    YoungDiagram.rowLens_ofRowLens_eq_self (by decide)
  rw [show youngFigure.cells = (YoungShape.mk [5, 3, 3, 1] .english).draw.cells from rfl,
    ← e, ← YoungShape.ofYoungDiagram]
  exact YoungShape.ofYoungDiagram_cells _ _ i j

figure_proves youngFigure youngFigure_spec

/-- The Young diagram of `(4, 3, 1)`. -/
def young431 : YoungDiagram := YoungDiagram.ofRowLens [4, 3, 1] (by decide)

/-- The figure writes, at each cell `(i, j)` of `young431`, the entry of Mathlib's highest-weight
tableau `SemistandardYoungTableau.highestWeight young431`, and nothing else. -/
theorem highestWeightFigure_spec (i j : ℕ) (s : String) :
    ((i, j), s) ∈ highestWeightFigure.entries ↔
      (i, j) ∈ young431 ∧ s = toString (SemistandardYoungTableau.highestWeight young431 i j) := by
  have e : Tableau.mk [[0, 0, 0, 0], [1, 1, 1], [2]] .english =
      Tableau.ofSSYT (SemistandardYoungTableau.highestWeight young431) .english := by
    have hr : young431.rowLens = [4, 3, 1] := YoungDiagram.rowLens_ofRowLens_eq_self (by decide)
    simp only [Tableau.ofSSYT, hr, SemistandardYoungTableau.highestWeight_apply, Tableau.mk.injEq,
      and_true]
    simp only [young431, YoungDiagram.mem_ofRowLens]
    decide
  rw [show highestWeightFigure.entries =
      (Tableau.mk [[0, 0, 0, 0], [1, 1, 1], [2]] .english).draw.entries from rfl, e]
  exact Tableau.ofSSYT_entries _ _ i j s

figure_proves highestWeightFigure highestWeightFigure_spec

/-! ### A permutation -/

/-- The permutation `(0 3)(2 4)` of `Fin 5`. -/
def σ5 : Equiv.Perm (Fin 5) := Equiv.swap 0 3 * Equiv.swap 2 4

/-- The figure's permutation is `σ5`. -/
theorem sigma_eq : sigma = FinPerm.ofPerm σ5 := by
  simp only [sigma, FinPerm.ofPerm, FinPerm.mk.injEq, and_true]
  decide

/-- The cycle diagram draws an arrow `a → b` exactly when `σ5 a = b`. -/
theorem cyclesFigure_spec (a b : Fin 5) :
    ((a : ℕ), (b : ℕ)) ∈ cyclesFigure.edges ↔ σ5 a = b := by
  rw [show cyclesFigure.edges = sigma.cycles.edges from rfl, sigma_eq]
  exact FinPerm.ofPerm_cycles_edges σ5 a b

figure_proves cyclesFigure cyclesFigure_spec

/-- The strands of the wiring diagram that cross are exactly the inversions of `σ5`; there are
six, and the sign of `σ5` is `(-1)` to their number. -/
theorem wiringFigure_spec :
    (∀ a b : Fin 5, ((a : ℕ), (b : ℕ)) ∈ crossingPairs wiringFigure.strands ↔ a < b ∧ σ5 b < σ5 a) ∧
    (crossingPairs wiringFigure.strands).length = 6 ∧
    Equiv.Perm.sign σ5 = (-1) ^ (crossingPairs wiringFigure.strands).length := by
  have e : wiringFigure.strands = (FinPerm.ofPerm σ5).wiring.strands := by
    rw [show wiringFigure.strands = sigma.wiring.strands from rfl, sigma_eq]
  refine ⟨fun a b => by rw [e]; exact FinPerm.ofPerm_crossings σ5 a b, ?_, ?_⟩
  · rw [e, FinPerm.wiring_crossings]
    decide
  · rw [e, FinPerm.wiring_crossings, show (FinPerm.ofPerm σ5).inversions.length = 6 by decide]
    rw [σ5, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide

figure_proves wiringFigure wiringFigure_spec

/-! ### A Dyck word -/

/-- The letters of `UUDUUDDDUD`. -/
def dyckSteps : List DyckStep := [.U, .U, .D, .U, .U, .D, .D, .D, .U, .D]

/-- Every prefix of `UUDUUDDDUD` has at least as many `U`s as `D`s. -/
theorem dyckSteps_prefix (i : ℕ) : (dyckSteps.take i).count .D ≤ (dyckSteps.take i).count .U := by
  have key : ∀ i < 11, (dyckSteps.take i).count .D ≤ (dyckSteps.take i).count .U := by decide
  rcases Nat.lt_or_ge i 11 with h | h
  · exact key i h
  · rw [List.take_of_length_le (by simp [dyckSteps]; omega)]
    decide

/-- The Dyck word `UUDUUDDDUD`. -/
def dyckWord : DyckWord where
  toList := dyckSteps
  count_U_eq_count_D := by decide
  count_D_le_count_U := dyckSteps_prefix

/-- The figure draws the path of `dyckWord`: its steps are those of `LatticePath.ofDyckWord`, and
step `k` rises exactly when letter `k` is `U`. -/
theorem dyckFigure_spec :
    (LatticePath.ofDyckWord dyckWord).Faithful dyckFigure ∧
    ∀ k (h : k < dyckWord.toList.length),
      (((LatticePath.ofDyckWord dyckWord).point (k + 1)).2 =
        ((LatticePath.ofDyckWord dyckWord).point k).2 + 1 ↔ dyckWord.toList[k] = .U) := by
  have e : LatticePath.ofDyck dyckBitsUUDUUDDDUD = LatticePath.ofDyckWord dyckWord := by
    simp only [LatticePath.ofDyckWord, dyckWord]
    congr 1
  refine ⟨?_, fun k h => LatticePath.ofDyckWord_step_rises dyckWord k h⟩
  rw [← e]
  exact (LatticePath.ofDyck dyckBitsUUDUUDDDUD).builder_faithful (by decide)

figure_proves dyckFigure dyckFigure_spec

/-! ### Three finsets -/

/-- The numbers of `1, …, 12` (as `Fin 12`, `x` for `x + 1`) that are multiples of `m`. -/
def multiplesOf (m : ℕ) : Finset (Fin 12) := Finset.univ.filter fun x => m ∣ x.val + 1

/-- The figure's set system is that of the finsets of multiples of 2, 3 and 5. -/
theorem multiples_eq :
    multiples = SetSystem.ofFinsets [multiplesOf 2, multiplesOf 3, multiplesOf 5] multiples.names
      multiples.setNames := by
  simp only [multiples, SetSystem.ofFinsets, SetSystem.mk.injEq, and_true, true_and]
  decide

/-- Every number is written inside the circle of the multiples of `m ∈ {2, 3, 5}` exactly when
it is a multiple of `m`. -/
theorem vennFigure_spec {x : Fin 12} {k : ℕ} {p : QPoint}
    (hx : ((x : ℕ), k, p) ∈ vennFigure.members) (s : Fin 3) :
    inside ((vennCentres 3).getD s (0, 0)) p = true ↔
      x ∈ [multiplesOf 2, multiplesOf 3, multiplesOf 5][s] := by
  have hm : vennFigure.members = multiples.venn.members := by
    rw [show vennFigure.members = multiples.vennFigure.members from rfl, SetSystem.vennFigure,
      Diagram.capped_of (by decide)]
  rw [hm, multiples_eq] at hx
  exact SetSystem.ofFinsets_venn_inside _ _ _ (by decide) (by decide) hx (by simp)

figure_proves vennFigure vennFigure_spec

end PILeanMathlib.Examples
