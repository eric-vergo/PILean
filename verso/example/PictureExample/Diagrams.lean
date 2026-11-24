/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Trust.Attr

/-!
# The example's diagrams

Three more figures, of the kinds of `PILean.Diagram`, and one whose name a page must escape:

* `divisorHasse`: the Hasse diagram of the divisors of 12 under divisibility, tied to its order
  by `divisorHasse_spec`;
* `reductionSquare`: a commutative square of reductions `ℤ/12 → ℤ/6 → ℤ/2`,
  `ℤ/12 → ℤ/4 → ℤ/2`, tied to its maps by `reductionSquare_spec`;
* `sketch`: the Young diagram of `(3, 2, 1)`, an illustration marked as one
  (`@[figure illustration]`): a picture with no theorem;
* `«hasse <b>"&'»`: the Hasse diagram of the divisors of 6, whose name holds markup, tied to its
  order by `«hasse <b>"&'_spec»`.
-/

namespace Example

open PILean PILean.Diagram

/-! ### A Hasse diagram -/

/-- The divisors of 12, in increasing order. -/
def divisorsOf12 : Array Nat := #[1, 2, 3, 4, 6, 12]

/-- The divisors of 12 ordered by divisibility: `i ≤ j` when the `i`-th divides the `j`-th. -/
def divisibility : FinPoset where
  n := 6
  le i j := divisorsOf12[j]! % divisorsOf12[i]! == 0
  names := divisorsOf12.map toString

/-- The divisors of 12 ordered by divisibility. -/
@[figure]
def divisorHasse : Diagram :=
  { divisibility.figure with title := "The divisors of 12 under divisibility", width := 240 }

/-- The figure draws exactly the seven covers of divisibility among the divisors of 12 (a
divisor and a prime multiple of it), written out; divisibility is a partial order, so its strict
order is the transitive closure of those edges. -/
theorem divisorHasse_spec :
    divisibility.Faithful divisibility.layout divisorHasse ∧
    divisorHasse.edges = [(0, 1), (0, 2), (1, 3), (1, 4), (2, 4), (3, 5), (4, 5)] ∧
    divisibility.IsPartialOrder :=
  ⟨divisibility.builder_faithful (by decide), by decide +kernel,
    ⟨by decide, by decide, by decide⟩⟩

figure_links divisorHasse divisorHasse_spec

/-! ### A commutative square -/

/-- Reduction modulo `m` on `{0, …, n - 1}`, as a table. -/
def reduction (n m : Nat) : Array Nat := ((List.range n).map (· % m)).toArray

/-- The square of reductions `ℤ/12 → ℤ/6 → ℤ/2` and `ℤ/12 → ℤ/4 → ℤ/2`. -/
def reductions : CommDiagram where
  objects := #["ℤ/12", "ℤ/6", "ℤ/4", "ℤ/2"]
  pos := #[(0, 0), (1, 0), (0, -1), (1, -1)]
  arrows := [{ src := 0, tgt := 1, label := "π₆", style := .epi },
    { src := 0, tgt := 2, label := "π₄", style := .epi, swap := true },
    { src := 1, tgt := 3, label := "π₂", style := .epi },
    { src := 2, tgt := 3, label := "π₂", style := .epi, swap := true }]
  paths := [(0, [0, 2], [1, 3])]

/-- The maps of the square: the reductions. -/
def reductionMaps : FinMaps where
  card := #[12, 6, 4, 2]
  fn := #[reduction 12 6, reduction 12 4, reduction 6 2, reduction 4 2]

/-- The square of reductions of `ℤ/12`. -/
@[figure]
def reductionSquare : Diagram :=
  { reductions.figure with title := "Reductions of ℤ/12: a commutative square" }

/-- The figure draws the four arrows of the square, `ℤ/12 → ℤ/6`, `ℤ/12 → ℤ/4`, `ℤ/6 → ℤ/2` and
`ℤ/4 → ℤ/2` (written out) with their labels; the reductions make the square commute and are
surjective, as their tips `↠` say. -/
theorem reductionSquare_spec :
    reductions.Faithful reductions.layout reductionSquare ∧
    reductionSquare.arrows = [(0, 0, 1), (1, 0, 2), (2, 1, 3), (3, 2, 3)] ∧
    reductionSquare.arrowTexts = [(0, "π₆"), (1, "π₄"), (2, "π₂"), (3, "π₂")] ∧
    reductionMaps.Commutes reductions = true ∧
    reductionMaps.StylesHold reductions = true :=
  ⟨reductions.builder_faithful (by decide +kernel), by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

figure_links reductionSquare reductionSquare_spec

/-! ### An illustration -/

/-- The Young diagram of the partition `(3, 2, 1)` of 6: shown for what it shows, with no
theorem about it. -/
@[figure illustration]
def sketch : Diagram :=
  let young : YoungShape := { rows := [3, 2, 1] }
  { young.figure with width := 160, title := "The partition (3, 2, 1)" }

/-! ### A name that holds markup -/

/-- The divisors of 6 ordered by divisibility. -/
def divisibility6 : FinPoset where
  n := 4
  le i j := #[1, 2, 3, 6][j]! % #[1, 2, 3, 6][i]! == 0
  names := #["1", "2", "3", "6"]

/-- The divisors of 6, under a name that holds markup a page must escape. -/
@[figure]
def «hasse <b>"&'» : Diagram := { divisibility6.figure with title := "<b>divisors</b> & \"6\"" }

/-- The figure draws exactly the four covers of divisibility among the divisors of 6. -/
theorem «hasse <b>"&'_spec» : «hasse <b>"&'».edges = [(0, 1), (0, 2), (1, 3), (2, 3)] := by
  decide +kernel

figure_links «hasse <b>"&'» «hasse <b>"&'_spec»

end Example
