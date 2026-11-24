/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Diagram.Hasse
import PILean.Diagram.Path
import PILean.Diagram.Perm
import PILean.Diagram.SetSystem
import PILean.Diagram.Young
import PILean.Trust.Attr

/-!
# Combinatorial figures and Mathlib's objects: the figures

The figures, built from plain data with PILean only (this module imports nothing from Mathlib, so
the program that draws them does not contain it). `PILeanMathlib.Examples.Combinatorics` proves
that each draws a Mathlib object: the divisors of 60 (`Nat.divisors`) and their covers, the
subsets of a 3-set with Mathlib's `CovBy`, the Petersen graph as a `SimpleGraph`, a
`YoungDiagram` and its highest-weight `SemistandardYoungTableau`, a permutation
`Equiv.Perm (Fin 5)`, a `DyckWord`, and three `Finset`s in a Venn diagram.
-/

namespace PILeanMathlib.Examples

open PILean PILean.Diagram

/-- The divisors of 60 in increasing order. -/
def divisors60 : List Nat := (List.range 61).filter fun d => 0 < d && 60 % d == 0

/-- The divisors of 60 ordered by divisibility. -/
def divisorOrder : FinPoset where
  n := divisors60.length
  le i j := divisors60.getD j.val 0 % divisors60.getD i.val 1 == 0
  names := (divisors60.map toString).toArray

/-- The Hasse diagram of the divisors of 60. -/
@[figure]
def divisorsFigure : Diagram :=
  { divisorOrder.figure with title := "The divisors of 60, ordered by divisibility", width := 360 }

/-- The subsets of `{0, 1, 2}` as the bit masks `0, …, 7`, ordered by inclusion. -/
def subsetOrder : FinPoset where
  n := 8
  le i j := i.val &&& j.val == i.val
  names := #["∅", "{0}", "{1}", "{0,1}", "{2}", "{0,2}", "{1,2}", "{0,1,2}"]

/-- The Hasse diagram of the subsets of `{0, 1, 2}`. -/
@[figure]
def subsetsFigure : Diagram :=
  { subsetOrder.figure with title := "The subsets of {0, 1, 2}", width := 300 }

/-- The 2-subsets of `{0, …, 4}` in lexicographic order. -/
def pairs5 : List (Nat × Nat) :=
  (List.range 5).flatMap fun a => ((List.range 5).filter (a < ·)).map fun b => (a, b)

/-- The Kneser graph `K(5, 2)`: two 2-subsets are adjacent when they are disjoint. -/
def kneserGraph : FinGraph where
  n := 10
  adj i j :=
    let (a, b) := pairs5.getD i.val (0, 0)
    let (c, d) := pairs5.getD j.val (0, 0)
    a != c && a != d && b != c && b != d
  names := (pairs5.map fun (a, b) => s!"{a}{b}").toArray

/-- A pentagon around a pentagram: the outer 5-cycle `01, 23, 04, 12, 34` on the unit circle and
the other vertices at half the radius. -/
def kneserLayout : Layout :=
  let at_ := fun (r : Rat) (k : Nat) =>
    let p := (Layout.circular 5).pos k
    (r * p.1, r * p.2)
  Layout.given ((List.range 10).map fun v =>
    match [0, 7, 3, 4, 9].idxOf? v, [8, 6, 5, 2, 1].idxOf? v with
    | some k, _ => at_ 1 k
    | none, some k => at_ (1 / 2) k
    | none, none => (0, 0)).toArray

/-- The Petersen graph. -/
@[figure]
def petersenFigure : Diagram :=
  { kneserGraph.draw kneserLayout with title := "The Petersen graph", width := 340 }

/-- The Young diagram of `(5, 3, 3, 1)`. -/
@[figure]
def youngFigure : Diagram :=
  { (YoungShape.mk [5, 3, 3, 1] .english).figure with
    title := "The Young diagram of (5, 3, 3, 1)", width := 220 }

/-- The highest-weight tableau of shape `(4, 3, 1)`: row `i` filled with `i`, from 0. -/
@[figure]
def highestWeightFigure : Diagram :=
  { (Tableau.mk [[0, 0, 0, 0], [1, 1, 1], [2]] .english).figure with
    title := "The highest-weight tableau of shape (4, 3, 1)", width := 200 }

/-- The permutation `σ = (0 3)(2 4)` of `Fin 5`, `42513` from 1. -/
def sigma : FinPerm := { values := [3, 1, 4, 0, 2] }

/-- The cycle diagram of `σ`. -/
@[figure]
def cyclesFigure : Diagram :=
  { sigma.figure FinPerm.cycles with title := "The cycles of (1 4)(3 5)", width := 260 }

/-- The wiring diagram of `σ`. -/
@[figure]
def wiringFigure : Diagram :=
  { sigma.figure FinPerm.wiring with title := "The wiring diagram of 42513" }

/-- The Dyck word `UUDUUDDDUD`. -/
def dyckBitsUUDUUDDDUD : List Bool :=
  [true, true, false, true, true, false, false, false, true, false]

/-- The path of the Dyck word `UUDUUDDDUD`. -/
@[figure]
def dyckFigure : Diagram :=
  { (LatticePath.ofDyck dyckBitsUUDUUDDDUD).figure with title := "The Dyck word UUDUUDDDUD" }

/-- The numbers `1, …, 12` and their multiples of 2, 3 and 5 (element `x` is `x + 1`). -/
def multiples : SetSystem where
  n := 12
  sets := [2, 3, 5].map fun m => (List.range 12).filter fun x => (x + 1) % m == 0
  names := ((List.range 12).map fun x => toString (x + 1)).toArray
  setNames := #["2ℤ", "3ℤ", "5ℤ"]

/-- The Venn diagram of the multiples of 2, 3 and 5 up to 12. -/
@[figure]
def vennFigure : Diagram :=
  { multiples.vennFigure with title := "Multiples of 2, 3 and 5 up to 12" }

/-- The figures by file stem. -/
def figures : Array (String × Diagram) :=
  #[("divisors-60", divisorsFigure), ("subsets", subsetsFigure), ("petersen", petersenFigure),
    ("young", youngFigure), ("highest-weight", highestWeightFigure), ("cycles", cyclesFigure),
    ("wiring", wiringFigure), ("dyck", dyckFigure), ("venn", vennFigure)]

end PILeanMathlib.Examples
