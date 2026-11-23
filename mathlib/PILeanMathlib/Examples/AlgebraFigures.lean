/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Diagram.CommDiagram
import PILean.Diagram.Group
import PILean.Diagram.Hasse
import PILean.Trust.Attr

/-!
# Figures of algebra tied to Mathlib's objects: the figures

The figures, built from plain data with PILean only (this module imports nothing from Mathlib).
`PILeanMathlib.Examples.Algebra` proves what each one draws in Mathlib's terms: the Cayley table
and a Cayley graph of the dihedral group `DihedralGroup 4` of order 8, its lattice of subgroups
with the normal ones marked, a commutative square of maps in the category of types, and the
drawing of a short exact sequence.

The elements of `DihedralGroup 4` are numbered `0, …, 7`: `k < 4` is the rotation `r k` and
`4 + k` the reflection `sr k`.
-/

namespace PILeanMathlib.Examples

open PILean PILean.Diagram

/-! ### The dihedral group of order 8 -/

/-- The product of the elements numbered `a` and `b` of the dihedral group of order 8, by the
rules `r i * r j = r (i + j)`, `r i * sr j = sr (j - i)`, `sr i * r j = sr (i + j)`,
`sr i * sr j = r (j - i)`. -/
def d4Mul (a b : Fin 8) : Fin 8 :=
  let i := a.val % 4
  let j := b.val % 4
  if a.val < 4 then
    if b.val < 4 then ⟨(i + j) % 4, by omega⟩ else ⟨4 + (j + 4 - i) % 4, by omega⟩
  else
    if b.val < 4 then ⟨4 + (i + j) % 4, by omega⟩ else ⟨(j + 4 - i) % 4, by omega⟩

/-- The names of the elements: `1, r, r², r³, s, sr, sr², sr³`. -/
def d4Names : Array String := #["1", "r", "r²", "r³", "s", "sr", "sr²", "sr³"]

/-- The dihedral group of order 8 as a table. -/
def d4Table : FinMagma := ⟨8, d4Mul, d4Names⟩

/-- The Cayley table of the dihedral group of order 8. -/
@[figure]
def d4TableFigure : Diagram :=
  { d4Table.tableFigure with title := "The Cayley table of the dihedral group of order 8" }

/-- The positions of the Cayley graph: the rotations on a square, each reflection `r^k s` (that
is `sr (-k)`) outside the rotation `r^k`. -/
def d4Positions : Array QPoint :=
  #[(0, 1 / 2), (1 / 2, 0), (0, -1 / 2), (-1 / 2, 0), (0, 1), (-1, 0), (0, -1), (1, 0)]

/-- The generators `r` and `s`. -/
def d4Generators : List (Fin d4Table.n) := [⟨1, by decide⟩, ⟨4, by decide⟩]

/-- The Cayley graph of the dihedral group of order 8 for `r` and `s`. -/
@[figure]
def d4CayleyFigure : Diagram :=
  { d4Table.cayleyFigure d4Generators d4Positions with
    title := "The Cayley graph of the dihedral group of order 8 for r and s", width := 340 }

/-- The ten subgroups of the dihedral group of order 8, as bit masks of their elements (bit `k`
for element `k`): `{1}`, `⟨s⟩`, `⟨sr²⟩`, `⟨r²⟩`, `⟨sr⟩`, `⟨sr³⟩`, `⟨r², s⟩`, `⟨r⟩`,
`⟨r², sr⟩`, the group (numbered so that the layered drawing has few crossings). -/
def d4SubgroupMasks : Array Nat := #[1, 17, 65, 5, 33, 129, 85, 15, 165, 255]

/-- Generators of each subgroup, by element number (none for the trivial subgroup). -/
def d4SubgroupGens : Array (List Nat) :=
  #[[], [4], [6], [2], [5], [7], [2, 4], [1], [2, 5], [1, 4]]

/-- The name of a subgroup from its generators: `⟨g, h⟩`, or `1` for none. -/
def genName (gs : List Nat) : String :=
  if gs.isEmpty then "1" else "⟨" ++ ", ".intercalate (gs.map fun g => d4Names.getD g "") ++ "⟩"

/-- Which of them are normal (checked against Mathlib's `Subgroup.Normal` in
`PILeanMathlib.Examples.Algebra`). -/
def d4Normal : Array Bool := #[true, false, false, true, false, false, true, true, true, true]

/-- The subgroups ordered by inclusion of their masks, the normal ones marked. -/
def d4Subgroups : FinPoset where
  n := 10
  le i j := d4SubgroupMasks.getD i 0 &&& d4SubgroupMasks.getD j 0 == d4SubgroupMasks.getD i 0
  names := d4SubgroupGens.map genName
  marked := d4Normal

/-- The lattice of subgroups of the dihedral group of order 8, normal subgroups in colour. -/
@[figure]
def d4SubgroupsFigure : Diagram :=
  { d4Subgroups.figure with
    title := "The subgroups of the dihedral group of order 8, normal ones in colour",
    width := 380 }

/-! ### Commutative diagrams in a category -/

/-- The labels of the square. -/
def squareObjects : Array String := #["ℤ/12", "ℤ/6", "ℤ/4", "ℤ/2"]

/-- The labels of its arrows. -/
def squareLabels : Array String := #["π₆", "π₄", "π₂", "π₂"]

/-- The square of reductions, as `CommDiagram.square` of `PILeanMathlib.Category` draws it. -/
def squareDiagram : CommDiagram where
  objects := squareObjects
  pos := #[(0, 0), (1, 0), (0, -1), (1, -1)]
  arrows := [{ src := 0, tgt := 1, label := squareLabels.getD 0 "" },
    { src := 0, tgt := 2, label := squareLabels.getD 1 "", swap := true },
    { src := 1, tgt := 3, label := squareLabels.getD 2 "" },
    { src := 2, tgt := 3, label := squareLabels.getD 3 "", swap := true }]
  paths := [(0, [0, 2], [1, 3])]

/-- A commutative square of reductions in the category of types. -/
@[figure]
def commSqFigure : Diagram :=
  { squareDiagram.figure with title := "A commutative square in the category of types" }

/-- The drawing `0 → A ↣ B ↠ C → 0`. -/
def shortExactDiagram : CommDiagram where
  objects := #["0", "A", "B", "C", "0"]
  pos := #[(0, 0), (1, 0), (2, 0), (3, 0), (4, 0)]
  arrows := [{ src := 0, tgt := 1 }, { src := 1, tgt := 2, label := "f", style := .mono },
    { src := 2, tgt := 3, label := "g", style := .epi }, { src := 3, tgt := 4 }]

/-- A short exact sequence. -/
@[figure]
def shortExactFigure : Diagram :=
  { shortExactDiagram.figure with title := "A short exact sequence" }

/-- The figures by file stem. -/
def algebraFigures : Array (String × Diagram) :=
  #[("dihedral-table", d4TableFigure), ("dihedral-cayley", d4CayleyFigure),
    ("dihedral-subgroups", d4SubgroupsFigure), ("comm-square", commSqFigure),
    ("short-exact", shortExactFigure)]

end PILeanMathlib.Examples
