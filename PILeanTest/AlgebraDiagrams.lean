/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Trust.Attr
import PILeanTest.Diagrams

/-!
# The gallery of diagrams of algebra, their specifications and their checks

Figures of commutative diagrams, Cayley tables and graphs, and quivers, each with the attribute
`figure` and a specification linked by `figure_links`: what the figure draws, read back from its
marks (`Diagram.arrows`, `arrowTexts`, `entries`), is written out and checked by the kernel, and
the mathematical claims about the data (that the maps commute, that the marks of the arrows'
styles hold, that the table is a group) are decided. Changing the data breaks the specification
(`PILeanTest.SpecMutations`).

`checks` holds what the theorems do not: each predicate refuses diagrams with a planted fault in
every class of mark (an arrow's body, tip, style mark, label, an object, a 2-cell, a cell, its
colour, an entry, a heading, a rule), the figures pass the layout checks of plane figures in both
themes, and hostile data is refused within the caps.
-/

namespace PILeanTest.AlgebraDiagrams

open PILean PILean.Diagram PILeanTest.Diagrams

/-! ### A commutative square of finite maps -/

/-- Reduction modulo `m` on `{0, …, n - 1}`, as a table. -/
def reduction (n m : Nat) : Array Nat := ((List.range n).map (· % m)).toArray

/-- The square of reductions `ℤ/12 → ℤ/6 → ℤ/2` and `ℤ/12 → ℤ/4 → ℤ/2`. -/
def reductionSquare : CommDiagram where
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

/-- The square of reductions. -/
@[figure]
def square : Diagram :=
  { reductionSquare.figure with title := "Reductions of ℤ/12: a commutative square" }

/-- The figure draws the four arrows of the square, `ℤ/12 → ℤ/6`, `ℤ/12 → ℤ/4`, `ℤ/6 → ℤ/2`,
`ℤ/4 → ℤ/2` (written out) with their labels; the reductions make the square commute and are
surjective, as their tips `↠` say. -/
theorem square_spec :
    reductionSquare.Faithful reductionSquare.layout square ∧
    square.arrows = [(0, 0, 1), (1, 0, 2), (2, 1, 3), (3, 2, 3)] ∧
    square.arrowTexts = [(0, "π₆"), (1, "π₄"), (2, "π₂"), (3, "π₂")] ∧
    reductionMaps.Commutes reductionSquare = true ∧
    reductionMaps.StylesHold reductionSquare = true := by
  exact ⟨reductionSquare.builder_faithful (by decide +kernel), by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

figure_links square square_spec

/-! ### A short exact sequence of finite abelian groups -/

/-- `0 → ℤ/2 ↣ ℤ/4 ↠ ℤ/2 → 0`, doubling then reducing. -/
def exactSequence : CommDiagram where
  objects := #["0", "ℤ/2", "ℤ/4", "ℤ/2", "0"]
  pos := #[(0, 0), (1, 0), (2, 0), (3, 0), (4, 0)]
  arrows := [{ src := 0, tgt := 1 }, { src := 1, tgt := 2, label := "·2", style := .mono },
    { src := 2, tgt := 3, label := "π₂", style := .epi }, { src := 3, tgt := 4 }]

/-- The maps: `0 ↦ 0`, doubling, reduction, everything to `0`. -/
def exactMaps : FinMaps where
  card := #[1, 2, 4, 2, 1]
  fn := #[#[0], #[0, 2], reduction 4 2, #[0, 0]]

/-- The image of each map is the kernel of the next: on these tables, the elements sent to `0`
by arrow `k + 1` are exactly the values of arrow `k`. -/
def exactAt (R : FinMaps) (k : Nat) : Bool :=
  let f := R.fn.getD k #[]
  let g := R.fn.getD (k + 1) #[]
  (List.range g.size).all fun y => (g.getD y 0 == 0) == f.contains y

/-- The short exact sequence. -/
@[figure]
def exact : Diagram :=
  { exactSequence.figure with title := "A short exact sequence 0 → ℤ/2 → ℤ/4 → ℤ/2 → 0" }

/-- The figure draws `0 → ℤ/2 ↣ ℤ/4 ↠ ℤ/2 → 0`, left to right (written out); doubling is
injective and the reduction surjective, as their marks say, and the image of each map is the
kernel of the next. -/
theorem exact_spec :
    exactSequence.Faithful exactSequence.layout exact ∧
    exact.arrows = [(0, 0, 1), (1, 1, 2), (2, 2, 3), (3, 3, 4)] ∧
    exact.arrowTexts = [(1, "·2"), (2, "π₂")] ∧
    exactMaps.WellTyped exactSequence = true ∧ exactMaps.StylesHold exactSequence = true ∧
    (exactAt exactMaps 0 && exactAt exactMaps 1 && exactAt exactMaps 2) = true := by
  exact ⟨exactSequence.builder_faithful (by decide +kernel), by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

figure_links exact exact_spec

/-! ### A cube of reductions -/

/-- The divisors of 30 that are the vertices of the cube: `30, 15, 10, 6, 5, 3, 2, 1`. -/
def cubeMods : Array Nat := #[30, 15, 10, 6, 5, 3, 2, 1]

/-- The cube of the reductions `ℤ/m → ℤ/(m / p)` among the quotients of `ℤ/30`: the front face
`ℤ/30, ℤ/15, ℤ/10, ℤ/5` and the back face `ℤ/6, ℤ/3, ℤ/2, ℤ/1`, drawn in oblique projection; the
claims are the six faces. -/
def reductionCube : CommDiagram where
  objects := cubeMods.map fun m => s!"ℤ/{m}"
  pos := #[(0, 0), (2, 0), (0, -2), (1, 1), (2, -2), (3, 1), (1, -1), (3, -1)].map
    fun (x, y) => (x * 3 / 4, y * 3 / 4)
  arrows := [{ src := 0, tgt := 1 }, { src := 0, tgt := 2 }, { src := 1, tgt := 4 },
    { src := 2, tgt := 4 }, { src := 0, tgt := 3 }, { src := 1, tgt := 5 },
    { src := 2, tgt := 6 }, { src := 4, tgt := 7 }, { src := 3, tgt := 5 },
    { src := 3, tgt := 6 }, { src := 5, tgt := 7 }, { src := 6, tgt := 7 }]
  paths := [(0, [0, 2], [1, 3]), (3, [8, 10], [9, 11]), (0, [0, 5], [4, 8]),
    (2, [3, 7], [6, 11]), (0, [1, 6], [4, 9]), (1, [2, 7], [5, 10])]

/-- The maps of the cube: reductions. -/
def cubeMaps : FinMaps where
  card := cubeMods
  fn := reductionCube.arrows.toArray.map fun a =>
    reduction (cubeMods.getD a.src 1) (cubeMods.getD a.tgt 1)

/-- The cube of reductions. -/
@[figure]
def cube : Diagram :=
  { reductionCube.figure with title := "A cube of reductions of ℤ/30", width := 420 }

/-- The figure draws the twelve edges of the cube (written out), and the reductions make all six
faces commute. -/
theorem cube_spec :
    reductionCube.Faithful reductionCube.layout cube ∧
    cube.arrows = [(0, 0, 1), (1, 0, 2), (2, 1, 4), (3, 2, 4), (4, 0, 3), (5, 1, 5), (6, 2, 6),
      (7, 4, 7), (8, 3, 5), (9, 3, 6), (10, 5, 7), (11, 6, 7)] ∧
    cubeMaps.Commutes reductionCube = true := by
  refine ⟨?_, by decide +kernel, by decide +kernel⟩
  have h := reductionCube.builder_faithful (by decide +kernel)
  exact h

figure_links cube cube_spec

/-! ### Parallel arrows and a 2-cell -/

/-- Two parallel functors `F, G : C ⇉ D`, a natural transformation `α : F ⇒ G` between them,
an inclusion `J : D ↪ E`, and an endofunctor `T` of `E`. -/
def functors : CommDiagram where
  objects := #["C", "D", "E"]
  pos := #[(0, 0), (3 / 2, 0), (3 / 2, -1)]
  arrows := [{ src := 0, tgt := 1, label := "F", bend := 2 },
    { src := 0, tgt := 1, label := "G", bend := -2, swap := true },
    { src := 1, tgt := 2, label := "J", style := .inclusion },
    { src := 2, tgt := 2, label := "T", bend := -1 }]
  twoCells := [{ src := 0, tgt := 1, label := "α" }]

/-- The functors and the transformation. -/
@[figure]
def twoCell : Diagram :=
  { functors.figure with title := "A natural transformation α : F ⇒ G" }

/-- The figure draws the arrows `F`, `G : C → D`, `J : D → E` and the loop `T` at `E` with their
labels, and one 2-cell (written out). -/
theorem twoCell_spec :
    functors.Faithful functors.layout twoCell ∧
    twoCell.arrows = [(0, 0, 1), (1, 0, 1), (2, 1, 2), (3, 2, 2)] ∧
    twoCell.arrowTexts = [(0, "F"), (1, "G"), (2, "J"), (3, "T")] ∧
    (twoCell.marksWhere Part.isTwoCell).length = 3 := by
  exact ⟨functors.builder_faithful (by decide +kernel), by decide +kernel, by decide +kernel,
    by decide +kernel⟩

figure_links twoCell twoCell_spec

/-! ### The symmetric group on three letters -/

/-- The permutations of `{0, 1, 2}` in one-line notation: the identity, the transpositions
`(0 1)`, `(1 2)`, `(0 2)`, the cycles `(0 1 2)`, `(0 2 1)`. -/
def perms3 : Array (Array Nat) :=
  #[#[0, 1, 2], #[1, 0, 2], #[0, 2, 1], #[2, 1, 0], #[1, 2, 0], #[2, 0, 1]]

/-- The composite `σ ∘ τ` (first `τ`, then `σ`) of the permutations numbered `σ` and `τ`, as a
number. -/
def compose3 (σ τ : Nat) : Nat :=
  let p := (perms3.getD σ #[]).toList
  let q := (perms3.getD τ #[]).toList
  let r := (List.range 3).map fun x => p.getD (q.getD x 0) 0
  (perms3.toList.findIdx? (·.toList == r)).getD 0

/-- `S₃` as a table: element `a * b` is the composite `a ∘ b`. -/
def s3 : FinMagma where
  n := 6
  mul a b := ⟨compose3 a b % 6, Nat.mod_lt _ (by decide +kernel)⟩
  names := #["e", "(1 2)", "(2 3)", "(1 3)", "(1 2 3)", "(1 3 2)"]

/-- The Cayley table of `S₃`. -/
@[figure]
def cayleyTable : Diagram :=
  { s3.tableFigure with title := "The Cayley table of S₃" }

/-- The figure writes in cell `(a, b)` the name of `a ∘ b`, row by row (written out for the first
row and the first column), the table is a group and is not commutative, and its centre is the
identity alone. -/
theorem cayleyTable_spec :
    s3.FaithfulTable cayleyTable ∧ s3.isGroup = true ∧ s3.isCommutative = false ∧
    s3.centre = [0] ∧
    (cayleyTable.entries.take 6).map (·.2) = ["e", "(1 2)", "(2 3)", "(1 3)", "(1 2 3)", "(1 3 2)"]
    ∧ (cayleyTable.entries.filter (·.1.2 == 1)).map (·.2) =
      ["(1 2)", "e", "(1 3 2)", "(1 2 3)", "(1 3)", "(2 3)"] := by
  exact ⟨s3.tableFigure_faithful (by decide +kernel), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

figure_links cayleyTable cayleyTable_spec

/-- The positions of the Cayley graph of `S₃` for `(1 2)` and `(1 2 3)`: the two cosets of the
rotations on two concentric triangles. -/
def s3Positions : Array QPoint :=
  let outer := FinMagma.circlePositions 3 (6 / 5)
  let inner := FinMagma.circlePositions 3 (9 / 20)
  #[outer.getD 0 (0, 0), inner.getD 0 (0, 0), inner.getD 2 (0, 0), inner.getD 1 (0, 0),
    outer.getD 1 (0, 0), outer.getD 2 (0, 0)]

/-- The Cayley graph of `S₃` for the generators `(1 2)` and `(1 2 3)`. -/
@[figure]
def cayleyGraph : Diagram :=
  { s3.cayleyFigure [⟨1, by decide +kernel⟩, ⟨4, by decide +kernel⟩] s3Positions with
    title := "The Cayley graph of S₃ for (1 2) and (1 2 3)", width := 320 }

/-- The figure draws, in the colour of `(1 2)`, a line joining `g` and `g ∘ (1 2)` for each pair,
and in the colour of `(1 2 3)` an arrow `g → g ∘ (1 2 3)` for each `g` (written out). -/
theorem cayleyGraph_spec :
    (s3.cayley [⟨1, by decide +kernel⟩, ⟨4, by decide +kernel⟩] s3Positions).Faithful
      (s3.cayley [⟨1, by decide +kernel⟩, ⟨4, by decide +kernel⟩] s3Positions).layout cayleyGraph ∧
    cayleyGraph.arrows = [(0, 0, 1), (1, 2, 5), (2, 3, 4), (3, 0, 4), (4, 1, 2), (5, 2, 3),
      (6, 3, 1), (7, 4, 5), (8, 5, 0)] := by
  have e : cayleyGraph.arrows = (s3.cayley [⟨1, by decide⟩, ⟨4, by decide⟩] s3Positions).figure.arrows := by
    unfold cayleyGraph FinMagma.cayleyFigure
    rw [Diagram.capped_of (by decide +kernel)]
    rfl
  have h := CommDiagram.builder_faithful (s3.cayley [⟨1, by decide⟩, ⟨4, by decide⟩] s3Positions)
    (by decide +kernel)
  refine ⟨?_, ?_⟩
  · unfold cayleyGraph FinMagma.cayleyFigure
    rw [Diagram.capped_of (by decide +kernel)]
    exact h
  · rw [e, h.1]
    decide +kernel

figure_links cayleyGraph cayleyGraph_spec

/-! ### A quiver with a dimension vector -/

/-- A quiver with a double arrow, a loop and a cycle, and the dimension vector `(2, 3, 1)`. -/
def quiverData : FinQuiver where
  vertices := #["1", "2", "3"]
  pos := #[(0, 0), (3 / 2, 0), (3 / 4, -1)]
  arrows := [(0, 1, "a"), (0, 1, "b"), (1, 2, "c"), (2, 0, "d"), (2, 2, "ℓ")]
  dims := #[2, 3, 1]

/-- The quiver with its dimension vector. -/
@[figure]
def quiver : Diagram := { quiverData.figure with title := "A quiver with dimension vector (2, 3, 1)" }

/-- The figure draws the five arrows of the quiver with their names and writes the dimension at
each vertex (written out). -/
theorem quiver_spec :
    quiverData.Faithful quiverData.layout quiver ∧
    quiver.arrows = [(0, 0, 1), (1, 0, 1), (2, 1, 2), (3, 2, 0), (4, 2, 2)] ∧
    quiver.arrowTexts = [(0, "a"), (1, "b"), (2, "c"), (3, "d"), (4, "ℓ")] ∧
    (quiver.marksWhere Part.isVertex).map (·.shape) = [.text "2" (0, 0) .center,
      .text "3" (3 / 2, 0) .center, .text "1" (3 / 4, -1) .center] := by
  exact ⟨quiverData.builder_faithful (by decide +kernel), by decide +kernel, by decide +kernel,
    by decide +kernel⟩

figure_links quiver quiver_spec

/-! ### The gallery -/

/-- The figures by file stem. -/
def figures : Array (String × Diagram) :=
  #[("diagram-square", square), ("diagram-exact", exact), ("diagram-reduction-cube", cube),
    ("diagram-two-cell", twoCell), ("diagram-cayley-table", cayleyTable),
    ("diagram-cayley-graph", cayleyGraph), ("diagram-quiver", quiver)]

/-- The gallery's files: each figure as a plane figure, light and dark. -/
def gallery : Array (String × Plane.Figure) :=
  figures.map (fun (n, d) => (n ++ ".svg", d.toPlane)) ++
    figures.map (fun (n, d) => (n ++ "-dark.svg", d.dark.toPlane))

/-! ### Checks -/

/-- The position of the `k`-th mark (from 0) whose part satisfies `p`. -/
def posWhere (d : Diagram) (p : Part → Bool) (k : Nat := 0) : Nat :=
  ((d.marks.zipIdx.filter fun (m, _) => p m.part).map (·.2)).getD k 0

/-- Each predicate holds of its figure and refuses planted faults in every class of mark. -/
def faultChecks : Array (String × Bool) :=
  let D := reductionSquare
  let L := D.layout
  let ok := fun (d : Diagram) => decide (D.Faithful L d)
  let isA := fun (k : Nat) (p : Part) => match p with | .arrow k' _ _ => k == k' | _ => false
  let body := posOf square (.arrow 0 0 1)
  let F := functors
  let FL := F.layout
  let tc := posWhere twoCell Part.isTwoCell
  let c0 := posOf cayleyTable (.cell 0 1)
  let e0 := posOf cayleyTable (.entry 1 1)
  let h0 := posOf cayleyTable (.header 1 2)
  #[("square: faithful", ok square),
    ("square: an arrow dropped is refused", !ok (dropMark square body)),
    ("square: an arrow's tip dropped is refused", !ok (dropMark square (body + 1))),
    ("square: an arrow's second tip (epi) dropped is refused", !ok (dropMark square (body + 2))),
    ("square: an arrow drawn to the wrong object is refused", !ok (changeMark square body fun m =>
      { m with part := .arrow 0 0 3 })),
    ("square: an arrow's body moved is refused", !ok (changeMark square body fun m =>
      { m with shape := .path [(0, 0), (1, 0)] .solid })),
    ("square: an arrow's body dashed is refused", !ok (changeMark square body fun m =>
      match m.shape with
      | .path ps _ => { m with shape := .path ps .dashed }
      | _ => m)),
    ("square: an arrow's colour changed is refused", !ok (changeMark square body fun m =>
      { m with ink := .accent 0 })),
    ("square: a label changed is refused", !ok (changeMark square (posWhere square (isA 0)
      2 + 1) fun m => match m.shape with
        | .text _ p sd => { m with shape := .text "π₃" p sd }
        | _ => m)),
    ("square: a label moved to the other side is refused", !ok (changeMark square
      (posWhere square (isA 0) 3) fun m => match m.shape with
        | .text s p _ => { m with shape := .text s p .below }
        | _ => m)),
    ("square: an extra arrow (the diagonal) is refused", !ok (addMark square
      { part := .arrow 4 0 3, shape := .path [(0, 0), (1, -1)] .solid })),
    ("square: an extra tip under an arrow's part is refused", !ok (addMark square
      { part := .arrow 0 0 1, shape := .arrow (0, 0) (1, 0) })),
    ("square: an object renamed is refused", !ok (changeMark square (posOf square (.vertex 1))
      fun m => { m with shape := .text "ℤ/3" (1, 0) .center })),
    ("square: an object moved is refused", !ok (changeMark square (posOf square (.vertex 1))
      fun m => { m with shape := .text "ℤ/6" (2, 0) .center })),
    ("square: a guide line is refused", !ok (addMark square
      { part := .guide, shape := .segment (0, 0) (1, -1) })),
    ("square: a dot under an object's part is refused", !ok (addMark square
      { part := .vertex 0, shape := .dot (0, 0) })),
    ("square: maps that do not commute are refused by Commutes", !(FinMaps.Commutes
      { reductionMaps with fn := #[reduction 12 6, reduction 12 4, reduction 6 2,
        #[0, 0, 1, 1]] } reductionSquare)),
    ("square: a map that does not fit its arrow is refused by WellTyped", !(FinMaps.WellTyped
      { reductionMaps with fn := #[reduction 12 6, reduction 12 4, reduction 6 2,
        #[0, 1, 2, 3]] } reductionSquare)),
    ("exact: a non-injective map drawn as a monomorphism is refused by StylesHold",
      !(FinMaps.StylesHold { exactMaps with fn := #[#[0], #[0, 0], reduction 4 2, #[0, 0]] }
        exactSequence)),
    ("exact: a non-surjective map drawn as an epimorphism is refused by StylesHold",
      !(FinMaps.StylesHold { exactMaps with fn := #[#[0], #[0, 2], #[0, 0, 0, 0], #[0, 0]] }
        exactSequence)),
    ("exact: the doubling replaced by zero is not exact at ℤ/4",
      !exactAt { exactMaps with fn := #[#[0], #[0, 0], reduction 4 2, #[0, 0]] } 1),
    ("exact: faithful", decide (exactSequence.Faithful exactSequence.layout exact)),
    ("exact: the hook drawn instead of the tail tip is refused", !decide (exactSequence.Faithful
      exactSequence.layout (changeMark exact (posWhere exact (isA 1) 2) fun m =>
        { m with shape := .polyline [(1, 0), (1, 1 / 10)] }))),
    ("two-cell: faithful", decide (F.Faithful FL twoCell)),
    ("two-cell: the 2-cell dropped is refused", !decide (F.Faithful FL (dropMark twoCell tc))),
    ("two-cell: the 2-cell's label changed is refused", !decide (F.Faithful FL
      (changeMark twoCell (tc + 2) fun m => match m.shape with
        | .text _ p sd => { m with shape := .text "β" p sd }
        | _ => m))),
    ("two-cell: the loop's body moved is refused", !decide (F.Faithful FL
      (changeMark twoCell (posOf twoCell (.arrow 3 2 2)) fun m =>
        { m with shape := .path [(0, 0), (1, 1)] .solid }))),
    ("table: faithful", decide (s3.FaithfulTable cayleyTable)),
    ("table: a cell's colour changed is refused", !decide (s3.FaithfulTable
      (changeMark cayleyTable c0 fun m => { m with ink := .series 0 true }))),
    ("table: a cell dropped is refused", !decide (s3.FaithfulTable (dropMark cayleyTable c0))),
    ("table: an entry changed is refused", !decide (s3.FaithfulTable
      (changeMark cayleyTable e0 fun m => match m.shape with
        | .text _ p sd => { m with shape := .text "(1 2)" p sd }
        | _ => m))),
    ("table: two entries swapped is refused", !decide (s3.FaithfulTable
      (changeMark (changeMark cayleyTable e0 fun m => { m with part := .entry 1 2 })
        (e0 + 1) fun m => { m with part := .entry 1 1 }))),
    ("table: a heading changed is refused", !decide (s3.FaithfulTable
      (changeMark cayleyTable h0 fun m => match m.shape with
        | .text _ p sd => { m with shape := .text "e" p sd }
        | _ => m))),
    ("table: a rule dropped is refused", !decide (s3.FaithfulTable
      (dropMark cayleyTable (posOf cayleyTable .guide)))),
    ("table: a rule drawn in an accent colour is refused", !decide (s3.FaithfulTable
      (changeMark cayleyTable (posOf cayleyTable .guide) fun m => { m with ink := .accent 0 }))),
    ("table: an extra guide is refused", !decide (s3.FaithfulTable
      (addMark cayleyTable { part := .guide, shape := .segment (1, -1) (7, -7) }))),
    ("table: a table that is not associative is not a group",
      !(FinMagma.isGroup { n := 3, mul := fun a b => ⟨(a.val + 2 * b.val) % 3,
        Nat.mod_lt _ (by decide +kernel)⟩ })),
    ("table: a table without inverses is not a group",
      !(FinMagma.isGroup { n := 2, mul := fun a b => ⟨a.val * b.val % 2, Nat.mod_lt _ (by decide)⟩ })),
    ("cayley: faithful", let C := s3.cayley [⟨1, by decide +kernel⟩, ⟨4, by decide +kernel⟩] s3Positions
      decide (C.Faithful C.layout cayleyGraph)),
    ("cayley: an edge in the other generator's colour is refused",
      let C := s3.cayley [⟨1, by decide +kernel⟩, ⟨4, by decide +kernel⟩] s3Positions
      !decide (C.Faithful C.layout (changeMark cayleyGraph 0 fun m =>
        { m with ink := .series 1 false }))),
    ("quiver: faithful", decide (quiverData.Faithful quiverData.layout quiver)),
    ("quiver: one of the double arrows dropped is refused", !decide (quiverData.Faithful
      quiverData.layout (dropMark quiver (posOf quiver (.arrow 1 0 1))))),
    ("quiver: a dimension changed is refused", !decide (quiverData.Faithful quiverData.layout
      (changeMark quiver (posOf quiver (.vertex 0)) fun m =>
        { m with shape := .text "3" (0, 0) .center })))]

/-- The layouts have the properties they are drawn for. -/
def layoutChecks : Array (String × Bool) :=
  let bodies := fun (d : Diagram) => d.marks.filterMap fun m => match m.shape with
    | .path ps _ => some ps
    | _ => none
  let L := reductionSquare.layout
  #[("arrows: every body of the square starts and ends outside the boxes of its objects",
      reductionSquare.arrows.zipIdx.all fun (a, k) =>
        let ps := CommDiagram.arrowPoints L k a
        outsideBox (L.pos a.src) (L.half a.src) 0 (ps.headD (0, 0)) &&
          outsideBox (L.pos a.tgt) (L.half a.tgt) 0 (ps.getLastD (0, 0))),
    ("arrows: the two parallel arrows of the quiver are 1/8 apart",
      let L := quiverData.layout
      let p := CommDiagram.arrowPoints L 0 { src := 0, tgt := 1 }
      let q := CommDiagram.arrowPoints L 1 { src := 0, tgt := 1 }
      L.shift 0 == 1 / 16 && L.shift 1 == -1 / 16 &&
        (p.headD (0, 0)).2 - (q.headD (0, 0)).2 == 1 / 8),
    ("arrows: an exact sequence runs left to right",
      (bodies exact).all fun ps => (ps.headD (0, 0)).1 < (ps.getLastD (0, 0)).1),
    ("table: the cells tile the table, row i below row i - 1",
      (FinMagma.cellPairs 6).all fun (i, j) =>
        let (lo, hi) := FinMagma.tableBox i j
        hi.1 - lo.1 == 1 && hi.2 - lo.2 == 1 && lo.1 == j + 1 && hi.2 == -((i : Rat) + 1))]

/-- A diagram of 100000 loops at one object. -/
def manyArrows : CommDiagram :=
  { objects := #["A"], pos := #[(0, 0)], arrows := List.replicate 100000 { src := 0, tgt := 0 } }

/-- A diagram with an arrow to an object it does not have. -/
def danglingArrow : CommDiagram :=
  { objects := #["A"], pos := #[(0, 0)], arrows := [{ src := 0, tgt := 5 }] }

/-- A diagram without a position for its second object. -/
def missingPosition : CommDiagram := { objects := #["A", "B"], pos := #[(0, 0)], arrows := [] }

/-- Hostile data is refused within the caps, before any work that grows with it. -/
def boundChecks : Array (String × Bool) :=
  let note := fun (d : Diagram) => d.marks.length == 1 && d.arrows.isEmpty && d.cells.isEmpty
  #[("bounds: a diagram with 100000 arrows is a note", note manyArrows.figure),
    ("bounds: a diagram with an arrow to a missing object is a note", note danglingArrow.figure),
    ("bounds: a diagram without a position for every object is a note",
      note missingPosition.figure),
    ("bounds: a table of a million elements is a note",
      note (FinMagma.tableFigure { n := 1000000, mul := fun a _ => a })),
    ("bounds: a Cayley graph of a million elements is a note",
      note (FinMagma.cayleyFigure { n := 1000000, mul := fun a _ => a } [] #[]))]

/-- The figures pass the layout checks of plane figures in both themes. -/
def planeChecks : Array (String × Bool) :=
  gallery.map fun (n, f) => (s!"layout checks: {n} has no problems ({f.checkMessages})",
    f.checkMessages.isEmpty)

/-- Every check of this module. -/
def checks : Array (String × Bool) := faultChecks ++ layoutChecks ++ boundChecks ++ planeChecks

end PILeanTest.AlgebraDiagrams
