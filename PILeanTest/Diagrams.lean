/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Trust.Attr

/-!
# The gallery of combinatorial diagrams, their specifications and their checks

One figure for each kind of `PILean.Diagram`, each with the attribute `figure` and a
specification linked by `figure_proves`: the figure is the builder applied to its data, and what
it draws, read back from its marks (`Diagram.edges`, `cells`, `entries`, `strands`, `steps`,
`members`), is written out in full and checked by the kernel. Changing the data of a figure
breaks its specification (`PILeanTest.SpecMutations` compiles such changes).

`checks` holds what the theorems do not: each kind's `Faithful` predicate refuses diagrams with a
planted fault (a mark dropped, added, moved or changed), the figures pass the plane figures'
layout checks in both themes, the exact layouts have the properties they are drawn for (Hasse
edges go up, the tidy layout keeps siblings apart, circle points are on the circle), and hostile
data is refused within the caps.

`gallery` lists the figures by file name, light and dark, for `pilean-gallery` and the goldens of
`lake test`.
-/

namespace PILeanTest.Diagrams

open PILean PILean.Diagram

/-! ### Graphs: the Petersen graph -/

/-- The 2-subsets of `{0, …, 4}` in lexicographic order: the vertices of the Kneser graph
`K(5, 2)`, which is the Petersen graph. -/
def pairs5 : List (Nat × Nat) :=
  (List.range 5).flatMap fun a => ((List.range 5).filter (a < ·)).map fun b => (a, b)

/-- The Petersen graph as the Kneser graph `K(5, 2)`: two 2-subsets are adjacent when they are
disjoint. -/
def petersenGraph : FinGraph where
  n := 10
  adj i j :=
    let (a, b) := pairs5.getD i.val (0, 0)
    let (c, d) := pairs5.getD j.val (0, 0)
    a != c && a != d && b != c && b != d
  names := (pairs5.map fun (a, b) => s!"{a}{b}").toArray

/-- The drawing's positions: the outer 5-cycle `01, 23, 04, 12, 34` on the unit circle and each
one's neighbour among the others (`24, 14, 13, 03, 02`) at half the radius, at the same angle. -/
def petersenLayout : Layout :=
  let outer := [0, 7, 3, 4, 9]
  let inner := [8, 6, 5, 2, 1]
  let at_ := fun (r : Rat) (k : Nat) =>
    let p := (Layout.circular 5).pos k
    (r * p.1, r * p.2)
  Layout.given ((List.range 10).map fun v =>
    match outer.idxOf? v, inner.idxOf? v with
    | some k, _ => at_ 1 k
    | none, some k => at_ (1 / 2) k
    | none, none => (0, 0)).toArray

/-- The Petersen graph, drawn as a pentagon around a pentagram. -/
@[figure]
def petersen : Diagram :=
  { petersenGraph.draw petersenLayout with
    title := "The Petersen graph, the Kneser graph K(5, 2)", width := 340 }

/-- The figure draws the Petersen graph: its vertices are the ten 2-subsets of `{0, …, 4}`, its
edges exactly the fifteen pairs of disjoint ones (written out), each vertex's dot and name at
the layout's position (`FinGraph.Faithful`). -/
theorem petersen_spec :
    petersenGraph.Faithful petersenLayout petersen ∧
    petersen.edges = [(0, 7), (0, 8), (0, 9), (1, 5), (1, 6), (1, 9), (2, 4), (2, 6), (2, 8),
      (3, 4), (3, 5), (3, 7), (4, 9), (5, 8), (6, 7)] := by
  exact ⟨petersenGraph.draw_faithful _, by decide +kernel⟩

figure_proves petersen petersen_spec

/-! ### Hasse diagrams: the Boolean lattice of a 3-set -/

/-- The subsets of `{1, 2, 3}` as bit masks `0, …, 7`, ordered by inclusion. -/
def booleanLattice : FinPoset where
  n := 8
  le i j := i.val &&& j.val == i.val
  names := #["∅", "{1}", "{2}", "{1,2}", "{3}", "{1,3}", "{2,3}", "{1,2,3}"]

/-- The Hasse diagram of the subsets of `{1, 2, 3}`: a cube. -/
@[figure]
def cube : Diagram := { booleanLattice.figure with title := "Subsets of {1, 2, 3}", width := 300 }

/-- The figure draws exactly the twelve covers of the Boolean lattice (adding one element),
written out; inclusion is a partial order, so its strict order is the transitive closure of
those edges (`FinPoset.transGen_covers_iff`). -/
theorem cube_spec :
    booleanLattice.Faithful booleanLattice.layout cube ∧
    cube.edges = [(0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3), (2, 6), (3, 7), (4, 5), (4, 6),
      (5, 7), (6, 7)] ∧ booleanLattice.IsPartialOrder := by
  exact ⟨booleanLattice.builder_faithful (by decide), by decide +kernel,
    ⟨by decide, by decide, by decide⟩⟩

figure_proves cube cube_spec

/-! ### Young diagrams and tableaux -/

/-- The Young diagram of `(5, 3, 3, 1)`, English notation. -/
def shape5331 : YoungShape := { rows := [5, 3, 3, 1] }

/-- The Young diagram of the partition `(5, 3, 3, 1)` of 12. -/
@[figure]
def young : Diagram :=
  { shape5331.figure with title := "The Young diagram of (5, 3, 3, 1)", width := 220 }

/-- The figure draws exactly the twelve cells `(i, j)` with `j < λᵢ` for `λ = (5, 3, 3, 1)`, row
by row, each the unit square of English notation. -/
theorem young_spec :
    shape5331.Faithful young ∧
    young.cells = [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1),
      (2, 2), (3, 0)] := by
  exact ⟨shape5331.builder_faithful (by decide), by decide +kernel⟩

figure_proves young young_spec

/-- A semistandard tableau of shape `(4, 3, 1)` in French notation. -/
def ssyt : Tableau := { entries := [[1, 1, 2, 4], [2, 3, 4], [4]], convention := .french }

/-- A semistandard Young tableau, French notation. -/
@[figure]
def tableau : Diagram :=
  { ssyt.figure with
    title := "A semistandard tableau of shape (4, 3, 1), French notation", width := 200 }

/-- The figure draws the cells of `(4, 3, 1)` and writes the filling, written out, in French
notation; the filling is semistandard. -/
theorem tableau_spec :
    ssyt.Faithful tableau ∧ ssyt.IsSemistandard ∧
    tableau.entries = [((0, 0), "1"), ((0, 1), "1"), ((0, 2), "2"), ((0, 3), "4"), ((1, 0), "2"),
      ((1, 1), "3"), ((1, 2), "4"), ((2, 0), "4")] := by
  exact ⟨ssyt.builder_faithful (by decide), by decide, by decide +kernel⟩

figure_proves tableau tableau_spec

/-! ### Permutations -/

/-- The permutation `4 2 5 1 3` in one-line notation (values from 1). -/
def perm : FinPerm := { values := [3, 1, 4, 0, 2] }

/-- The permutation in two-line notation. -/
@[figure]
def permTwoLine : Diagram :=
  { perm.figure FinPerm.twoLine with title := "The permutation 42513 in two-line notation" }

/-- The figure writes the arguments `1, …, 5` above their values `4 2 5 1 3`. -/
theorem permTwoLine_spec :
    perm.FaithfulTwoLine permTwoLine ∧ perm.IsPerm ∧
    permTwoLine.entries = [((0, 0), "1"), ((0, 1), "2"), ((0, 2), "3"), ((0, 3), "4"),
      ((0, 4), "5"), ((1, 0), "4"), ((1, 1), "2"), ((1, 2), "5"), ((1, 3), "1"), ((1, 4), "3")] := by
  exact ⟨perm.twoLine_faithful, by decide, by decide +kernel⟩

figure_proves permTwoLine permTwoLine_spec

/-- The permutation matrix. -/
@[figure]
def permMatrix : Diagram :=
  { perm.figure FinPerm.matrix with title := "The permutation matrix of 42513", width := 200 }

/-- The figure marks exactly the cells `(i, σ i)`: `(0, 3), (1, 1), (2, 4), (3, 0), (4, 2)`. -/
theorem permMatrix_spec :
    perm.FaithfulMatrix permMatrix ∧
    permMatrix.cells = [(0, 3), (1, 1), (2, 4), (3, 0), (4, 2)] := by
  exact ⟨perm.matrix_faithful, by decide +kernel⟩

figure_proves permMatrix permMatrix_spec

/-- The cycle diagram. -/
@[figure]
def permCycles : Diagram :=
  { perm.figure FinPerm.cycles with title := "The cycles of 42513: (1 4)(2)(3 5)", width := 260 }

/-- The figure draws exactly the arrows `i → σ i`, written out (the fixed point `1 ↦ 1` as a
loop). -/
theorem permCycles_spec :
    perm.FaithfulCycles permCycles ∧
    permCycles.edges = [(0, 3), (1, 1), (2, 4), (3, 0), (4, 2)] := by
  exact ⟨perm.cycles_faithful, by decide +kernel⟩

figure_proves permCycles permCycles_spec

/-- The wiring diagram. -/
@[figure]
def permWiring : Diagram :=
  { perm.figure FinPerm.wiring with title := "The wiring diagram of 42513: six inversions" }

/-- The figure draws the five strands, and the pairs of strands that cross are exactly the six
inversions of `42513`, written out. -/
theorem permWiring_spec :
    perm.FaithfulWiring permWiring ∧
    crossingPairs permWiring.strands = [(0, 1), (0, 3), (0, 4), (1, 3), (2, 3), (2, 4)] := by
  refine ⟨perm.wiring_faithful, ?_⟩
  rw [show permWiring.strands = perm.wiring.strands from rfl, perm.wiring_crossings]
  decide

figure_proves permWiring permWiring_spec

/-! ### Trees -/

/-- A rooted tree on twelve vertices: the parent of each. -/
def treeParents : List (Option Nat) :=
  [none, some 0, some 0, some 0, some 1, some 1, some 2, some 3, some 3, some 3, some 7, some 7]

/-- The tree as a forest. -/
def rooted : Forest := ⟨12, fun c => treeParents.getD c none, #[]⟩

/-- A rooted tree in the tidy layout. -/
@[figure]
def tree : Diagram := { rooted.figure with title := "A rooted tree, tidy layout" }

/-- The figure draws exactly the eleven parent links `(parent c, c)`, written out. -/
theorem tree_spec :
    rooted.Faithful rooted.layout tree ∧ rooted.IsForest ∧
    tree.edges = [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6), (3, 7), (3, 8), (3, 9), (7, 10),
      (7, 11)] := by
  exact ⟨rooted.builder_faithful (by decide), by decide, by decide +kernel⟩

figure_proves tree tree_spec

/-- The binary search tree of the keys `5, 3, 8, 1, 4, 7, 9, 2, 6` inserted in that order:
vertex `k` holds key `k + 1`. -/
def bst : BinTree where
  n := 9
  left := fun v => match v with | 4 => some 2 | 2 => some 0 | 7 => some 6 | 6 => some 5 | _ => none
  right := fun v => match v with | 4 => some 7 | 2 => some 3 | 0 => some 1 | 7 => some 8 | _ => none
  names := #["1", "2", "3", "4", "5", "6", "7", "8", "9"]

/-- A binary search tree. -/
@[figure]
def binaryTree : Diagram :=
  { bst.figure with title := "A binary search tree of 1, …, 9", width := 320 }

/-- The figure draws exactly the eight parent links of the binary search tree, written out. -/
theorem binaryTree_spec :
    bst.toForest.Faithful bst.layout binaryTree ∧
    binaryTree.edges = [(0, 1), (2, 0), (2, 3), (4, 2), (4, 7), (6, 5), (7, 6), (7, 8)] := by
  exact ⟨bst.builder_faithful (by decide), by decide +kernel⟩

figure_proves binaryTree binaryTree_spec

/-! ### Set systems -/

/-- The numbers `1, …, 12` and their multiples of 2, 3 and 5 (element `x` is the number
`x + 1`). -/
def multiples : SetSystem where
  n := 12
  sets := [2, 3, 5].map fun m => (List.range 12).filter fun x => (x + 1) % m == 0
  names := ((List.range 12).map fun x => toString (x + 1)).toArray
  setNames := #["2ℤ", "3ℤ", "5ℤ"]

/-- A Venn diagram of the multiples of 2, 3 and 5 up to 12. -/
@[figure]
def venn : Diagram :=
  { multiples.vennFigure with title := "Multiples of 2, 3 and 5 up to 12" }

/-- The figure writes each number in the region of the sets that contain it (written out as
`(element, region)`), and every number is written inside the circle of each set exactly when it
belongs to it (`SetSystem.venn_inside`). -/
theorem venn_spec :
    multiples.FaithfulVenn venn ∧
    venn.members.map (fun (x, k, _) => (x, k)) = [(0, 0), (1, 1), (2, 2), (3, 1), (4, 4), (5, 3),
      (6, 0), (7, 1), (8, 2), (9, 5), (10, 0), (11, 3)] ∧
    ∀ x k p, (x, k, p) ∈ venn.members → ∀ s < 3,
      inside ((vennCentres 3).getD s (0, 0)) p = multiples.mem x s := by
  have hl : multiples.sets.length = 3 := by decide
  refine ⟨multiples.venn_faithful, by decide +kernel, fun x k p hx s hs => ?_⟩
  have := multiples.venn_inside (by decide) (by decide) hx (s := s) (by omega)
  rwa [hl] at this

figure_proves venn venn_spec

/-- The Fano plane: the points `0, …, 6` and its seven lines. -/
def fanoPlane : SetSystem where
  n := 7
  sets := [[0, 1, 2], [0, 3, 4], [0, 5, 6], [1, 3, 5], [1, 4, 6], [2, 3, 6], [2, 4, 5]]
  names := #["1", "2", "3", "4", "5", "6", "7"]
  setNames := #["L1", "L2", "L3", "L4", "L5", "L6", "L7"]

/-- The incidences of the Fano plane. -/
@[figure]
def fano : Diagram :=
  { fanoPlane.incidenceFigure with title := "Points and lines of the Fano plane" }

/-- The figure draws exactly the 21 incidences of the Fano plane, an edge from point `x` to line
`7 + s` for each `x ∈ s`. -/
theorem fano_spec :
    fano.edges = [(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13),
      (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9),
      (6, 11), (6, 12)] := by
  decide +kernel

figure_proves fano fano_spec

/-! ### Paths and boards -/

/-- The Dyck word `UUDUUDDDUD` (`true` for up). -/
def dyckWord : List Bool := [true, true, false, true, true, false, false, false, true, false]

/-- A Dyck path of semilength 5. -/
@[figure]
def dyck : Diagram :=
  { (LatticePath.ofDyck dyckWord).figure with title := "The Dyck path UUDUUDDDUD" }

/-- The figure draws the ten steps of the path of `UUDUUDDDUD`, each from point `k` to point
`k + 1` (written out); the word is a Dyck word. -/
theorem dyck_spec :
    (LatticePath.ofDyck dyckWord).Faithful dyck ∧ LatticePath.isDyck dyckWord = true ∧
    dyck.steps.map (fun (_, _, q) => q) = [(1, 1), (2, 2), (3, 1), (4, 2), (5, 3), (6, 2), (7, 1),
      (8, 0), (9, 1), (10, 0)] := by
  exact ⟨(LatticePath.ofDyck dyckWord).builder_faithful (by decide), by decide,
    by decide +kernel⟩

figure_proves dyck dyck_spec

/-- The Ferrers board of `(4, 3, 1)`. -/
def board : Polyomino := Polyomino.ferrers [4, 3, 1]

/-- A Ferrers board. -/
@[figure]
def ferrers : Diagram := { board.draw with title := "The Ferrers board of (4, 3, 1)", width := 200 }

/-- The figure draws exactly the eight cells of the board, written out. -/
theorem ferrers_spec :
    board.Faithful ferrers ∧
    ferrers.cells = [(0, 0), (1, 0), (2, 0), (3, 0), (0, 1), (1, 1), (2, 1), (0, 2)] := by
  exact ⟨board.draw_faithful, by decide +kernel⟩

figure_proves ferrers ferrers_spec

/-! ### The gallery -/

/-- The figures by file stem. -/
def figures : Array (String × Diagram) :=
  #[("diagram-petersen", petersen), ("diagram-cube", cube), ("diagram-young", young),
    ("diagram-tableau", tableau), ("diagram-perm-two-line", permTwoLine),
    ("diagram-perm-matrix", permMatrix), ("diagram-perm-cycles", permCycles),
    ("diagram-perm-wiring", permWiring), ("diagram-tree", tree), ("diagram-binary-tree", binaryTree),
    ("diagram-venn", venn), ("diagram-fano", fano), ("diagram-dyck", dyck),
    ("diagram-ferrers", ferrers)]

/-- The gallery's files: each figure as a plane figure, light and dark. -/
def gallery : Array (String × Plane.Figure) :=
  figures.map (fun (n, d) => (n ++ ".svg", d.toPlane)) ++
    figures.map (fun (n, d) => (n ++ "-dark.svg", d.dark.toPlane))

/-! ### Checks -/

/-- A diagram with one mark changed by `f` at position `k`. -/
def changeMark (d : Diagram) (k : Nat) (f : Mark → Mark) : Diagram :=
  { d with marks := d.marks.modify k f }

/-- The diagram without its mark at `k`. -/
def dropMark (d : Diagram) (k : Nat) : Diagram := { d with marks := d.marks.eraseIdx k }

/-- The diagram with a mark added at the end. -/
def addMark (d : Diagram) (m : Mark) : Diagram := { d with marks := d.marks ++ [m] }

/-- The diagram with its first two marks swapped. -/
def swapFirst (d : Diagram) : Diagram :=
  match d.marks with
  | a :: b :: rest => { d with marks := b :: a :: rest }
  | _ => d

/-- The position of the first mark of a part. -/
def posOf (d : Diagram) (p : Part) : Nat := (d.marks.findIdx? (·.part == p)).getD 0

/-- Each kind's predicate holds of its figure and refuses planted faults. -/
def faultChecks : Array (String × Bool) :=
  let pg := petersenGraph
  let pl := petersenLayout
  let e0 := posOf petersen (.edge 0 7)
  let v3 := posOf petersen (.vertex 3)
  let bl := booleanLattice
  let c0 := posOf young (.cell 0 0)
  let t0 := posOf tableau (.entry 0 0)
  let w0 := posOf permWiring (.strand 0)
  let m0 := posOf permMatrix (.cell 0 3)
  let x0 := posOf venn (.member 0 0)
  let s0 := posOf dyck (.step 0)
  #[("graph: the Petersen figure is faithful", decide (pg.Faithful pl petersen)),
    ("graph: a dropped edge is refused", !decide (pg.Faithful pl (dropMark petersen e0))),
    ("graph: an added edge is refused", !decide (pg.Faithful pl
      (addMark petersen { part := .edge 0 1, shape := .segment (pl.pos 0) (pl.pos 1) }))),
    ("graph: an edge drawn to the wrong point is refused", !decide (pg.Faithful pl
      (changeMark petersen e0 fun m => { m with shape := .segment (pl.pos 0) (pl.pos 1) }))),
    ("graph: a moved vertex is refused", !decide (pg.Faithful pl
      (changeMark petersen v3 fun m => { m with shape := .dot (5, 5) }))),
    ("graph: a renamed vertex is refused", !decide (pg.Faithful pl
      (changeMark petersen (posOf petersen (.vertex 3) + 10) fun m =>
        { m with shape := .text "xx" (pl.pos 3) .auto }))),
    ("graph: an edge relabelled as another is refused", !decide (pg.Faithful pl
      (changeMark petersen e0 fun m => { m with part := .edge 7 0 }))),
    ("hasse: the cube is faithful", decide (bl.Faithful bl.layout cube)),
    ("hasse: a non-cover drawn as an edge is refused", !decide (bl.Faithful bl.layout
      (addMark cube
        { part := .edge 0 7, shape := .segment (bl.layout.pos 0) (bl.layout.pos 7) }))),
    ("hasse: a dropped cover is refused",
      !decide (bl.Faithful bl.layout (dropMark cube (posOf cube (.edge 3 7))))),
    ("hasse: a cover drawn downwards is refused", !decide (bl.Faithful bl.layout
      (changeMark cube (posOf cube (.edge 0 1)) fun m => { m with part := .edge 1 0 }))),
    ("hasse: an element moved is refused", !decide (bl.Faithful bl.layout
      (changeMark cube (posOf cube (.vertex 7)) fun m => { m with shape := .dot (0, 0) }))),
    ("hasse: an element dropped is refused",
      !decide (bl.Faithful bl.layout (dropMark cube (posOf cube (.vertex 5))))),
    ("young: the diagram is faithful", decide (shape5331.Faithful young)),
    ("young: a dropped cell is refused", !decide (shape5331.Faithful (dropMark young c0))),
    ("young: an extra cell is refused", !decide (shape5331.Faithful (addMark young
      { part := .cell 3 1, shape := .rect (cellBox .english 3 1).1 (cellBox .english 3 1).2 }))),
    ("young: a cell in French position is refused", !decide (shape5331.Faithful
      (changeMark young c0 fun m =>
        { m with shape := .rect (cellBox .french 0 0).1 (cellBox .french 0 0).2 }))),
    ("young: a cell renamed is refused", !decide (shape5331.Faithful
      (changeMark young c0 fun m => { m with part := .cell 0 5 }))),
    ("young: two cells swapped is refused", !decide (shape5331.Faithful (swapFirst young))),
    ("tableau: faithful", decide (ssyt.Faithful tableau)),
    ("tableau: a changed entry is refused", !decide (ssyt.Faithful
      (changeMark tableau t0 fun m => { m with shape := .text "2" (cellCentre .french 0 0) .center }))),
    ("tableau: an entry in another cell's place is refused", !decide (ssyt.Faithful
      (changeMark tableau t0 fun m => { m with shape := .text "1" (cellCentre .french 1 0) .center }))),
    ("tableau: a dropped entry is refused", !decide (ssyt.Faithful (dropMark tableau t0))),
    ("tableau: an English cell in a French tableau is refused", !decide (ssyt.Faithful
      (changeMark tableau 0 fun m =>
        { m with shape := .rect (cellBox .english 0 0).1 (cellBox .english 0 0).2 }))),
    ("tableau: a filling that is not semistandard is refused by IsSemistandard",
      !decide (Tableau.IsSemistandard { entries := [[2, 1], [3]] }) &&
        !decide (Tableau.IsSemistandard { entries := [[1, 2], [1]] }) &&
        !decide (Tableau.IsSemistandard { entries := [[1], [2, 3]] })),
    ("permutation: the wiring diagram is faithful", decide (perm.FaithfulWiring permWiring)),
    ("permutation: a strand ending elsewhere is refused", !decide (perm.FaithfulWiring
      (changeMark permWiring w0 fun m => { m with shape := .segment (0, 1) (0, 0) }))),
    ("permutation: a dropped strand is refused",
      !decide (perm.FaithfulWiring (dropMark permWiring w0))),
    ("permutation: a dot of the matrix moved is refused", !decide (perm.FaithfulMatrix
      (changeMark permMatrix m0 fun m => { m with part := .cell 0 2 }))),
    ("permutation: a two-line entry changed is refused", !decide (perm.FaithfulTwoLine
      (changeMark permTwoLine 6 fun m => { m with shape := .text "9" (1, 0) .center }))),
    ("permutation: an arrow of the cycle diagram reversed is refused", !decide
      (perm.FaithfulCycles (changeMark permCycles (posOf permCycles (.edge 0 3)) fun m =>
        { m with part := .edge 3 0 }))),
    ("permutation: the crossings are the inversions on 200 random permutations",
      (List.range 200).all fun seed =>
        let vals := (List.range 7).foldl (fun (acc : List Nat × Nat) _ =>
          let (l, s) := acc
          let s' := (s * 1103515245 + 12345) % 2147483648
          let free := (List.range 7).filter (!l.contains ·)
          (l ++ [free.getD (s' / 65536 % free.length) 0], s')) ([], seed + 1) |>.1
        let σ : FinPerm := { values := vals }
        crossingPairs σ.wiring.strands == σ.inversions && decide σ.IsPerm),
    ("permutation: a list that is not a permutation is refused by IsPerm",
      !decide (FinPerm.IsPerm { values := [0, 0, 1] }) &&
        !decide (FinPerm.IsPerm { values := [1, 2, 3] })),
    ("tree: faithful", decide (rooted.Faithful rooted.layout tree)),
    ("tree: a parent link to another parent is refused", !decide (rooted.Faithful rooted.layout
      (changeMark tree (posOf tree (.edge 3 7)) fun m => { m with part := .edge 2 7 }))),
    ("tree: a cycle in the parent links is refused by IsForest",
      !decide (Forest.IsForest ⟨3, fun c => some ((c + 1) % 3), #[]⟩)),
    ("venn: faithful", decide (multiples.FaithfulVenn venn)),
    ("venn: a member in another region is refused", !decide (multiples.FaithfulVenn
      (changeMark venn x0 fun m => { m with part := .member 0 1 }))),
    ("venn: a member moved is refused", !decide (multiples.FaithfulVenn
      (changeMark venn x0 fun m => { m with shape := .text "1" (0, 0) .center }))),
    ("venn: a circle moved is refused", !decide (multiples.FaithfulVenn
      (changeMark venn 0 fun m => { m with shape := .circle (0, 0) vennRadius }))),
    ("venn: a set with an overfull region does not fit",
      !(SetSystem.mk 5 [[0, 1, 2, 3]] #[] #[]).fits),
    ("path: faithful", decide ((LatticePath.ofDyck dyckWord).Faithful dyck)),
    ("path: a step drawn down instead of up is refused", !decide
      ((LatticePath.ofDyck dyckWord).Faithful
        (changeMark dyck s0 fun m => { m with shape := .segment (0, 0) (1, -1) }))),
    ("path: a dropped step is refused",
      !decide ((LatticePath.ofDyck dyckWord).Faithful (dropMark dyck s0))),
    ("path: a word that dips below the axis is not a Dyck word",
      !LatticePath.isDyck [true, false, false, true] && !LatticePath.isDyck [true, true]),
    ("board: faithful", decide (board.Faithful ferrers)),
    ("board: a dropped cell is refused", !decide (board.Faithful (dropMark ferrers 0))),
    ("board: a moved cell is refused", !decide (board.Faithful
      (changeMark ferrers 0 fun m => { m with shape := .rect (1, 1) (2, 2) })))]

/-- The layouts have the properties they are drawn for. -/
def layoutChecks : Array (String × Bool) :=
  let bl := booleanLattice
  let up := fun (P : FinPoset) =>
    P.coverPairs.all fun (i, j) => (P.layout.pos i).2 < (P.layout.pos j).2
  let tidyApart := fun (F : Forest) =>
    let L := F.layout
    (List.range F.n).all fun v =>
      let cs := F.children v
      (cs.zip cs.tail).all (fun (a, b) => (L.pos a).1 + 1 ≤ (L.pos b).1) &&
        (cs.isEmpty || (L.pos v).1 * 2 == (L.pos (cs.headD 0)).1 + (L.pos (cs.getLastD 0)).1)
  let samePos := fun (L : Layout) (n : Nat) =>
    (List.range n).any fun i => (List.range n).any fun j => i < j && L.pos i == L.pos j
  #[("hasse: every cover goes up the page (cube, divisors of 60, a chain, an antichain)",
      up bl && up (FinPoset.mk 12 (fun i j =>
        let ds := [1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60]
        ds.getD j.val 1 % ds.getD i.val 1 == 0) #[]) &&
      up { n := 6, le := fun i j => decide (i ≤ j) } && up { n := 4, le := fun i j => i == j }),
    ("hasse: no two elements share a position", !samePos bl.layout 8),
    ("tree: siblings at least 1 apart, each parent centred over its first and last child",
      tidyApart rooted && tidyApart ⟨30, fun c => if c = 0 then none else some ((c - 1) / 3), #[]⟩),
    ("tree: no two vertices share a position", !samePos rooted.layout 12 &&
      !samePos bst.layout 9),
    ("tree: a vertex in a cycle is drawn below the forest",
      let F : Forest := ⟨4, fun c => if c = 0 then none else if c = 1 then some 0
        else some (5 - c), #[]⟩
      (F.layout.pos 2).2 < -1 && (F.layout.pos 3).2 < -1),
    ("circle: the circular layout's points are exactly on the circle, for n up to 40",
      (List.range 41).all fun n => (List.range n).all fun i =>
        let p := (Layout.circular n).pos i
        p.1 * p.1 + p.2 * p.2 == 1),
    ("circle: the points are within 1e-5 of the equally spaced angles",
      (List.range 13).all fun n => (List.range n).all fun i =>
        let p := (Layout.circular n).pos i
        let θ := 3.141592653589793 / 2 - 2 * 3.141592653589793 * i.toFloat / n.toFloat
        (Exact.toFloat p.1 - θ.cos).abs < 1e-5 && (Exact.toFloat p.2 - θ.sin).abs < 1e-5),
    ("venn: each region's places are inside exactly its circles", slotsOk)]

/-- Hostile data is refused within the caps, quickly (each builder checks its cap before any
work that grows with the data). -/
def boundChecks : Array (String × Bool) :=
  let note := fun (d : Diagram) => d.marks.length == 1 && d.edges.isEmpty && d.cells.isEmpty
  #[("bounds: a graph of a billion vertices is a note",
      note (FinGraph.figure { n := 1000000000, adj := fun _ _ => true })),
    ("bounds: an order on a billion elements is a note",
      note (FinPoset.figure { n := 1000000000, le := fun _ _ => true })),
    ("bounds: a Young diagram with a billion cells is a note",
      note (YoungShape.figure { rows := [1000000000] }) &&
        note (YoungShape.figure { rows := List.replicate 100000 1000 })),
    ("bounds: a tableau with too many cells is a note",
      note (Tableau.figure { entries := List.replicate 5000 [1] })),
    ("bounds: a permutation of 100000 values is a note in every drawing",
      let σ : FinPerm := { values := List.range 100000 }
      [FinPerm.matrix, FinPerm.wiring, FinPerm.cycles, FinPerm.twoLine, FinPerm.oneLine].all
        fun f => note (σ.figure f)),
    ("bounds: a forest of a billion vertices is a note",
      note (Forest.figure ⟨1000000000, fun _ => none, #[]⟩)),
    ("bounds: a path of 100000 steps, or with a long step, is a note",
      note (LatticePath.ofDyck (List.replicate 100000 true)).figure &&
        note (LatticePath.figure ⟨[(1000000000, 0)]⟩)),
    ("bounds: a Venn diagram of four sets, or of a million elements, is a note",
      note (SetSystem.vennFigure ⟨3, [[0], [1], [2], [0]], #[], #[]⟩) &&
        note (SetSystem.vennFigure ⟨1000000, [[0]], #[], #[]⟩) &&
        note (SetSystem.incidenceFigure ⟨1000000, [[0]], #[], #[]⟩))]

/-- The figures pass the layout checks of plane figures in both themes. -/
def planeChecks : Array (String × Bool) :=
  gallery.map fun (n, f) => (s!"layout checks: {n} has no problems ({f.checkMessages})",
    f.checkMessages.isEmpty)

/-- Every check of this module. -/
def checks : Array (String × Bool) := faultChecks ++ layoutChecks ++ boundChecks ++ planeChecks

end PILeanTest.Diagrams
