/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Diagram.CommDiagram
import PILean.Diagram.Graph

/-!
# Finite groups: Cayley tables and Cayley graphs

A `FinMagma` is a binary operation on `Fin n` given by its table, with names for the elements.
Whether it is a group is checked, not assumed: `FinMagma.isGroup` decides associativity, an
identity and inverses on the table.

* The **Cayley table** (`FinMagma.table`) draws the multiplication table: the headings of the
  rows and columns are the elements, and cell `(a, b)` holds the name of `a * b`, tinted in the
  colour of `a * b` (series colour `a * b`, `Ink.series`). `FinMagma.FaithfulTable` accounts for
  every mark: the cells, their colours, the entries, the headings, the two rules and the corner
  sign are exactly the builder's, at their positions, and there is nothing else. In particular
  the entry written in cell `(a, b)` is the name of `a * b` (`FinMagma.entries_table`).
* The **Cayley graph** (`FinMagma.cayley`) for a list of generators is a `CommDiagram` whose
  objects are the elements and which has, for generator number `c` (`s = gens[c]`) and every
  element `g`, an arrow `g → g * s` in series colour `c`; for an involution `s` (`s * s` is the
  identity, `s` is not) the two arrows `g → g s` and `g s → g` are drawn as one line without a
  tip (from the smaller number to the larger). Its faithfulness is that of `CommDiagram`, and
  `FinMagma.mem_cayleyArrows` says which arrows the data has.

## Main definitions

* `FinMagma`, `FinMagma.isAssoc`, `FinMagma.identity?`, `FinMagma.isGroup`,
  `FinMagma.isCommutative`, `FinMagma.isInvolution`
* `FinMagma.table`, `FinMagma.FaithfulTable`, `FinMagma.tableFigure`
* `FinMagma.cayleyArrows`, `FinMagma.cayley`, `FinMagma.cayleyFigure`

## Main results

* `FinMagma.table_faithful`, `FinMagma.entries_table`: the table is faithful, and its entries are
  the products.
* `FinMagma.mem_cayleyArrows`: an arrow of the Cayley graph in colour `c` joins `g` to `g * s`.
-/

namespace PILean.Diagram

/-- A binary operation on the elements `0, …, n - 1`, with their names. -/
structure FinMagma where
  /-- The number of elements. -/
  n : Nat
  /-- The operation. -/
  mul : Fin n → Fin n → Fin n
  /-- The elements' names. -/
  names : Array String := #[]

/-- Whether a part is a cell. -/
def Part.isCell : Part → Bool
  | .cell .. => true
  | _ => false

/-- Whether a part is an entry. -/
def Part.isEntry : Part → Bool
  | .entry .. => true
  | _ => false

/-- Whether a part is a heading. -/
def Part.isHeader : Part → Bool
  | .header .. => true
  | _ => false

/-- Whether a part is a decoration (a guide or a note). -/
def Part.isDecoration : Part → Bool
  | .guide => true
  | .note _ => true
  | _ => false

namespace FinMagma

/-- The most elements a table or a Cayley graph draws: the table has `n²` cells. -/
def maxElements : Nat := 64

/-- The name of element `i`: `names[i]`, or its number. -/
def name (M : FinMagma) (i : Nat) : String := M.names.getD i (toString i)

/-- The operation is associative. -/
def isAssoc (M : FinMagma) : Bool :=
  (List.finRange M.n).all fun a => (List.finRange M.n).all fun b => (List.finRange M.n).all fun c =>
    M.mul (M.mul a b) c == M.mul a (M.mul b c)

/-- `e` is an identity: `e * a = a = a * e` for every `a`. -/
def isIdentity (M : FinMagma) (e : Fin M.n) : Bool :=
  (List.finRange M.n).all fun a => M.mul e a == a && M.mul a e == a

/-- The identity, if there is one (the first element that is one). -/
def identity? (M : FinMagma) : Option (Fin M.n) := (List.finRange M.n).find? M.isIdentity

/-- The table is a group: associative, with an identity `e`, and every `a` has a `b` with
`a * b = e = b * a`. -/
def isGroup (M : FinMagma) : Bool :=
  M.isAssoc && match M.identity? with
    | some e => (List.finRange M.n).all fun a =>
        (List.finRange M.n).any fun b => M.mul a b == e && M.mul b a == e
    | none => false

/-- The operation is commutative: `a * b = b * a` for all `a`, `b`. -/
def isCommutative (M : FinMagma) : Bool :=
  (List.finRange M.n).all fun a => (List.finRange M.n).all fun b => M.mul a b == M.mul b a

/-- The elements that commute with every element (the centre of a group). -/
def centre (M : FinMagma) : List Nat :=
  ((List.finRange M.n).filter fun a => (List.finRange M.n).all fun b => M.mul a b == M.mul b a).map
    (·.val)

/-- `s` is an involution: `s * s` is the identity and `s` is not. -/
def isInvolution (M : FinMagma) (s : Fin M.n) : Bool :=
  match M.identity? with
  | some e => M.mul s s == e && s != e
  | none => false

/-! ### The Cayley table -/

/-- The box of cell `(i, j)`: rows go down and columns right, after the row of headings at the
top and the column of headings at the left, each one unit. -/
def tableBox (i j : Nat) : QPoint × QPoint :=
  (((j : Rat) + 1, -((i : Rat) + 2)), ((j : Rat) + 2, -((i : Rat) + 1)))

/-- The centre of cell `(i, j)`. -/
def tableCentre (i j : Nat) : QPoint := ((j : Rat) + 3 / 2, -((i : Rat) + 3 / 2))

/-- The cells `(i, j)`, row by row. -/
def cellPairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun i => (List.range n).map fun j => (i, j)

/-- The product of the elements numbered `i` and `j` (`0` outside the table). -/
def prod (M : FinMagma) (i j : Nat) : Nat :=
  if h : i < M.n ∧ j < M.n then (M.mul ⟨i, h.1⟩ ⟨j, h.2⟩).val else 0

/-- The marks of the cells: cell `(i, j)` is its box, tinted in the colour of `i * j`. -/
def cellMarks (M : FinMagma) : List Mark :=
  (cellPairs M.n).map fun (i, j) =>
    { part := .cell i j, shape := .rect (tableBox i j).1 (tableBox i j).2,
      ink := .series (M.prod i j) true }

/-- The marks of the entries: the name of `i * j` at the centre of cell `(i, j)`. -/
def entryMarks (M : FinMagma) : List Mark :=
  (cellPairs M.n).map fun (i, j) =>
    { part := .entry i j, shape := .text (M.name (M.prod i j)) (tableCentre i j) .center }

/-- The marks of the headings: the name of element `j` above column `j`, then the name of `i`
left of row `i`. -/
def headerMarks (M : FinMagma) : List Mark :=
  (List.range M.n).map (fun j =>
      { part := .header 1 j, shape := .text (M.name j) ((j : Rat) + 3 / 2, -1 / 2) .center }) ++
    (List.range M.n).map fun i =>
      { part := .header 0 i, shape := .text (M.name i) (1 / 2, -((i : Rat) + 3 / 2)) .center }

/-- The decorations of the table: the rule under the headings of the columns, the rule right of
the headings of the rows, and the sign of the operation `·` in the corner. -/
def tableDecorations (M : FinMagma) : List (Part × Shape) :=
  [(.guide, .segment (0, -1) ((M.n : Rat) + 1, -1)), (.guide, .segment (1, 0) (1, -((M.n : Rat) + 1))),
    (.note 0, .text "·" (1 / 2, -1 / 2) .center)]

/-- The width in pixels of a cell of the table: room for the longest name. -/
def cellPixels (M : FinMagma) : Float :=
  let longest := (List.range M.n).foldl (fun w i => max w (M.name i).length) 1
  max 36 (9 * longest.toFloat + 14)

/-- The marks of the table's decorations, in the faint ink. -/
def decorationMarks (M : FinMagma) : List Mark :=
  M.tableDecorations.map fun (p, s) => { part := p, shape := s, ink := .faint }

/-- The Cayley table: the rules and the corner (under the cells), the cells, the entries, the
headings. -/
def table (M : FinMagma) : Diagram where
  marks := M.decorationMarks ++ M.cellMarks ++ M.entryMarks ++ M.headerMarks
  width := M.cellPixels * (M.n.toFloat + 1) + 40

/-- The entries the table writes: the name of `i * j` in cell `(i, j)`, row by row. -/
def entryTexts (M : FinMagma) : List ((Nat × Nat) × String) :=
  (cellPairs M.n).map fun (i, j) => ((i, j), M.name (M.prod i j))

/-- The diagram draws the table of `M` faithfully: its cells are the `n²` cells, row by row; its
entries are the names of the products (`entryTexts`); its marks of cells (with their colours),
of entries and of headings are exactly the builder's at their positions; its decorations are
exactly the two rules and the corner sign, in the faint ink; and it has no mark of any other
part. -/
def FaithfulTable (M : FinMagma) (d : Diagram) : Prop :=
  d.cells = cellPairs M.n ∧ d.entries = M.entryTexts ∧ d.marksWhere Part.isCell = M.cellMarks ∧
    d.marksWhere Part.isEntry = M.entryMarks ∧ d.marksWhere Part.isHeader = M.headerMarks ∧
    d.marksWhere Part.isDecoration = M.decorationMarks ∧
    d.marks.all (fun m => m.part.isCell || m.part.isEntry || m.part.isHeader ||
      m.part.isDecoration) = true

instance (M : FinMagma) (d : Diagram) : Decidable (M.FaithfulTable d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The marks of the table, class by class. -/
theorem table_marks (M : FinMagma) :
    M.table.marks = M.decorationMarks ++ M.cellMarks ++ M.entryMarks ++ M.headerMarks := rfl

/-- Every mark of the cells is a cell's. -/
theorem isCell_of_mem_cellMarks {M : FinMagma} {m : Mark} (h : m ∈ M.cellMarks) :
    ∃ i j, m.part = .cell i j := by
  simp only [cellMarks, List.mem_map] at h
  obtain ⟨⟨i, j⟩, -, rfl⟩ := h
  exact ⟨i, j, rfl⟩

/-- Every mark of the entries is an entry's. -/
theorem isEntry_of_mem_entryMarks {M : FinMagma} {m : Mark} (h : m ∈ M.entryMarks) :
    ∃ i j, m.part = .entry i j := by
  simp only [entryMarks, List.mem_map] at h
  obtain ⟨⟨i, j⟩, -, rfl⟩ := h
  exact ⟨i, j, rfl⟩

/-- Every mark of the headings is a heading's. -/
theorem isHeader_of_mem_headerMarks {M : FinMagma} {m : Mark} (h : m ∈ M.headerMarks) :
    ∃ a i, m.part = .header a i := by
  simp only [headerMarks, List.mem_append, List.mem_map] at h
  rcases h with ⟨j, -, rfl⟩ | ⟨i, -, rfl⟩
  · exact ⟨1, j, rfl⟩
  · exact ⟨0, i, rfl⟩

/-- Every mark of the decorations is a guide or the note of the corner. -/
theorem isDecoration_of_mem_decorationMarks {M : FinMagma} {m : Mark}
    (h : m ∈ M.decorationMarks) : m.part = .guide ∨ m.part = .note 0 := by
  simp only [decorationMarks, tableDecorations, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> simp

/-- The table is faithful. -/
theorem table_faithful (M : FinMagma) : M.FaithfulTable M.table := by
  have hC := @isCell_of_mem_cellMarks M
  have hE := @isEntry_of_mem_entryMarks M
  have hH := @isHeader_of_mem_headerMarks M
  have hD := @isDecoration_of_mem_decorationMarks M
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Diagram.cells, table_marks, List.filterMap_append]
    rw [(List.filterMap_eq_nil_iff (l := M.entryMarks)).2 fun m hm => by
        obtain ⟨a, i, h⟩ := hE hm; simp [h],
      (List.filterMap_eq_nil_iff (l := M.headerMarks)).2 fun m hm => by
        obtain ⟨a, i, h⟩ := hH hm; simp [h],
      (List.filterMap_eq_nil_iff (l := M.decorationMarks)).2 fun m hm => by
        rcases hD hm with h | h <;> simp [h]]
    simp [cellMarks, List.filterMap_map, Function.comp_def]
  · simp only [Diagram.entries, table_marks, List.filterMap_append]
    rw [(List.filterMap_eq_nil_iff (l := M.cellMarks)).2 fun m hm => by
        obtain ⟨a, i, h⟩ := hC hm; simp [h],
      (List.filterMap_eq_nil_iff (l := M.headerMarks)).2 fun m hm => by
        obtain ⟨a, i, h⟩ := hH hm; simp [h],
      (List.filterMap_eq_nil_iff (l := M.decorationMarks)).2 fun m hm => by
        rcases hD hm with h | h <;> simp [h]]
    simp [entryMarks, entryTexts, List.filterMap_map, Function.comp_def]
  · simp only [Diagram.marksWhere, table_marks, List.filter_append]
    rw [(List.filter_eq_self (l := M.cellMarks)).2 fun m hm => by
        obtain ⟨a, i, h⟩ := hC hm; simp [h, Part.isCell],
      (List.filter_eq_nil_iff (l := M.entryMarks)).2 fun m hm => by
        obtain ⟨a, i, h⟩ := hE hm; simp [h, Part.isCell],
      (List.filter_eq_nil_iff (l := M.headerMarks)).2 fun m hm => by
        obtain ⟨a, i, h⟩ := hH hm; simp [h, Part.isCell],
      (List.filter_eq_nil_iff (l := M.decorationMarks)).2 fun m hm => by
        rcases hD hm with h | h <;> simp [h, Part.isCell]]
    simp
  · simp only [Diagram.marksWhere, table_marks, List.filter_append]
    rw [(List.filter_eq_nil_iff (l := M.cellMarks)).2 fun m hm => by
        obtain ⟨a, i, h⟩ := hC hm; simp [h, Part.isEntry],
      (List.filter_eq_self (l := M.entryMarks)).2 fun m hm => by
        obtain ⟨a, i, h⟩ := hE hm; simp [h, Part.isEntry],
      (List.filter_eq_nil_iff (l := M.headerMarks)).2 fun m hm => by
        obtain ⟨a, i, h⟩ := hH hm; simp [h, Part.isEntry],
      (List.filter_eq_nil_iff (l := M.decorationMarks)).2 fun m hm => by
        rcases hD hm with h | h <;> simp [h, Part.isEntry]]
    simp
  · simp only [Diagram.marksWhere, table_marks, List.filter_append]
    rw [(List.filter_eq_nil_iff (l := M.cellMarks)).2 fun m hm => by
        obtain ⟨a, i, h⟩ := hC hm; simp [h, Part.isHeader],
      (List.filter_eq_nil_iff (l := M.entryMarks)).2 fun m hm => by
        obtain ⟨a, i, h⟩ := hE hm; simp [h, Part.isHeader],
      (List.filter_eq_self (l := M.headerMarks)).2 fun m hm => by
        obtain ⟨a, i, h⟩ := hH hm; simp [h, Part.isHeader],
      (List.filter_eq_nil_iff (l := M.decorationMarks)).2 fun m hm => by
        rcases hD hm with h | h <;> simp [h, Part.isHeader]]
    simp
  · simp only [Diagram.marksWhere, table_marks, List.filter_append]
    rw [(List.filter_eq_self (l := M.decorationMarks)).2 fun m hm => by
        rcases hD hm with h | h <;> simp [h, Part.isDecoration],
      (List.filter_eq_nil_iff (l := M.cellMarks)).2 fun m hm => by
        obtain ⟨a, i, h⟩ := hC hm; simp [h, Part.isDecoration],
      (List.filter_eq_nil_iff (l := M.entryMarks)).2 fun m hm => by
        obtain ⟨a, i, h⟩ := hE hm; simp [h, Part.isDecoration],
      (List.filter_eq_nil_iff (l := M.headerMarks)).2 fun m hm => by
        obtain ⟨a, i, h⟩ := hH hm; simp [h, Part.isDecoration]]
    simp
  · simp only [table_marks, List.all_append, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true]
    refine ⟨⟨⟨fun m hm => ?_, fun m hm => ?_⟩, fun m hm => ?_⟩, fun m hm => ?_⟩
    · rcases hD hm with h | h <;> simp [h, Part.isDecoration]
    · obtain ⟨a, i, h⟩ := hC hm; simp [h, Part.isCell]
    · obtain ⟨a, i, h⟩ := hE hm; simp [h, Part.isEntry]
    · obtain ⟨a, i, h⟩ := hH hm; simp [h, Part.isHeader]

/-- The table, or a note for more than `maxElements` elements. -/
def tableFigure (M : FinMagma) : Diagram :=
  Diagram.capped (M.n ≤ maxElements) s!"{M.n} elements: too many to draw" fun _ => M.table

/-- Within the cap the table is drawn faithfully. -/
theorem tableFigure_faithful (M : FinMagma) (h : M.n ≤ maxElements) :
    M.FaithfulTable M.tableFigure := by
  unfold tableFigure
  rw [Diagram.capped_of (by simpa using h)]
  exact M.table_faithful

/-- The entry written in cell `(i, j)` of a faithful table is the name of `i * j`, and every cell
of the table has its entry. -/
theorem entries_table {M : FinMagma} {d : Diagram} (h : M.FaithfulTable d) (i j : Nat)
    (s : String) : ((i, j), s) ∈ d.entries ↔
      ∃ (hi : i < M.n) (hj : j < M.n), s = M.name (M.mul ⟨i, hi⟩ ⟨j, hj⟩) := by
  rw [h.2.1, entryTexts, List.mem_map]
  simp only [cellPairs, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨i', j'⟩, ⟨a, ha, b, hb, h⟩, h'⟩
    simp only [Prod.mk.injEq] at h h'
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h'
    exact ⟨ha, hb, by simp [prod, ha, hb]⟩
  · rintro ⟨hi, hj, rfl⟩
    exact ⟨(i, j), ⟨i, hi, j, hj, rfl⟩, by simp [prod, hi, hj]⟩

/-! ### The Cayley graph -/

/-- The arrows of the Cayley graph for the generators `gens`: generator by generator (number `c`,
in series colour `c`), element by element, an arrow `g → g * s`; for an involution `s` one line
without a tip for each pair `{g, g s}`, from the smaller number. -/
def cayleyArrows (M : FinMagma) (gens : List (Fin M.n)) : List CDArrow :=
  gens.zipIdx.flatMap fun (s, c) => (List.finRange M.n).filterMap fun g =>
    let h := M.mul g s
    if M.isInvolution s then
      if g.val < h.val then some { src := g, tgt := h, style := .line, ink := .series c false }
      else none
    else some { src := g, tgt := h, ink := .series c false }

/-- The Cayley graph as a diagram of the elements at the positions `pos`. -/
def cayley (M : FinMagma) (gens : List (Fin M.n)) (pos : Array QPoint) : CommDiagram where
  objects := ((List.range M.n).map M.name).toArray
  pos := pos
  arrows := M.cayleyArrows gens

/-- The elements on a circle of radius `radius` (`Layout.circular`). -/
def circlePositions (n : Nat) (radius : Rat := 1) : Array QPoint :=
  ((List.range n).map (Layout.circular n radius).pos).toArray

/-- The Cayley graph at the positions `pos`, or a note for more than `maxElements` elements or
more than 8 generators. -/
def cayleyFigure (M : FinMagma) (gens : List (Fin M.n)) (pos : Array QPoint) : Diagram :=
  Diagram.capped (M.n ≤ maxElements && gens.length ≤ 8)
    s!"{M.n} elements and {gens.length} generators: too many to draw" fun _ =>
    (M.cayley gens pos).figure

/-- The arrows of the Cayley graph in colour `c` are those of generator `s = gens[c]`: each
joins an element `g` to `g * s`; a line (an involution's) joins the smaller-numbered of `g` and
`g * s` to the other. Conversely every element `g` has its arrow for every generator. -/
theorem mem_cayleyArrows (M : FinMagma) (gens : List (Fin M.n)) (a : CDArrow) :
    a ∈ M.cayleyArrows gens ↔ ∃ c s g, gens[c]? = some s ∧ a.ink = .series c false ∧
      a.src = g.val ∧ a.tgt = (M.mul g s).val ∧
      (if M.isInvolution s then g.val < (M.mul g s).val ∧ a.style = .line
        else a.style = .plain) ∧ a.label = "" ∧ a.bend = 0 ∧ a.swap = false := by
  simp only [cayleyArrows, List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨⟨s, c⟩, hsc, g, hg⟩
    rw [List.mem_zipIdx_iff_getElem?] at hsc
    refine ⟨c, s, g, hsc, ?_⟩
    split at hg
    · split at hg
      · cases hg
        simp_all
      · cases hg
    · cases hg
      simp_all
  · rintro ⟨c, s, g, hsc, hink, hsrc, htgt, hst, hl, hb, hsw⟩
    refine ⟨(s, c), List.mem_zipIdx_iff_getElem?.2 hsc, g, ?_⟩
    obtain ⟨src, tgt, label, style, bend, swap, k⟩ := a
    simp only at hink hsrc htgt hst hl hb hsw
    subst hink hsrc htgt hl hb hsw
    split
    · rename_i hinv
      simp only [hinv, ite_true] at hst
      simp [hst.1, hst.2]
    · rename_i hinv
      simp only [hinv, Bool.false_eq_true, ite_false] at hst
      simp [hst]

end FinMagma

end PILean.Diagram
