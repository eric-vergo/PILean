/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Diagram.CommDiagram

/-!
# Plots of sequences and grids of numbers

Two kinds for number theory, drawn from the sequences and predicates themselves.

* A `SeqPlot` plots sequences `f : ℕ → ℚ` on a range `lo, …, hi`: point `n` of sequence `k` is a
  dot at `(sx n, sy (f n))` for the plot's exact scales `sx`, `sy` (`SeqLayout`), and comparison
  curves are polylines through `(sx n, sy (c n))`. The axes, their ticks and tick labels, and the
  legend are the plot's decorations. `SeqPlot.Faithful` accounts for every mark: the dots are
  exactly the points `(k, n)` for every sequence `k` and every `n` of the range, each at its exact
  position (`SeqPlot.mem_data`), the curves are exactly the comparison curves, the decorations
  exactly the builder's, and there is nothing else.
* A `CellPlot` is a list of unit cells at integer positions, each marked or not, with a text: the
  numbers of an Ulam spiral marked where a predicate holds, or a table of residues.
  `CellPlot.Faithful` accounts for every cell, its colour (accent 0 tinted exactly when marked)
  and its text, the headings and nothing else.

`ulam n` is the position of `n ≥ 1` on the square spiral, `1` at the origin.

## Main definitions

* `SeqPlot`, `SeqLayout`, `SeqPlot.layout`, `SeqPlot.draw`, `SeqPlot.figure`, `SeqPlot.Faithful`
* `Diagram.data`: the dots of a plot, read back
* `CellPlot`, `CellPlot.draw`, `CellPlot.figure`, `CellPlot.Faithful`, `ulam`, `ulamCells`

## Main results

* `SeqPlot.draw_faithful`, `SeqPlot.builder_faithful`, `SeqPlot.mem_data`.
* `CellPlot.draw_faithful`, `CellPlot.builder_faithful`, `CellPlot.mem_marked`.
-/

namespace PILean.Diagram

/-- Whether a part is a point of a plotted sequence. -/
def Part.isDatum : Part → Bool
  | .datum .. => true
  | _ => false

/-- Whether a part is a plotted curve. -/
def Part.isCurve : Part → Bool
  | .curve _ => true
  | _ => false

/-- The points a plot draws: `(k, n, p)` for each mark of the part `datum k n` (point `n` of
sequence `k`) that is a dot at `p`, in order. -/
def Diagram.data (d : Diagram) : List (Nat × Nat × QPoint) :=
  d.marks.filterMap fun m => match m.part, m.shape with
    | .datum k n, .dot p => some (k, n, p)
    | _, _ => none

/-- Sequences on a range of integers, with comparison curves. -/
structure SeqPlot where
  /-- The first index. -/
  lo : Nat
  /-- The last index. -/
  hi : Nat
  /-- The sequences, with their names. -/
  series : List (String × (Nat → Rat))
  /-- Comparison curves, evaluated at the integers of the range and joined by straight lines. -/
  curves : List (String × (Nat → Rat)) := []

/-- The exact scales of a plot: index `n` at `x = sx n`, value `v` at `y = sy v`; the lowest value
`vlo` and the highest `vhi` the axes show, and the steps of their ticks. -/
structure SeqLayout where
  /-- World units per unit of the index. -/
  sx : Rat
  /-- World units per unit of value. -/
  sy : Rat
  /-- The lowest value shown (where the index axis crosses). -/
  vlo : Rat
  /-- The highest value shown. -/
  vhi : Rat
  /-- The step of the ticks of the index axis. -/
  xstep : Nat
  /-- The step of the ticks of the value axis. -/
  ystep : Rat

namespace SeqPlot

/-- The most indices a plot draws. -/
def maxIndices : Nat := 2000

/-- The most sequences and curves a plot draws. -/
def maxSeries : Nat := 6

/-- The indices `lo, …, hi`. -/
def indices (P : SeqPlot) : List Nat := List.range' P.lo (P.hi + 1 - P.lo)

/-- A step for ticks across a range: the least of `1, 2, 5, 10, 20, 50, …` at least a sixth of
the range. -/
def niceStep (range : Rat) : Rat := Id.run do
  let mut s : Rat := 1
  for _ in [0:30] do
    if s * 6 ≥ range then return s
    if 2 * s * 6 ≥ range then return 2 * s
    if 5 * s * 6 ≥ range then return 5 * s
    s := 10 * s
  return s

/-- The values of every sequence and curve on the range, with `0`. -/
def values (P : SeqPlot) : List Rat :=
  0 :: (P.series ++ P.curves).flatMap fun (_, f) => P.indices.map f

/-- The layout: the values from the least to the greatest of `values` (rounded out to the ticks'
step), an index axis three units long and a value axis two units high. -/
def layout (P : SeqPlot) : SeqLayout :=
  let vs := P.values
  let lo := vs.foldl min 0
  let hi := vs.foldl max 0
  let ystep := niceStep (hi - lo)
  let vlo := ystep * ((lo / ystep).floor : Rat)
  let vhi := ystep * ((hi / ystep).ceil : Rat)
  let span : Rat := max 1 ((P.hi : Rat) - P.lo)
  { sx := 3 / span, sy := 2 / max 1 (vhi - vlo), vlo, vhi,
    xstep := max 1 (niceStep span).ceil.toNat, ystep }

/-- The exact point of index `n` and value `v`. -/
def point (L : SeqLayout) (n : Nat) (v : Rat) : QPoint := (L.sx * n, L.sy * v)

/-- The marks of the points: point `n` of sequence `k` is a dot at `point n (f n)` in series colour
`k`. -/
def dataMarks (P : SeqPlot) (L : SeqLayout) : List Mark :=
  P.series.zipIdx.flatMap fun ((_, f), k) => P.indices.map fun n =>
    { part := .datum k n, shape := .dot (point L n (f n)), ink := .series k false }

/-- The marks of the curves: curve `j` is the polyline through `point n (c n)`, in series colour
`#series + j`, of the part `curve j`. -/
def curveMarks (P : SeqPlot) (L : SeqLayout) : List Mark :=
  P.curves.zipIdx.map fun ((_, c), j) =>
    { part := .curve j, shape := .polyline (P.indices.map fun n => point L n (c n)),
      ink := .series (P.series.length + j) false }

/-- A tick label: an integer as itself, another rational as `p/q`. -/
def tickText (q : Rat) : String := if q.den = 1 then toString q.num else s!"{q.num}/{q.den}"

/-- The tick marks of the index axis, the indices at which they stand. -/
def xticks (P : SeqPlot) (L : SeqLayout) : List Nat :=
  (List.range ((P.hi - P.lo) / L.xstep + 1)).map fun i => P.lo + i * L.xstep

/-- The values at the ticks of the value axis. -/
def yticks (L : SeqLayout) : List Rat :=
  (List.range (((L.vhi - L.vlo) / L.ystep).floor.toNat + 1)).map fun (i : Nat) =>
    L.vlo + i * L.ystep

/-- The names of the sequences and curves, in the order of their colours. -/
def names (P : SeqPlot) : List String := P.series.map (·.1) ++ P.curves.map (·.1)

/-- The height of the legend's line `i`, above the value axis. -/
def legendY (P : SeqPlot) (L : SeqLayout) (i : Nat) : Rat :=
  L.sy * L.vhi + (3 : Rat) / 10 * ((P.names.length : Rat) - i)

/-- The lines of the decorations with their inks: the index axis at the lowest value and the
value axis at the first index, their ticks (faint), and the legend's samples (a short line in the
colour of each sequence and curve, at the top left). -/
def guides (P : SeqPlot) (L : SeqLayout) : List (Shape × Ink) :=
  let x0 := L.sx * P.lo
  let y0 := L.sy * L.vlo
  let t : Rat := 1 / 20
  [(.segment (x0, y0) (L.sx * P.hi, y0), .faint), (.segment (x0, y0) (x0, L.sy * L.vhi), .faint)] ++
    (P.xticks L).map (fun n => (.segment (L.sx * n, y0) (L.sx * n, y0 - t), .faint)) ++
    (yticks L).map (fun v => (.segment (x0, L.sy * v) (x0 - t, L.sy * v), .faint)) ++
    P.names.zipIdx.map fun (_, i) =>
      (.segment (x0, P.legendY L i) (x0 + 1 / 5, P.legendY L i), .series i false)

/-- The texts of the decorations: the ticks' labels (`note 0` below the index axis, `note 1` left
of the value axis) and the legend's names (`note 2`). -/
def notes (P : SeqPlot) (L : SeqLayout) : List (Nat × Shape) :=
  let x0 := L.sx * P.lo
  let y0 := L.sy * L.vlo
  let t : Rat := 1 / 20
  (P.xticks L).map (fun n => (0, .text (toString n) (L.sx * n, y0 - t) .below)) ++
    (yticks L).map (fun v => (1, .text (tickText v) (x0 - t, L.sy * v) .left)) ++
    P.names.zipIdx.map fun (s, i) => (2, .text s (x0 + 3 / 10, P.legendY L i) .right)

/-- The marks of the decorations: the guides in their inks, then the notes in the ink. -/
def decorationMarks (P : SeqPlot) (L : SeqLayout) : List Mark :=
  (P.guides L).map (fun (s, i) => { part := .guide, shape := s, ink := i }) ++
    (P.notes L).map fun (k, s) => { part := .note k, shape := s }

/-- The diagram at the layout `L`: the decorations, the curves, then the points. -/
def draw (P : SeqPlot) (L : SeqLayout) : Diagram where
  marks := P.decorationMarks L ++ P.curveMarks L ++ P.dataMarks L

/-- The points of the plot: `(k, n, point n (f n))` for every sequence `k` and every index `n`,
sequence by sequence. -/
def dataTriples (P : SeqPlot) (L : SeqLayout) : List (Nat × Nat × QPoint) :=
  P.series.zipIdx.flatMap fun ((_, f), k) => P.indices.map fun n => (k, n, point L n (f n))

/-- The diagram draws the plot faithfully at `L`: its points (`Diagram.data`) are exactly
`dataTriples`; its marks of points, of curves and of decorations are exactly the builder's
(colours included); there is no mark of any other part. -/
def Faithful (P : SeqPlot) (L : SeqLayout) (d : Diagram) : Prop :=
  d.data = P.dataTriples L ∧ d.marksWhere Part.isDatum = P.dataMarks L ∧
    d.marksWhere Part.isCurve = P.curveMarks L ∧
    d.marksWhere (fun p => p.isDecoration) = P.decorationMarks L ∧
    d.marks.all (fun m => m.part.isDatum || m.part.isCurve || m.part.isDecoration) = true

instance (P : SeqPlot) (L : SeqLayout) (d : Diagram) : Decidable (P.Faithful L d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Every mark of the points is a point's. -/
theorem isDatum_of_mem_dataMarks {P : SeqPlot} {L : SeqLayout} {m : Mark}
    (h : m ∈ P.dataMarks L) : ∃ k n, m.part = .datum k n := by
  simp only [dataMarks, List.mem_flatMap, List.mem_map] at h
  obtain ⟨_, -, n, -, rfl⟩ := h
  exact ⟨_, n, rfl⟩

/-- Every mark of the curves is a curve's. -/
theorem isCurve_of_mem_curveMarks {P : SeqPlot} {L : SeqLayout} {m : Mark}
    (h : m ∈ P.curveMarks L) : ∃ j, m.part = .curve j := by
  simp only [curveMarks, List.mem_map] at h
  obtain ⟨_, -, rfl⟩ := h
  exact ⟨_, rfl⟩

/-- Every mark of the decorations is a guide or a note. -/
theorem isDecoration_of_mem_decorationMarks {P : SeqPlot} {L : SeqLayout} {m : Mark}
    (h : m ∈ P.decorationMarks L) : m.part = .guide ∨ ∃ k, m.part = .note k := by
  simp only [decorationMarks, List.mem_append, List.mem_map] at h
  rcases h with ⟨_, -, rfl⟩ | ⟨_, -, rfl⟩
  · exact .inl rfl
  · exact .inr ⟨_, rfl⟩

/-- The plot is faithful at every layout. -/
theorem draw_faithful (P : SeqPlot) (L : SeqLayout) : P.Faithful L (P.draw L) := by
  have hD := @isDatum_of_mem_dataMarks P L
  have hC := @isCurve_of_mem_curveMarks P L
  have hN := @isDecoration_of_mem_decorationMarks P L
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Diagram.data, draw, List.filterMap_append]
    rw [(List.filterMap_eq_nil_iff (l := P.decorationMarks L)).2 fun m hm => by
        rcases hN hm with h | ⟨k, h⟩ <;> simp [h],
      (List.filterMap_eq_nil_iff (l := P.curveMarks L)).2 fun m hm => by
        obtain ⟨j, h⟩ := hC hm; simp [h]]
    simp [dataMarks, dataTriples, List.filterMap_flatMap, List.filterMap_map, Function.comp_def]
  · simp only [Diagram.marksWhere, draw, List.filter_append]
    rw [(List.filter_eq_nil_iff (l := P.decorationMarks L)).2 fun m hm => by
        rcases hN hm with h | ⟨k, h⟩ <;> simp [h, Part.isDatum],
      (List.filter_eq_nil_iff (l := P.curveMarks L)).2 fun m hm => by
        obtain ⟨j, h⟩ := hC hm; simp [h, Part.isDatum],
      (List.filter_eq_self (l := P.dataMarks L)).2 fun m hm => by
        obtain ⟨k, n, h⟩ := hD hm; simp [h, Part.isDatum]]
    simp
  · simp only [Diagram.marksWhere, draw, List.filter_append]
    rw [(List.filter_eq_nil_iff (l := P.decorationMarks L)).2 fun m hm => by
        rcases hN hm with h | ⟨k, h⟩ <;> simp [h, Part.isCurve],
      (List.filter_eq_self (l := P.curveMarks L)).2 fun m hm => by
        obtain ⟨j, h⟩ := hC hm; simp [h, Part.isCurve],
      (List.filter_eq_nil_iff (l := P.dataMarks L)).2 fun m hm => by
        obtain ⟨k, n, h⟩ := hD hm; simp [h, Part.isCurve]]
    simp
  · simp only [Diagram.marksWhere, draw, List.filter_append]
    rw [(List.filter_eq_self (l := P.decorationMarks L)).2 fun m hm => by
        rcases hN hm with h | ⟨k, h⟩ <;> simp [h, Part.isDecoration],
      (List.filter_eq_nil_iff (l := P.curveMarks L)).2 fun m hm => by
        obtain ⟨j, h⟩ := hC hm; simp [h, Part.isDecoration],
      (List.filter_eq_nil_iff (l := P.dataMarks L)).2 fun m hm => by
        obtain ⟨k, n, h⟩ := hD hm; simp [h, Part.isDecoration]]
    simp
  · simp only [draw, List.all_append, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true]
    refine ⟨⟨fun m hm => ?_, fun m hm => ?_⟩, fun m hm => ?_⟩
    · rcases hN hm with h | ⟨k, h⟩ <;> simp [h, Part.isDecoration]
    · obtain ⟨j, h⟩ := hC hm; simp [h, Part.isCurve]
    · obtain ⟨k, n, h⟩ := hD hm; simp [h, Part.isDatum]

/-- The points of a plot are exactly the values of its sequences on its range: `(k, n, p)` is
drawn exactly when `k` is a sequence, `n` an index of the range, and `p` the exact point of `n`
and the value of sequence `k` at `n`. -/
theorem mem_data (P : SeqPlot) (L : SeqLayout) (k n : Nat) (p : QPoint) :
    (k, n, p) ∈ P.dataTriples L ↔ ∃ s f, P.series[k]? = some (s, f) ∧ P.lo ≤ n ∧ n ≤ P.hi ∧
      p = point L n (f n) := by
  simp only [dataTriples, List.mem_flatMap, List.mem_map, Prod.mk.injEq, indices, List.mem_range']
  constructor
  · rintro ⟨⟨⟨s, f⟩, k'⟩, hk, n', ⟨i, hi, rfl⟩, rfl, rfl, rfl⟩
    exact ⟨s, f, List.mem_zipIdx_iff_getElem?.1 hk, by omega, by omega, rfl⟩
  · rintro ⟨s, f, hk, hlo, hhi, rfl⟩
    exact ⟨((s, f), k), List.mem_zipIdx_iff_getElem?.2 hk, n, ⟨n - P.lo, by omega, by omega⟩,
      rfl, rfl, rfl⟩

/-- The plot at its layout, or a note beyond the caps (more than `maxIndices` indices or
`maxSeries` sequences and curves). -/
def figure (P : SeqPlot) : Diagram :=
  Diagram.capped (P.hi + 1 - P.lo ≤ maxIndices && P.series.length + P.curves.length ≤ maxSeries)
    s!"a plot of {P.hi + 1 - P.lo} indices and {P.series.length + P.curves.length} series: \
      too many to draw" fun _ => { P.draw P.layout with width := 560 }

/-- Within the caps the plot is drawn faithfully by `figure`. -/
theorem builder_faithful (P : SeqPlot)
    (h : (P.hi + 1 - P.lo ≤ maxIndices && P.series.length + P.curves.length ≤ maxSeries) = true) :
    P.Faithful P.layout P.figure := by
  have e : P.figure.marks = (P.draw P.layout).marks := by
    simp only [figure, Diagram.capped, h, ite_true]
  have hd := P.draw_faithful P.layout
  unfold Faithful Diagram.data Diagram.marksWhere at hd ⊢
  rw [e]
  exact hd

end SeqPlot

/-! ### Grids of numbers -/

/-- A cell of a `CellPlot`: its key, its position (the lower left corner of a unit square), whether
it is marked, and its text (none when empty). -/
structure NumberCell where
  /-- The number or key the cell stands for. -/
  key : Nat
  /-- The lower left corner. -/
  pos : Int × Int
  /-- Whether the cell is marked. -/
  marked : Bool
  /-- The text written in the cell. -/
  text : String := ""
  deriving DecidableEq, Repr, Inhabited

/-- Unit cells at integer positions, marked or not, with texts and headings. -/
structure CellPlot where
  /-- The cells. -/
  cells : List NumberCell
  /-- The headings: their texts and positions. -/
  headings : List (String × QPoint) := []
  deriving Inhabited

namespace CellPlot

/-- The most cells a plot draws. -/
def maxCells : Nat := 4000

/-- The unit square of a cell. -/
def box (c : NumberCell) : QPoint × QPoint :=
  (((c.pos.1 : Rat), (c.pos.2 : Rat)), ((c.pos.1 : Rat) + 1, (c.pos.2 : Rat) + 1))

/-- The marks of a cell: its square, tinted in accent 0 when marked and in the faint ink otherwise,
then its text at its centre when it has one. -/
def cellMarks (c : NumberCell) : List Mark :=
  { part := .cell c.key 0, shape := .rect (box c).1 (box c).2,
    ink := if c.marked then .tint 0 else .faint } ::
  (if c.text.isEmpty then [] else
    let centre : QPoint := ((c.pos.1 : Rat) + 1 / 2, (c.pos.2 : Rat) + 1 / 2)
    [{ part := .entry c.key 0, shape := .text c.text centre .center }])

/-- The marks of the headings. -/
def headingMarks (P : CellPlot) : List Mark :=
  P.headings.zipIdx.map fun ((s, p), i) => { part := .header 0 i, shape := .text s p .center }

/-- The diagram: the cells (each with its text), then the headings. -/
def draw (P : CellPlot) : Diagram where
  marks := P.cells.flatMap cellMarks ++ P.headingMarks

/-- The diagram draws the cells faithfully: its marks of cells and entries are exactly the cells'
(position, colour by mark, text), cell by cell; its headings exactly the plot's; and nothing
else. -/
def Faithful (P : CellPlot) (d : Diagram) : Prop :=
  d.marksWhere (fun p => p.isCell || p.isEntry) = P.cells.flatMap cellMarks ∧
    d.marksWhere Part.isHeader = P.headingMarks ∧
    d.marks.all (fun m => m.part.isCell || m.part.isEntry || m.part.isHeader) = true

instance (P : CellPlot) (d : Diagram) : Decidable (P.Faithful d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Every mark of a cell is the cell's square or its text. -/
theorem part_of_mem_cellMarks {c : NumberCell} {m : Mark} (h : m ∈ cellMarks c) :
    m.part = .cell c.key 0 ∨ m.part = .entry c.key 0 := by
  unfold cellMarks at h
  simp only [List.mem_cons] at h
  rcases h with rfl | h
  · exact .inl rfl
  · split at h <;> simp at h
    subst h
    exact .inr rfl

/-- The diagram is faithful. -/
theorem draw_faithful (P : CellPlot) : P.Faithful P.draw := by
  have hC : ∀ m ∈ P.cells.flatMap cellMarks, m.part.isCell = true ∨ m.part.isEntry = true := by
    intro m hm
    obtain ⟨c, -, hm⟩ := List.mem_flatMap.1 hm
    rcases part_of_mem_cellMarks hm with h | h <;> simp [h, Part.isCell, Part.isEntry]
  have hH : ∀ m ∈ P.headingMarks, ∃ i, m.part = .header 0 i := by
    intro m hm
    simp only [headingMarks, List.mem_map] at hm
    obtain ⟨_, -, rfl⟩ := hm
    exact ⟨_, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [Diagram.marksWhere, draw, List.filter_append]
    rw [(List.filter_eq_self (l := P.cells.flatMap cellMarks)).2 fun m hm => by
        simpa [Bool.or_eq_true] using hC m hm,
      (List.filter_eq_nil_iff (l := P.headingMarks)).2 fun m hm => by
        obtain ⟨i, h⟩ := hH m hm; simp [h, Part.isCell, Part.isEntry]]
    simp
  · simp only [Diagram.marksWhere, draw, List.filter_append]
    rw [(List.filter_eq_nil_iff (l := P.cells.flatMap cellMarks)).2 fun m hm => by
        rcases hC m hm with h | h <;> cases hp : m.part <;> simp_all [Part.isCell, Part.isEntry,
          Part.isHeader],
      (List.filter_eq_self (l := P.headingMarks)).2 fun m hm => by
        obtain ⟨i, h⟩ := hH m hm; simp [h, Part.isHeader]]
    simp
  · simp only [draw, List.all_append, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true]
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · rcases hC m hm with h | h <;> simp [h]
    · obtain ⟨i, h⟩ := hH m hm; simp [h, Part.isHeader]

/-- In a faithful diagram every cell is drawn as its unit square in the colour of its mark:
accent 0 tinted when the cell is marked, the faint ink otherwise. -/
theorem mem_marked {P : CellPlot} {d : Diagram} (h : P.Faithful d) (c : NumberCell)
    (hc : c ∈ P.cells) :
    { part := .cell c.key 0, shape := .rect (box c).1 (box c).2,
      ink := if c.marked then .tint 0 else .faint } ∈ d.marks := by
  let m : Mark := { part := .cell c.key 0, shape := .rect (box c).1 (box c).2,
                    ink := if c.marked then .tint 0 else .faint }
  have hm : m ∈ d.marksWhere (fun p => p.isCell || p.isEntry) := by
    rw [h.1]
    exact List.mem_flatMap.2 ⟨c, hc, by simp [cellMarks, m]⟩
  exact (List.mem_filter.1 hm).1

/-- The diagram, or a note for more than `maxCells` cells. -/
def figure (P : CellPlot) : Diagram :=
  Diagram.capped (P.cells.length ≤ maxCells && P.headings.length ≤ maxCells)
    s!"{P.cells.length} cells: too many to draw" fun _ => P.draw

/-- Within the cap the cells are drawn faithfully by `figure`. -/
theorem builder_faithful (P : CellPlot)
    (h : (P.cells.length ≤ maxCells && P.headings.length ≤ maxCells) = true) :
    P.Faithful P.figure := by
  unfold figure
  rw [Diagram.capped_of h]
  exact P.draw_faithful

end CellPlot

/-- The position of `n ≥ 1` on the square spiral: `1` at the origin, then one step right, one up,
two left, two down, three right, … (`ulamWalk`). -/
def ulamWalk (count : Nat) : Array (Int × Int) := Id.run do
  let mut out : Array (Int × Int) := #[(0, 0)]
  let mut x : Int := 0
  let mut y : Int := 0
  let mut run := 1
  let mut dir := 0
  while out.size < count do
    for _ in [0:2] do
      for _ in [0:run] do
        match dir % 4 with
        | 0 => x := x + 1
        | 1 => y := y + 1
        | 2 => x := x - 1
        | _ => y := y - 1
        out := out.push (x, y)
      dir := dir + 1
    run := run + 1
  return out

/-- The Ulam spiral of `1, …, count`: cell `n` at its place on the spiral, marked where `p n`,
with its number written when `numbers`. -/
def ulamCells (count : Nat) (p : Nat → Bool) (numbers : Bool := false) : List NumberCell :=
  let w := ulamWalk count
  (List.range count).map fun i =>
    { key := i + 1, pos := w.getD i (0, 0), marked := p (i + 1),
      text := if numbers then toString (i + 1) else "" }

end PILean.Diagram
