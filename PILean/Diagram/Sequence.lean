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

`ulamWalk count` lists the positions of `1, …, count` on the square spiral, `1` at the origin.

## Main definitions

* `SeqPlot`, `SeqLayout`, `SeqPlot.layout`, `SeqPlot.draw`, `SeqPlot.figure`, `SeqPlot.Faithful`
* `Diagram.data`: the dots of a plot, read back
* `plotProblems`: the layout checks of plane figures as a plot needs them
* `CellPlot`, `CellPlot.draw`, `CellPlot.figure`, `CellPlot.Faithful`, `ulamWalk`, `ulamCells`

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
`vlo` and the highest `vhi` the axes show, the first tick `xlo` of the index axis, and the steps of
the ticks. -/
structure SeqLayout where
  /-- World units per unit of the index. -/
  sx : Rat
  /-- World units per unit of value. -/
  sy : Rat
  /-- The lowest value shown. -/
  vlo : Rat
  /-- The highest value shown. -/
  vhi : Rat
  /-- The index of the first tick of the index axis (a multiple of `xstep`, at most `lo`). -/
  xlo : Nat
  /-- The step of the ticks of the index axis. -/
  xstep : Nat
  /-- The step of the ticks of the value axis. -/
  ystep : Rat

namespace SeqPlot

/-- The most indices a plot draws. -/
def maxIndices : Nat := 2000

/-- The most sequences and curves a plot draws. -/
def maxSeries : Nat := 6

/-- The most characters of a sequence's or a curve's name. -/
def maxNameLength : Nat := 80

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
step), the index axis from the multiple `xlo` of its step at or below `lo` to `hi`, three units
long, and the value axis two units high. -/
def layout (P : SeqPlot) : SeqLayout :=
  let vs := P.values
  let lo := vs.foldl min 0
  let hi := vs.foldl max 0
  let ystep := niceStep (hi - lo)
  let vlo := ystep * ((lo / ystep).floor : Rat)
  let vhi := ystep * ((hi / ystep).ceil : Rat)
  let xstep := max 1 (niceStep (max 1 ((P.hi : Rat) - P.lo))).ceil.toNat
  let xlo := xstep * (P.lo / xstep)
  let span : Rat := max 1 ((P.hi : Rat) - xlo)
  { sx := 3 / span, sy := 2 / max 1 (vhi - vlo), vlo, vhi, xlo, xstep, ystep }

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

/-- The indices at the ticks of the index axis: `xlo, xlo + xstep, …` up to `hi`. -/
def xticks (P : SeqPlot) (L : SeqLayout) : List Nat :=
  (List.range ((P.hi - L.xlo) / L.xstep + 1)).map fun i => L.xlo + i * L.xstep

/-- The number of ticks of the value axis. -/
def tickCount (L : SeqLayout) : Nat := ((L.vhi - L.vlo) / L.ystep).floor.toNat + 1

/-- The values at the ticks of the value axis. -/
def yticks (L : SeqLayout) : List Rat :=
  (List.range (tickCount L)).map fun (i : Nat) => L.vlo + i * L.ystep

/-- The names of the sequences and curves, in the order of their colours. -/
def names (P : SeqPlot) : List String := P.series.map (·.1) ++ P.curves.map (·.1)

/-- The abscissa of the value axis: a tenth of a unit left of the first tick of the index axis, so
that no point of the plot lies on it. -/
def axisX (L : SeqLayout) : Rat := L.sx * L.xlo - 1 / 10

/-- The ordinate of the index axis: a tenth of a unit below the lowest value shown, so that no
point of the plot lies on it. -/
def axisY (L : SeqLayout) : Rat := L.sy * L.vlo - 1 / 10

/-- The height of the legend's line `i`, above the value axis. -/
def legendY (P : SeqPlot) (L : SeqLayout) (i : Nat) : Rat :=
  L.sy * L.vhi + (3 : Rat) / 10 * ((P.names.length : Rat) - i)

/-- The decorations with their inks, in order:

* the index axis (`axis 0`) from the value axis to `hi` and the value axis (`axis 1`) up to the
  highest value shown, faint;
* their ticks, faint guides;
* the legend's samples, guides in the colour of each sequence (a dot) and of each curve (a short
  line), at the top left;
* the ticks' labels (`note 0` below the index axis, `note 1` left of the value axis), the legend's
  names (`note 2`, right of their samples) and the name `n` of the index axis (`note 3`, at its
  right end), in the ink. -/
def decorations (P : SeqPlot) (L : SeqLayout) : List (Part × Shape × Ink) :=
  let x0 := axisX L
  let y0 := axisY L
  let t : Rat := 1 / 20
  let xe := L.sx * P.hi + 1 / 10
  [(.axis 0, .segment (x0, y0) (xe, y0), .faint),
    (.axis 1, .segment (x0, y0) (x0, L.sy * L.vhi), .faint)] ++
    (P.xticks L).map (fun n => (.guide, .segment (L.sx * n, y0) (L.sx * n, y0 - t), .faint)) ++
    (yticks L).map (fun v => (.guide, .segment (x0, L.sy * v) (x0 - t, L.sy * v), .faint)) ++
    P.names.zipIdx.map (fun (_, i) =>
      (.guide, if i < P.series.length then .dot (x0 + 1 / 10, P.legendY L i)
        else .segment (x0, P.legendY L i) (x0 + 1 / 5, P.legendY L i), .series i false)) ++
    (P.xticks L).map (fun n => (.note 0, .text (toString n) (L.sx * n, y0 - t) .below, .ink)) ++
    (yticks L).map (fun v => (.note 1, .text (tickText v) (x0 - t, L.sy * v) .left, .ink)) ++
    P.names.zipIdx.map (fun (s, i) =>
      (.note 2, .text s (x0 + 1 / 4, P.legendY L i) .right, .ink)) ++
    [(.note 3, .text "n" (xe, y0) .right, .ink)]

/-- The marks of the decorations. -/
def decorationMarks (P : SeqPlot) (L : SeqLayout) : List Mark :=
  (P.decorations L).map fun (p, s, i) => { part := p, shape := s, ink := i }

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

/-- Every decoration's part is a decoration's. -/
theorem decorations_all (P : SeqPlot) (L : SeqLayout) :
    (P.decorations L).all (·.1.isDecoration) = true := by
  simp [decorations, List.all_map, Part.isDecoration, Function.comp_def]

/-- Every mark of the decorations is an axis, a guide or a note. -/
theorem isDecoration_of_mem_decorationMarks {P : SeqPlot} {L : SeqLayout} {m : Mark}
    (h : m ∈ P.decorationMarks L) : m.part = .guide ∨ (∃ k, m.part = .axis k) ∨
      ∃ k, m.part = .note k := by
  simp only [decorationMarks, List.mem_map] at h
  obtain ⟨⟨p, s, i⟩, hp, rfl⟩ := h
  have := List.all_eq_true.1 (P.decorations_all L) _ hp
  cases p <;> simp_all [Part.isDecoration]

/-- The plot is faithful at every layout. -/
theorem draw_faithful (P : SeqPlot) (L : SeqLayout) : P.Faithful L (P.draw L) := by
  have hD := @isDatum_of_mem_dataMarks P L
  have hC := @isCurve_of_mem_curveMarks P L
  have hN := @isDecoration_of_mem_decorationMarks P L
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Diagram.data, draw, List.filterMap_append]
    rw [(List.filterMap_eq_nil_iff (l := P.decorationMarks L)).2 fun m hm => by
        rcases hN hm with h | ⟨k, h⟩ | ⟨k, h⟩ <;> simp [h],
      (List.filterMap_eq_nil_iff (l := P.curveMarks L)).2 fun m hm => by
        obtain ⟨j, h⟩ := hC hm; simp [h]]
    simp [dataMarks, dataTriples, List.filterMap_flatMap, List.filterMap_map, Function.comp_def]
  · simp only [Diagram.marksWhere, draw, List.filter_append]
    rw [(List.filter_eq_nil_iff (l := P.decorationMarks L)).2 fun m hm => by
        rcases hN hm with h | ⟨k, h⟩ | ⟨k, h⟩ <;> simp [h, Part.isDatum],
      (List.filter_eq_nil_iff (l := P.curveMarks L)).2 fun m hm => by
        obtain ⟨j, h⟩ := hC hm; simp [h, Part.isDatum],
      (List.filter_eq_self (l := P.dataMarks L)).2 fun m hm => by
        obtain ⟨k, n, h⟩ := hD hm; simp [h, Part.isDatum]]
    simp
  · simp only [Diagram.marksWhere, draw, List.filter_append]
    rw [(List.filter_eq_nil_iff (l := P.decorationMarks L)).2 fun m hm => by
        rcases hN hm with h | ⟨k, h⟩ | ⟨k, h⟩ <;> simp [h, Part.isCurve],
      (List.filter_eq_self (l := P.curveMarks L)).2 fun m hm => by
        obtain ⟨j, h⟩ := hC hm; simp [h, Part.isCurve],
      (List.filter_eq_nil_iff (l := P.dataMarks L)).2 fun m hm => by
        obtain ⟨k, n, h⟩ := hD hm; simp [h, Part.isCurve]]
    simp
  · simp only [Diagram.marksWhere, draw, List.filter_append]
    rw [(List.filter_eq_self (l := P.decorationMarks L)).2 fun m hm => by
        rcases hN hm with h | ⟨k, h⟩ | ⟨k, h⟩ <;> simp [h, Part.isDecoration],
      (List.filter_eq_nil_iff (l := P.curveMarks L)).2 fun m hm => by
        obtain ⟨j, h⟩ := hC hm; simp [h, Part.isDecoration],
      (List.filter_eq_nil_iff (l := P.dataMarks L)).2 fun m hm => by
        obtain ⟨k, n, h⟩ := hD hm; simp [h, Part.isDecoration]]
    simp
  · simp only [draw, List.all_append, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true]
    refine ⟨⟨fun m hm => ?_, fun m hm => ?_⟩, fun m hm => ?_⟩
    · rcases hN hm with h | ⟨k, h⟩ | ⟨k, h⟩ <;> simp [h, Part.isDecoration]
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

/-- The radius in pixels of the points of a plot of `count` indices on the page: `135 / count`,
between `1` and `3`, so that, up to 140 indices, neighbours keep a gap of more than half their
width between them (the page is 560 pixels wide and the index axis about 450 of them, about
`450 / count` from one index to the next). -/
def dotRadiusFor (count : Nat) : Float := min 3 (max 1 (135 / count.toFloat))

/-- The most ticks of the value axis: values too large for the steps of `niceStep` would need
more. -/
def maxTicks : Nat := 20

/-- The caps: at most `maxIndices` indices, `maxSeries` sequences and curves, a range that is not
empty, names of at most `maxNameLength` characters, and at most `maxTicks` ticks on the value
axis (checked last, after the others have bounded the work of the layout). -/
def withinCaps (P : SeqPlot) : Bool :=
  P.lo ≤ P.hi && P.hi + 1 - P.lo ≤ maxIndices && P.series.length + P.curves.length ≤ maxSeries &&
    P.names.all (·.length ≤ maxNameLength) && tickCount P.layout ≤ maxTicks

/-- The plot at its layout, or a note beyond the caps (`withinCaps`). -/
def figure (P : SeqPlot) : Diagram :=
  Diagram.capped (P.withinCaps)
    s!"a plot of {P.hi + 1 - P.lo} indices and {P.series.length + P.curves.length} series: \
      too many to draw" fun _ =>
    { P.draw P.layout with width := 560, dotRadius := some (dotRadiusFor (P.hi + 1 - P.lo)) }

/-- Within the caps the plot is drawn faithfully by `figure`. -/
theorem builder_faithful (P : SeqPlot) (h : P.withinCaps = true) :
    P.Faithful P.layout P.figure := by
  have e : P.figure.marks = (P.draw P.layout).marks := by
    simp only [figure, Diagram.capped, h, ite_true]
  have hd := P.draw_faithful P.layout
  unfold Faithful Diagram.data Diagram.marksWhere at hd ⊢
  rw [e]
  exact hd

end SeqPlot

/-! ### The layout checks of a plot -/

/-- The radius of a leaf's marker without its ring (`Item.size`, or the style's radius). -/
def discRadius (e : Plane.Env) (lf : Plane.Leaf) : Float := lf.look.size.getD e.ps.markerRadius

/-- Whether a leaf is a point of a plotted sequence (its title is `sequence k at n`). -/
def isDatumLeaf (lf : Plane.Leaf) : Bool := lf.info.title.startsWith "sequence "

/-- Whether a leaf is a plotted curve (its title is `curve j`). -/
def isCurveLeaf (lf : Plane.Leaf) : Bool := lf.info.title.startsWith "curve "

/-- The problems the layout checks of plane figures find in a figure, with two exceptions for the
points of a plot: two of them may stand closer than markers must in a geometric figure when their
discs do not overlap (in a plot the abscissa tells the indices apart, and a reader can still count
the points), and a point may lie near a comparison curve (a plot's point is read against its axes,
and a point near the curve claims no incidence with it). -/
def plotProblems (fig : Plane.Figure) : Array String :=
  if fig.checks == .ignore then #[] else
  let e := fig.env
  let lv := (fig.autoPlaced).leaves
  (fig.problems.filter fun pr =>
    match pr.kind, pr.items[0]?, pr.items[1]? with
    | .markersTooClose, some i, some j =>
      match lv[i]?, lv[j]? with
      | some a, some b =>
        let apart := match Plane.markerOf e a, Plane.markerOf e b with
          | some (p, _), some (q, _) => (p - q).norm ≥ discRadius e a + discRadius e b
          | _, _ => false
        !(isDatumLeaf a && isDatumLeaf b && apart)
      | _, _ => true
    | .undecidedIncidence, some i, some j =>
      match lv[i]?, lv[j]? with
      | some a, some b => !(isDatumLeaf a && isCurveLeaf b)
      | _, _ => true
    | _, _, _ => true).map (·.message)

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
  /-- Whether a marked cell is filled opaque (`Ink.solid 0`, for cells without text) rather than
  tinted (`Ink.tint 0`). -/
  solid : Bool := false
  /-- The key of a cell drawn with a ring around it (the start of a spiral); none for no ring. -/
  ringed : Option Nat := none
  /-- What a marked cell means, written beside a sample of its fill below the cells (a legend);
  empty for none. -/
  legend : String := ""
  deriving Inhabited

namespace CellPlot

/-- The most cells a plot draws. -/
def maxCells : Nat := 4000

/-- The square of a cell: the unit square at its position, or the square inside it a twelfth of a
unit from its sides for a plot of `solid` cells, a sixteenth for a marked (tinted) cell of a plot
of cells with text, so that neighbouring marked cells stand apart. -/
def box (solid : Bool) (c : NumberCell) : QPoint × QPoint :=
  let e : Rat := if solid then 1 / 12 else if c.marked then 1 / 16 else 0
  (((c.pos.1 : Rat) + e, (c.pos.2 : Rat) + e), ((c.pos.1 : Rat) + 1 - e, (c.pos.2 : Rat) + 1 - e))

/-- The ink of a cell: accent 0, opaque when `solid` and tinted otherwise, when the cell is marked;
the faint ink when it is not. -/
def cellInk (solid : Bool) (c : NumberCell) : Ink :=
  if c.marked then (if solid then .solid 0 else .tint 0) else .faint

/-- The marks of a cell: its square in its ink (`cellInk`), then its text at its centre when it
has one. -/
def cellMarks (solid : Bool) (c : NumberCell) : List Mark :=
  { part := .cell c.key 0, shape := .rect (box solid c).1 (box solid c).2,
    ink := cellInk solid c } ::
  (if c.text.isEmpty then [] else
    let centre : QPoint := ((c.pos.1 : Rat) + 1 / 2, (c.pos.2 : Rat) + 1 / 2)
    [{ part := .entry c.key 0, shape := .text c.text centre .center }])

/-- The marks of the headings. -/
def headingMarks (P : CellPlot) : List Mark :=
  P.headings.zipIdx.map fun ((s, p), i) => { part := .header 0 i, shape := .text s p .center }

/-- The decorations: a ring around the cell `ringed` (accent 1, `note 0`) and, with a legend, a
sample of a marked cell's fill (`note 1`) and the legend's text to its right (`note 2`), a unit
below the lowest cell, at the left of the leftmost. -/
def decorationMarks (P : CellPlot) : List Mark :=
  let ring := match P.ringed.bind (fun k => P.cells.find? (·.key == k)) with
    | some c =>
      let centre : QPoint := ((c.pos.1 : Rat) + 1 / 2, (c.pos.2 : Rat) + 1 / 2)
      [{ part := .note 0, ink := .accent 1, shape := .circle centre (11 / 16) }]
    | none => []
  let x0 : Rat := P.cells.foldl (fun m c => min m c.pos.1) ((P.cells.headD default).pos.1)
  let y0 : Rat := P.cells.foldl (fun m c => min m c.pos.2) ((P.cells.headD default).pos.2)
  let legend := if P.legend.isEmpty then [] else
    let swatch : Shape := .rect (x0 + 1 / 16, y0 - 2 + 1 / 16) (x0 + 15 / 16, y0 - 1 - 1 / 16)
    let fill : Ink := if P.solid then .solid 0 else .tint 0
    [{ part := .note 1, ink := fill, shape := swatch },
     { part := .note 2, shape := .text P.legend (x0 + 5 / 4, y0 - 3 / 2) .right }]
  ring ++ legend

/-- The diagram: the cells (each with its text), then the headings, then the decorations. -/
def draw (P : CellPlot) : Diagram where
  marks := P.cells.flatMap (cellMarks P.solid) ++ P.headingMarks ++ P.decorationMarks

/-- The diagram draws the cells faithfully: its marks of cells and entries are exactly the cells'
(position, colour by mark, text), cell by cell; its headings exactly the plot's; its decorations
(the ring and the legend) exactly the builder's; and nothing else. -/
def Faithful (P : CellPlot) (d : Diagram) : Prop :=
  d.marksWhere (fun p => p.isCell || p.isEntry) = P.cells.flatMap (cellMarks P.solid) ∧
    d.marksWhere Part.isHeader = P.headingMarks ∧
    d.marksWhere Part.isDecoration = P.decorationMarks ∧
    d.marks.all (fun m => m.part.isCell || m.part.isEntry || m.part.isHeader ||
      m.part.isDecoration) = true

instance (P : CellPlot) (d : Diagram) : Decidable (P.Faithful d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Every decoration is a note. -/
theorem note_of_mem_decorationMarks {P : CellPlot} {m : Mark} (h : m ∈ P.decorationMarks) :
    ∃ k, m.part = .note k := by
  unfold decorationMarks at h
  simp only [List.mem_append] at h
  rcases h with h | h
  · split at h <;> simp at h
    exact ⟨0, by rw [h]⟩
  · split at h
    · simp at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩

/-- Every mark of a cell is the cell's square or its text. -/
theorem part_of_mem_cellMarks {solid : Bool} {c : NumberCell} {m : Mark}
    (h : m ∈ cellMarks solid c) :
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
  have hC : ∀ m ∈ P.cells.flatMap (cellMarks P.solid), m.part.isCell = true ∨ m.part.isEntry = true := by
    intro m hm
    obtain ⟨c, -, hm⟩ := List.mem_flatMap.1 hm
    rcases part_of_mem_cellMarks hm with h | h <;> simp [h, Part.isCell, Part.isEntry]
  have hH : ∀ m ∈ P.headingMarks, ∃ i, m.part = .header 0 i := by
    intro m hm
    simp only [headingMarks, List.mem_map] at hm
    obtain ⟨_, -, rfl⟩ := hm
    exact ⟨_, rfl⟩
  have hD : ∀ m ∈ P.decorationMarks, ∃ k, m.part = .note k := fun m hm =>
    note_of_mem_decorationMarks hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Diagram.marksWhere, draw, List.filter_append]
    rw [(List.filter_eq_self (l := P.cells.flatMap (cellMarks P.solid))).2 fun m hm => by
        simpa [Bool.or_eq_true] using hC m hm,
      (List.filter_eq_nil_iff (l := P.headingMarks)).2 fun m hm => by
        obtain ⟨i, h⟩ := hH m hm; simp [h, Part.isCell, Part.isEntry],
      (List.filter_eq_nil_iff (l := P.decorationMarks)).2 fun m hm => by
        obtain ⟨k, h⟩ := hD m hm; simp [h, Part.isCell, Part.isEntry]]
    simp
  · simp only [Diagram.marksWhere, draw, List.filter_append]
    rw [(List.filter_eq_nil_iff (l := P.cells.flatMap (cellMarks P.solid))).2 fun m hm => by
        rcases hC m hm with h | h <;> cases hp : m.part <;> simp_all [Part.isCell, Part.isEntry,
          Part.isHeader],
      (List.filter_eq_self (l := P.headingMarks)).2 fun m hm => by
        obtain ⟨i, h⟩ := hH m hm; simp [h, Part.isHeader],
      (List.filter_eq_nil_iff (l := P.decorationMarks)).2 fun m hm => by
        obtain ⟨k, h⟩ := hD m hm; simp [h, Part.isHeader]]
    simp
  · simp only [Diagram.marksWhere, draw, List.filter_append]
    rw [(List.filter_eq_nil_iff (l := P.cells.flatMap (cellMarks P.solid))).2 fun m hm => by
        rcases hC m hm with h | h <;> cases hp : m.part <;> simp_all [Part.isCell, Part.isEntry,
          Part.isDecoration],
      (List.filter_eq_nil_iff (l := P.headingMarks)).2 fun m hm => by
        obtain ⟨i, h⟩ := hH m hm; simp [h, Part.isDecoration],
      (List.filter_eq_self (l := P.decorationMarks)).2 fun m hm => by
        obtain ⟨k, h⟩ := hD m hm; simp [h, Part.isDecoration]]
    simp
  · simp only [draw, List.all_append, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true]
    refine ⟨⟨fun m hm => ?_, fun m hm => ?_⟩, fun m hm => ?_⟩
    · rcases hC m hm with h | h <;> simp [h]
    · obtain ⟨i, h⟩ := hH m hm; simp [h, Part.isHeader]
    · obtain ⟨k, h⟩ := hD m hm; simp [h, Part.isDecoration]

/-- In a faithful diagram every cell is drawn as its unit square in the colour of its mark:
accent 0 when the cell is marked, the faint ink otherwise. -/
theorem mem_marked {P : CellPlot} {d : Diagram} (h : P.Faithful d) (c : NumberCell)
    (hc : c ∈ P.cells) :
    { part := .cell c.key 0, shape := .rect (box P.solid c).1 (box P.solid c).2,
      ink := cellInk P.solid c } ∈ d.marks := by
  let m : Mark := { part := .cell c.key 0, shape := .rect (box P.solid c).1 (box P.solid c).2,
                    ink := cellInk P.solid c }
  have hm : m ∈ d.marksWhere (fun p => p.isCell || p.isEntry) := by
    rw [h.1]
    exact List.mem_flatMap.2 ⟨c, hc, by simp [cellMarks, m]⟩
  exact (List.mem_filter.1 hm).1

/-- The most characters of a cell's text or a heading. -/
def maxTextLength : Nat := 40

/-- The caps: at most `maxCells` cells and headings, texts of at most `maxTextLength`
characters. -/
def withinCaps (P : CellPlot) : Bool :=
  P.cells.length ≤ maxCells && P.headings.length ≤ maxCells &&
    P.cells.all (·.text.length ≤ maxTextLength) && P.headings.all (·.1.length ≤ maxTextLength)

/-- The diagram, or a note beyond the caps (`withinCaps`). -/
def figure (P : CellPlot) : Diagram :=
  Diagram.capped P.withinCaps s!"{P.cells.length} cells: too many to draw" fun _ => P.draw

/-- Within the caps the cells are drawn faithfully by `figure`. -/
theorem builder_faithful (P : CellPlot) (h : P.withinCaps = true) :
    P.Faithful P.figure := by
  unfold figure
  rw [Diagram.capped_of h]
  exact P.draw_faithful

end CellPlot

/-- The point one step from `p` in the direction `dir` (`0` right, `1` up, `2` left, `3` down,
taken modulo 4). -/
def spiralStep (dir : Nat) (p : Int × Int) : Int × Int :=
  match dir % 4 with
  | 0 => (p.1 + 1, p.2)
  | 1 => (p.1, p.2 + 1)
  | 2 => (p.1 - 1, p.2)
  | _ => (p.1, p.2 - 1)

/-- The next `n` points of the square spiral after `p`: going `dir`, `k` steps taken of a run of
`run` steps, the run the first (`second = false`) or the second of its length; after two runs of
a length the next is one longer, and each run turns left. Structural in `n`, so that the kernel
can evaluate it. -/
def spiralFrom : Nat → Int × Int → (run k dir : Nat) → (second : Bool) → List (Int × Int)
  | 0, _, _, _, _, _ => []
  | n + 1, p, run, k, dir, second =>
    let q := spiralStep dir p
    if k + 1 < run then q :: spiralFrom n q run (k + 1) dir second
    else if second then q :: spiralFrom n q (run + 1) 0 (dir + 1) false
    else q :: spiralFrom n q run 0 (dir + 1) true

/-- The positions of `1, …, count` on the square spiral: `1` at the origin, then one step right,
one up, two left, two down, three right, … -/
def ulamWalk (count : Nat) : List (Int × Int) :=
  if count = 0 then [] else (0, 0) :: spiralFrom (count - 1) (0, 0) 1 0 0 false

/-- The Ulam spiral of `1, …, count`: cell `n` at its place on the spiral, marked where `p n`,
with its number written when `numbers`. -/
def ulamCells (count : Nat) (p : Nat → Bool) (numbers : Bool := false) : List NumberCell :=
  (ulamWalk count).zipIdx.map fun (pos, i) =>
    { key := i + 1, pos, marked := p (i + 1), text := if numbers then toString (i + 1) else "" }

end PILean.Diagram
