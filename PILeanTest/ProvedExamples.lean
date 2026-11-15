/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Trust.Attr

/-!
# Pictures with a proved specification

One picture of each kind whose specification is a theorem about the Lean object it was drawn
from (see `docs/PROOFS.md`):

* `provedFunction`: a function plot. The curve is drawn through the exact samples of the
  functions `cubic` and `parabola` on the grid of 24 steps from `-3/2` to `3/2`
  (`provedFunction_spec`).
* `provedData`: a data plot. The line and the markers are drawn through the integer list
  `residues`, point for point (`provedData_spec`).
* `provedGraph`: a graph. Its nodes are the numbers 1 to 12 and its edges are exactly the pairs
  `a < b` with `a ∣ b`; the layout draws one route for each (`provedGraph_spec`).
* `provedClock`: an animation. Frame `i` is the drawing at the time `i / 10`
  (`provedClock_spec`).

Each theorem is about the same definition that the figure is built from, so changing the figure
changes what is proved.
-/

namespace PILeanTest.ProvedExamples

open PILean PILean.Plot

/-! ### A function plot -/

/-- The cubic `x³ - x`, exact. -/
def cubic (x : Q) : Q := x * x * x - x

/-- The parabola `x² - 1`, exact. -/
def parabola (x : Q) : Q := x * x - Q.ofInt 1

/-- The left end of the interval: `-3/2`. -/
def lo : Q := Q.ofFrac (-3) 2

/-- The right end of the interval: `3/2`. -/
def hi : Q := Q.ofFrac 3 2

/-- The number of steps of the grid. -/
def steps : Nat := 24

/-- The cubic's series: a line through its 25 exact samples. -/
def cubicSeries : Series := .ofExact "x^3 - x" cubic lo hi steps

/-- The parabola's series. -/
def parabolaSeries : Series := .ofExact "x^2 - 1" parabola lo hi steps (dash := #[5, 4])

/-- Two polynomials, plotted from exact samples. -/
@[figure]
def provedFunction : Figure where
  title := "Two polynomials from exact samples"
  panels := #[{
      x := { label := "x" }, y := { label := "y" },
      series := #[cubicSeries, parabolaSeries] }]

/-- The curve of `provedFunction` is the exact samples converted one by one, and nothing else:
25 points, the abscissae the grid `-3/2 + k/8` (`k = 0, …, 24`: from `lo` to `hi` in equal
steps), the ordinates the exact values of `cubic` there; floating point enters only through
`Q.toFloat`. -/
theorem provedFunction_spec :
    cubicSeries.points = ((Q.samples cubic lo hi steps).map Q.toPoint).toArray ∧
    cubicSeries.points.size = 25 ∧
    (∀ p ∈ Q.samples cubic lo hi steps, p.1 ∈ Q.grid lo hi steps ∧ p.2 = cubic p.1) ∧
    Q.Equiv (Q.gridPoint lo hi steps 0) lo ∧ Q.Equiv (Q.gridPoint lo hi steps steps) hi ∧
    (∀ k, Q.Equiv (Q.gridPoint lo hi steps (k + 1) - Q.gridPoint lo hi steps k)
      (Q.gridStep lo hi steps)) :=
  ⟨Series.ofExact_points .., Series.ofExact_size .., fun p hp => (Q.mem_samples ..).1 hp,
    Q.gridPoint_zero .., Q.gridPoint_last _ _ _ (by decide),
    fun k => Q.gridPoint_succ _ _ _ k (by decide)⟩

/-- The hypotheses are met: the step is `1/8` (the grid's denominators are `2 · 2 · 24`). -/
example : Q.Equiv (Q.gridStep lo hi steps) (Q.ofFrac 1 8) := by decide

/-! ### A data plot -/

/-- The data: `k² mod 17`, centred, for `k = 0, …, 24`, as integer pairs. -/
def residues : List (Int × Int) :=
  (List.range 25).map fun (k : Nat) => (Int.ofNat k, Int.ofNat (k * k % 17) - 8)

/-- Quadratic residues modulo 17, drawn as a line and as markers over it. -/
@[figure]
def provedData : Figure where
  title := "Squares modulo 17"
  panels := #[{
      x := { label := "k" }, y := { label := "k^2 mod 17, minus 8" },
      series := #[.ofIntPoints "line" residues, .scatterOfIntPoints "points" residues] }]

/-- The line and the markers of `provedData` are the input list converted point for point: as
many points as given, in the given order, none added, dropped or changed (the integers are
recovered from the exact points); floating point enters only through `Q.toFloat`. -/
theorem provedData_spec :
    (Series.ofIntPoints "line" residues).points =
        (residues.map fun p => Q.toPoint (Q.ofIntPair p)).toArray ∧
      (Series.scatterOfIntPoints "points" residues).points =
        (residues.map fun p => Q.toPoint (Q.ofIntPair p)).toArray ∧
      (residues.map Q.ofIntPair).map (fun q => (q.1.num, q.2.num)) = residues ∧
      residues.length = 25 :=
  ⟨Series.ofIntPoints_points .., Series.scatterOfIntPoints_points ..,
    Series.ofIntPairs_recover _, by simp [residues]⟩

/-- The data are not degenerate: the first three are `(0, -8)`, `(1, -7)`, `(2, -4)`. -/
example : residues.take 3 = [(0, -8), (1, -7), (2, -4)] := by decide +kernel

/-! ### A graph -/

/-- The nodes: the numbers 1 to 12. -/
def numbers : List Nat := (List.range 12).map (· + 1)

/-- Divisibility: `a` is joined to `b` when `a < b` and `a` divides `b`. -/
def properDivisor (a b : Nat) : Bool := a < b && b % a == 0

/-- The numbers 1 to 12 with the relation "is a proper divisor of". -/
@[figure]
def provedGraph : PILean.Graph :=
  Graph.ofRelation numbers properDivisor toString

/-- The graph's nodes are the numbers 1 to 12 (as labels, in order), its edges are exactly the
pairs of positions whose numbers are related, each once, and the layout draws one route for each
of them, in order: route `i` has index `i` and the ends of the `i`-th edge. (A route of an edge
over several layers passes through dummy nodes inside the layout and is still one route.) -/
theorem provedGraph_spec (o : Graph.LayeredOptions) (st : Style) :
    provedGraph.nodes.toList.map (·.label) = numbers.map toString ∧
    (∀ i j, (i, j) ∈ Graph.relationPairs numbers properDivisor ↔
      ∃ a b, numbers[i]? = some a ∧
        numbers[j]? = some b ∧ properDivisor a b = true) ∧
    (Graph.relationPairs numbers properDivisor).Nodup ∧
    (provedGraph.layout o st).edges.toList.map (fun e => (e.index, e.src, e.dst)) =
      (List.range (Graph.relationPairs numbers properDivisor).length).zip
        (Graph.relationPairs numbers properDivisor) := by
  refine ⟨?_, fun i j => Graph.mem_relationPairs .., Graph.relationPairs_nodup .., ?_⟩
  · unfold provedGraph
    exact (Graph.ofRelation_node_labels numbers properDivisor toString true)
  · unfold provedGraph
    exact Graph.ofRelation_layout_edges numbers properDivisor toString true o st

/-- The hypotheses are met: 2 divides 6 (positions 1 and 5), and the graph has 23 edges. -/
example : (1, 5) ∈ Graph.relationPairs numbers properDivisor ∧
    (Graph.relationPairs numbers properDivisor).length = 23 := by
  decide +kernel

/-! ### An animation -/

/-- One frame of the clock: a dot at the angle `2π t` (one turn per second) on a circle. -/
def clockFrame (t : Float) : Canvas.Shape :=
  let a := 2 * 3.141592653589793 * t
  let c : Point := ⟨100 + 70 * a.cos, 100 + 70 * a.sin⟩
  .group #[
    .path (Canvas.circle ⟨100, 100⟩ 70) none (some { ink := ⟨190, 195, 205, 255⟩, width := 2 }),
    .path (Canvas.circle c 12) (some (.solid ⟨41, 98, 255, 255⟩)) none]

/-- A dot going once round a circle: 10 frames per second for one second, played once. -/
@[figure]
def provedClock : Animation :=
  { width := 200, height := 200, fps := 10, duration := 1, loops := 1, frame := clockFrame,
    text := Style.light.text, fontFamily := Style.light.fontFamily }

/-- Frame `i` of the clock is the drawing `clockFrame` at the time `i / 10`: the time the writers
pass is the conversion of the exact fraction with numerator `i` and denominator 10, and both the
raster frames and the SVG frames are built from that drawing at that time. -/
theorem provedClock_spec (i : Nat) :
    provedClock.time i = (provedClock.exactTime i).toFloat ∧
    (provedClock.exactTime i).num = i ∧ (provedClock.exactTime i).den = 10 ∧
    (∀ h : i < provedClock.frameSeq.frames.size, provedClock.frameSeq.frames[i] =
      (clockFrame (provedClock.time i)).toImage 200 200 Style.light.text ⟨255, 255, 255, 255⟩) ∧
    (∀ (mode : Canvas.TextMode) (h : i < (provedClock.frameTrees mode).size),
      (provedClock.frameTrees mode)[i] =
        Svg.el "g" #[] ((clockFrame (provedClock.time i)).render mode)) :=
  ⟨Animation.time_eq_exactTime .., rfl, rfl,
    fun h => Animation.frameSeq_getElem _ i h, fun mode h => Animation.frameTrees_getElem _ mode i h⟩

/-- The hypotheses are met: the clock's frame rate is 10, so frame 5 is at `5/10`. -/
example : (provedClock.exactTime 5).num = 5 ∧ (provedClock.exactTime 5).den = 10 := by
  decide

end PILeanTest.ProvedExamples

#print axioms PILean.Q.gridPoint_equiv
#print axioms PILean.Q.gridPoint_zero
#print axioms PILean.Q.gridPoint_last
#print axioms PILean.Q.gridPoint_succ
#print axioms PILean.Q.mem_samples
#print axioms PILean.Q.samples_fst
#print axioms PILean.Q.samples_length
#print axioms PILean.Plot.runs_map_some
#print axioms PILean.Plot.runs_length
#print axioms PILean.Plot.runs_sublist
#print axioms PILean.Plot.polylinesWith_all
#print axioms PILean.Plot.drawSeries_line_unmarked
#print axioms PILean.Plot.drawSeries_scatter
#print axioms PILean.Plot.drawSeries_scatter_all
#print axioms PILean.Plot.Series.ofExact_points
#print axioms PILean.Plot.Series.ofExact_xs
#print axioms PILean.Plot.Series.ofExact_ys
#print axioms PILean.Plot.Series.ofExact_size
#print axioms PILean.Plot.Series.ofSamples_draw
#print axioms PILean.Plot.Series.ofExact_draw
#print axioms PILean.Plot.Series.scatterOfSamples_draw
#print axioms PILean.Plot.Series.ofIntPairs_recover
#print axioms PILean.Plot.Series.ofIntPoints_points
#print axioms PILean.Graph.mem_relationPairs
#print axioms PILean.Graph.relationPairs_nodup
#print axioms PILean.Graph.ofRelation_node_labels
#print axioms PILean.Graph.ofRelation_edge_pairs
#print axioms PILean.Graph.layout_edge_endpoints
#print axioms PILean.Graph.layout_edges_of_valid
#print axioms PILean.Graph.ofRelation_layout_edges
#print axioms PILean.Graph.ofNames_layout_edges
#print axioms PILean.Animation.time_eq_exactTime
#print axioms PILean.Animation.frameSeq_getElem
#print axioms PILean.Animation.frameTrees_getElem
#print axioms PILeanTest.ProvedExamples.provedFunction_spec
#print axioms PILeanTest.ProvedExamples.provedData_spec
#print axioms PILeanTest.ProvedExamples.provedGraph_spec
#print axioms PILeanTest.ProvedExamples.provedClock_spec
