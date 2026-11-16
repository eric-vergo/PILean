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

Each theorem names its figure: the plots' theorems say which series the figure holds, the
graph's and the animation's are statements about the figure itself. So a change to a figure
changes what is proved, and a figure that no longer satisfies its theorem does not build.
-/

namespace PILeanTest.ProvedExamples

open PILean PILean.Plot

/-! ### A function plot -/

/-- The cubic `x³ - x`, exact. -/
def cubic (x : Rat) : Rat := x * x * x - x

/-- The parabola `x² - 1`, exact. -/
def parabola (x : Rat) : Rat := x * x - 1

/-- The left end of the interval: `-3/2`. -/
def lo : Rat := -3 / 2

/-- The right end of the interval: `3/2`. -/
def hi : Rat := 3 / 2

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

/-- The step of the grid is `1/8`. -/
theorem gridStep_lo_hi : Exact.gridStep lo hi steps = 1 / 8 := by decide +kernel

/-- The figure `provedFunction` has one panel, whose series are `cubicSeries` and
`parabolaSeries` and no other. The points of each are the exact samples converted one by one, and
nothing else: 25 points, the abscissae the grid `-3/2 + k/8` (`k = 0, …, 24`, from `lo` to `hi`)
in order, the ordinates the exact values of `cubic` (of `parabola`) there; the conversion is
`Exact.toPoint`. The statement is about the points the series hold: nothing is said here about
how they are drawn (`Series.ofExact_draw`, under its hypotheses), about the axes, or about the
curve between two samples. -/
theorem provedFunction_spec :
    provedFunction.panels.map (·.series) = #[#[cubicSeries, parabolaSeries]] ∧
    cubicSeries.points = ((Exact.samples cubic lo hi steps).map Exact.toPoint).toArray ∧
    parabolaSeries.points = ((Exact.samples parabola lo hi steps).map Exact.toPoint).toArray ∧
    cubicSeries.points.size = 25 ∧ parabolaSeries.points.size = 25 ∧
    (Exact.samples cubic lo hi steps).map Prod.fst = Exact.grid lo hi steps ∧
    (Exact.samples parabola lo hi steps).map Prod.fst = Exact.grid lo hi steps ∧
    (∀ p ∈ Exact.samples cubic lo hi steps, p.1 ∈ Exact.grid lo hi steps ∧ p.2 = cubic p.1) ∧
    (∀ p ∈ Exact.samples parabola lo hi steps,
      p.1 ∈ Exact.grid lo hi steps ∧ p.2 = parabola p.1) ∧
    Exact.grid lo hi steps = (List.range 25).map (fun k : Nat => (-3 / 2 + k / 8 : Rat)) ∧
    Exact.gridPoint lo hi steps 0 = lo ∧ Exact.gridPoint lo hi steps steps = hi := by
  refine ⟨by simp [provedFunction], Series.ofExact_points .., Series.ofExact_points ..,
    Series.ofExact_size .., Series.ofExact_size .., Exact.samples_fst .., Exact.samples_fst ..,
    fun p hp => (Exact.mem_samples ..).1 hp, fun p hp => (Exact.mem_samples ..).1 hp, ?_,
    Exact.gridPoint_zero .., Exact.gridPoint_last _ _ _ (by decide)⟩
  refine List.map_congr_left fun k _ => ?_
  rw [Exact.gridPoint, gridStep_lo_hi, lo]
  grind

/-- The statement has content: the grid is not degenerate, its first three points are `-3/2`,
`-11/8` and `-5/4`, and the values at `-3/2` are `-15/8` (the cubic) and `5/4` (the parabola). -/
example : (Exact.grid lo hi steps).take 3 = [-3 / 2, -11 / 8, -5 / 4] ∧ cubic lo = -15 / 8 ∧
    parabola lo = 5 / 4 := by
  decide +kernel

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

/-- The figure `provedData` has one panel, whose series are a line and markers over the list
`residues` and no other. The points of both are the input list converted point for point: as many
points as given, in the given order, none added, dropped or changed (the integers are recovered
from the exact points); floating point enters only through `Exact.toFloat`. -/
theorem provedData_spec :
    provedData.panels.map (·.series) =
        #[#[.ofIntPoints "line" residues, .scatterOfIntPoints "points" residues]] ∧
      (Series.ofIntPoints "line" residues).points =
        (residues.map fun p => Exact.toPoint (Exact.ofIntPair p)).toArray ∧
      (Series.scatterOfIntPoints "points" residues).points =
        (residues.map fun p => Exact.toPoint (Exact.ofIntPair p)).toArray ∧
      (residues.map Exact.ofIntPair).map (fun q => (q.1.num, q.2.num)) = residues ∧
      residues.length = 25 :=
  ⟨by simp [provedData], Series.ofIntPoints_points .., Series.scatterOfIntPoints_points ..,
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
pass is the conversion of the exact rational number `i / 10`, and both the raster frames and the
SVG frames are built from that drawing at that time. -/
theorem provedClock_spec (i : Nat) :
    provedClock.time i = Exact.toFloat (provedClock.exactTime i) ∧
    provedClock.exactTime i = i / 10 ∧
    (∀ h : i < provedClock.frameSeq.frames.size, provedClock.frameSeq.frames[i] =
      (clockFrame (provedClock.time i)).toImage 200 200 Style.light.text ⟨255, 255, 255, 255⟩) ∧
    (∀ (mode : Canvas.TextMode) (h : i < (provedClock.frameTrees mode).size),
      (provedClock.frameTrees mode)[i] =
        Svg.el "g" #[] ((clockFrame (provedClock.time i)).render mode)) :=
  ⟨Animation.time_eq_exactTime .., Animation.exactTime_eq _ i (by decide),
    fun h => Animation.frameSeq_getElem _ i h,
    fun mode h => Animation.frameTrees_getElem _ mode i h⟩

/-- The hypotheses are met: the clock's frame rate is 10, so frame 5 is at half a second. -/
example : provedClock.exactTime 5 = 1 / 2 := by decide +kernel

/-! ### The links from the pictures to their theorems

Each link is checked when this module is built: the theorem is proved from the standard axioms
and its statement mentions the picture or a definition of this module the picture is built
from. Here every statement mentions the picture itself. -/

figure_proves provedFunction provedFunction_spec
figure_proves provedData provedData_spec
figure_proves provedGraph provedGraph_spec
figure_proves provedClock provedClock_spec

/--
error: PILeanTest.ProvedExamples.provedData_spec does not mention
PILeanTest.ProvedExamples.provedClock or a declaration of its module that
PILeanTest.ProvedExamples.provedClock uses directly, so it is not a statement about this figure
-/
#guard_msgs in
figure_proves provedClock provedData_spec

end PILeanTest.ProvedExamples

