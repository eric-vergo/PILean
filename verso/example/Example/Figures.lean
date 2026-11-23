/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Trust.Attr

/-!
# The example's figures

Four pictures, each the value of a declaration marked `@[figure]`, each with a theorem about the
Lean object it is drawn from (see PILean's `docs/PROOFS.md`):

* `cubicPlot`: the cubic `x³ − 3x` and its derivative, plotted from exact samples
  (`cubicPlot_spec`);
* `collatzPlot`: the Collatz stopping times of 1 to 40, a line through the computed list
  (`collatzPlot_spec`);
* `divisorGraph`: the divisors of 24 joined by the covering relation of divisibility
  (`divisorGraph_spec`);
* `circleAnimation`: a point going once round the unit circle with its height
  (`circleAnimation_spec`).
-/

namespace Example

open PILean PILean.Plot

/-! ### A function plot -/

/-- The cubic `x³ − 3x`, exact. -/
def cubic (x : Rat) : Rat := x * x * x - 3 * x

/-- Its derivative `3x² − 3`, exact. -/
def cubic' (x : Rat) : Rat := 3 * x * x - 3

/-- The left end of the interval: `-2`. -/
def lo : Rat := -2

/-- The right end of the interval: `2`. -/
def hi : Rat := 2

/-- The number of steps of the grid. -/
def steps : Nat := 32

/-- The cubic's series: a line through its 33 exact samples. -/
def cubicSeries : Series := .ofExact "x³ − 3x" cubic lo hi steps

/-- The derivative's series, dashed. -/
def cubicSeries' : Series := .ofExact "3x² − 3" cubic' lo hi steps (dash := #[5, 4])

/-- The cubic x³ − 3x and its derivative on [−2, 2]. -/
@[figure]
def cubicPlot : Figure where
  title := "The cubic x³ − 3x and its derivative"
  panels := #[{
      x := { label := "x" }, y := { label := "y" },
      series := #[cubicSeries, cubicSeries'] }]

/-- The figure `cubicPlot` has one panel, whose series are `cubicSeries` and `cubicSeries'` and
no other. The points of each are its exact samples converted one by one: 33 points, whose
abscissae are the grid from `-2` to `2` in steps of `1/8` and whose ordinates are the exact
values of `cubic` (of `cubic'`). Nothing is said about the curve between two samples. -/
theorem cubicPlot_spec :
    cubicPlot.panels.map (·.series) = #[#[cubicSeries, cubicSeries']] ∧
    cubicSeries.points = ((Exact.samples cubic lo hi steps).map Exact.toPoint).toArray ∧
    cubicSeries'.points = ((Exact.samples cubic' lo hi steps).map Exact.toPoint).toArray ∧
    cubicSeries.points.size = 33 ∧ cubicSeries'.points.size = 33 ∧
    (∀ p ∈ Exact.samples cubic lo hi steps, p.1 ∈ Exact.grid lo hi steps ∧ p.2 = cubic p.1) ∧
    ∀ p ∈ Exact.samples cubic' lo hi steps, p.1 ∈ Exact.grid lo hi steps ∧ p.2 = cubic' p.1 :=
  ⟨by simp [cubicPlot], Series.ofExact_points .., Series.ofExact_points ..,
    Series.ofExact_size .., Series.ofExact_size ..,
    fun _ hp => (Exact.mem_samples ..).1 hp, fun _ hp => (Exact.mem_samples ..).1 hp⟩

/-- The hypotheses are met: the grid's step is `1/8`. -/
example : Exact.gridStep lo hi steps = 1 / 8 := by decide +kernel

/-! ### A data plot -/

/-- The number of steps the Collatz map takes from `n` to 1, looking at most `fuel` steps ahead
(0 when it does not get there in time). -/
def collatzSteps : (fuel n : Nat) → Nat
  | 0, _ => 0
  | fuel + 1, n =>
    if n ≤ 1 then 0
    else 1 + collatzSteps fuel (if n % 2 == 0 then n / 2 else 3 * n + 1)

/-- The stopping times of 1 to 40, as integer points `(n, steps)`. -/
def collatzData : List (Int × Int) :=
  (List.range 40).map fun k => (Int.ofNat (k + 1), Int.ofNat (collatzSteps 500 (k + 1)))

/-- The Collatz stopping times of 1 to 40. -/
@[figure]
def collatzPlot : Figure where
  title := "Collatz stopping times"
  panels := #[{
      x := { label := "n" }, y := { label := "steps to reach 1" },
      series := #[.ofIntPoints "steps" collatzData,
        .scatterOfIntPoints "n" collatzData] }]

/-- The figure `collatzPlot` has one panel, whose series are a line and markers over
`collatzData` and no other; the points of both are the computed list point for point: none
added, dropped or changed. -/
theorem collatzPlot_spec :
    collatzPlot.panels.map (·.series) =
        #[#[.ofIntPoints "steps" collatzData, .scatterOfIntPoints "n" collatzData]] ∧
      (Series.ofIntPoints "steps" collatzData).points =
        (collatzData.map fun p => Exact.toPoint (Exact.ofIntPair p)).toArray ∧
      (Series.scatterOfIntPoints "n" collatzData).points =
        (collatzData.map fun p => Exact.toPoint (Exact.ofIntPair p)).toArray ∧
      (collatzData.map Exact.ofIntPair).map (fun q => (q.1.num, q.2.num)) = collatzData :=
  ⟨by simp [collatzPlot], Series.ofIntPoints_points .., Series.scatterOfIntPoints_points ..,
    Series.ofIntPairs_recover _⟩

/-- The data are what they should be: 27 takes 111 steps, and 1, 2, 3 take 0, 1 and 7. -/
example : collatzSteps 500 27 = 111 ∧ collatzData.take 3 = [(1, 0), (2, 1), (3, 7)] := by
  decide +kernel

/-! ### A graph of a relation -/

/-- The divisors of 24. -/
def divisors24 : List Nat := [1, 2, 3, 4, 6, 8, 12, 24]

/-- `b` covers `a` in divisibility: `a` is a proper divisor of `b` with no divisor of 24 strictly
between them. -/
def covers (a b : Nat) : Bool :=
  a < b && b % a == 0 &&
    divisors24.all fun c => !(a < c && c < b && c % a == 0 && b % c == 0)

/-- The divisors of 24 ordered by divisibility: an edge for every covering pair. -/
@[figure]
def divisorGraph : PILean.Graph :=
  Graph.ofRelation divisors24 covers toString

/-- The nodes of `divisorGraph` are the divisors of 24, its edges exactly the covering pairs, each
once, and its layout draws one route for each edge, in order. -/
theorem divisorGraph_spec (o : Graph.LayeredOptions) (st : Style) :
    divisorGraph.nodes.toList.map (·.label) = divisors24.map toString ∧
    (∀ i j, (i, j) ∈ Graph.relationPairs divisors24 covers ↔
      ∃ a b, divisors24[i]? = some a ∧ divisors24[j]? = some b ∧ covers a b = true) ∧
    (Graph.relationPairs divisors24 covers).Nodup ∧
    (divisorGraph.layout o st).edges.toList.map (fun e => (e.index, e.src, e.dst)) =
      (List.range (Graph.relationPairs divisors24 covers).length).zip
        (Graph.relationPairs divisors24 covers) := by
  refine ⟨?_, fun i j => Graph.mem_relationPairs .., Graph.relationPairs_nodup .., ?_⟩
  · unfold divisorGraph
    exact Graph.ofRelation_node_labels divisors24 covers toString true
  · unfold divisorGraph
    exact Graph.ofRelation_layout_edges divisors24 covers toString true o st

/-- The relation is not empty: 4 covers 2 (positions 1 and 3), and there are 10 covering pairs. -/
example : (1, 3) ∈ Graph.relationPairs divisors24 covers ∧
    (Graph.relationPairs divisors24 covers).length = 10 := by
  decide +kernel

/-! ### An animation -/

/-- One frame: the unit circle, a point at the angle `2π t` on it, and its height. -/
def circleFrame (t : Float) : Canvas.Shape :=
  let a := 2 * 3.141592653589793 * t
  let c : Point := ⟨120 + 80 * a.cos, 120 - 80 * a.sin⟩
  let ink : Rgba := ⟨41, 98, 255, 255⟩
  .group #[
    .path (Canvas.circle ⟨120, 120⟩ 80) none (some { ink := ⟨190, 195, 205, 255⟩, width := 2 }),
    .path (Path.polyline #[⟨32, 120⟩, ⟨208, 120⟩]) none
      (some { ink := ⟨210, 214, 222, 255⟩, width := 1.5 }),
    .path (Path.polyline #[c, ⟨c.x, 120⟩]) none (some { ink, width := 2, dash := #[4, 3] }),
    .path (Canvas.circle c 9) (some (.solid ink)) none]

/-- A point going once round the unit circle in two seconds, 15 frames a second, with its
height. -/
@[figure]
def circleAnimation : Animation :=
  { width := 240, height := 240, fps := 15, duration := 2, loops := 0, frame := fun t =>
      circleFrame (t / 2), posterTime := some 0.25,
    text := Style.light.text, fontFamily := Style.light.fontFamily }

/-- Frame `i` of `circleAnimation` is the drawing `circleFrame` at half the time `i / 15` (one
turn takes two seconds): the time passed is the conversion of that exact rational number, and the
raster frames are drawn from it. The halving is a floating-point division. -/
theorem circleAnimation_spec (i : Nat) :
    circleAnimation.time i = Exact.toFloat (circleAnimation.exactTime i) ∧
    circleAnimation.exactTime i = i / 15 ∧
    (∀ h : i < circleAnimation.frameSeq.frames.size, circleAnimation.frameSeq.frames[i] =
      (circleFrame (circleAnimation.time i / 2)).toImage 240 240 Style.light.text
        ⟨255, 255, 255, 255⟩) :=
  ⟨Animation.time_eq_exactTime .., Animation.exactTime_eq _ i (by decide),
    fun h => Animation.frameSeq_getElem _ i h⟩

/-- The hypotheses are met: frame 5 is at a third of a second. -/
example : circleAnimation.exactTime 5 = 1 / 3 := by decide +kernel

/-! ### Explorers and an inline figure -/

open PILean.Plane in
/-- A window disk of radius `r` about `1/2` over the five unit steps `ζʲ`, each step's point
naming `cubic` so that it links to it. -/
def windowAt (r : Float) : Plane.Figure :=
  { width := 360,
    items := #[disk ⟨0.5, 0⟩ r |>.accent 0 |>.named "the window"] ++
      ((List.range 5).toArray.map fun j => segment ⟨0, 0⟩ (rootOfUnity 5 j) |>.faint) ++
      ((List.range 5).toArray.map fun j => point (rootOfUnity 5 j)
        |>.named s!"ζ^{j}" |>.declRef ``Example.cubic) }

/-- The window's radius from 0.6 to 1.0: a slider over five frames. -/
@[figure]
def radiusExplorer : Explorer :=
  Plane.slider "r" ((List.range 5).toArray.map fun k =>
    (s!"{6 + k}/10", windowAt (0.6 + k.toFloat / 10))) (poster := 2)

open PILean.Plane in
/-- The point after the first `n` letters of the word `a b a`, each a fifth turn clockwise about
`-1` (`a`) or `1` (`b`). -/
def wordAt (n : Nat) : Plane.Figure :=
  let turn := fun (c : Point) (p : Point) =>
    let a := -(2 * pi / 5)
    let v := p - c
    c + (⟨a.cos * v.x - a.sin * v.y, a.sin * v.x + a.cos * v.y⟩ : Point)
  let letters := [false, true, false].take n
  let pts := letters.foldl (fun acc l => acc.push (turn (if l then ⟨1, 0⟩ else ⟨-1, 0⟩) acc.back!))
    #[(⟨0, 0.3⟩ : Point)]
  { width := 360,
    items := #[circle ⟨-1, 0⟩ 1.5 |>.accent 0, circle ⟨1, 0⟩ 1.5 |>.accent 1,
      polyline pts |>.faint |>.dashed, point pts.back! |>.named "the point"] }

/-- The word `a b a` acting on a point, letter by letter: four steps. -/
@[figure]
def wordExplorer : Explorer :=
  Plane.stepper #[("start", wordAt 0), ("a: a fifth turn about −1", wordAt 1),
    ("b: a fifth turn about 1", wordAt 2), ("a again", wordAt 3)]

/-- The window of radius 0.8, inline, with a narrow rendition. -/
@[figure]
def windowInline : Plane.Figure := { windowAt 0.8 with narrowWidth := some 280 }

/-- A declaration whose name a page must escape: quotes, angle brackets and an ampersand. -/
def «odd "name" <a href=x> & 'more'» : Nat := 0

/-- The window of radius `r` at a width of `w` pixels. -/
def windowSized (r w : Float) : Plane.Figure := { windowAt r with width := w }

/-- Frames of two sizes, each keeping its own view box: a wide and a narrow window. -/
@[figure]
def sizesExplorer : Explorer :=
  Explorer.stepper #[("wide", ExplorerFrame.ofPlane (windowSized 0.8 360)),
    ("narrow", ExplorerFrame.ofPlane (windowSized 0.6 220)),
    ("wide again", ExplorerFrame.ofPlane (windowSized 0.9 360))]

open PILean.Plane in
/-- A picture whose names, ids and links a page must escape. -/
def oddAt (i : Nat) : Plane.Figure :=
  { width := 300,
    items := #[disk ⟨0.5, 0⟩ (0.6 + i.toFloat / 5) |>.accent 0
        |>.named "</title><script>alert(1)</script> & \"q\"" |>.withId "1\" onload=\"x",
      point ⟨0, 0⟩ |>.named "zero <b>" |>.declRef `Example.«odd "name" <a href=x> & 'more'»,
      point ⟨1, 0⟩ |>.named "one" |>.declRef ``Example.cubic] }

/-- Captions, values and an axis name that hold the separators of a frame's label (` · `,
` = `, `Step 1 of 2: `) and markup a page must escape. -/
@[figure]
def oddExplorer : Explorer :=
  Explorer.grid "x = \"<b>\" · y" #["1 · 2 = 3", "</style><script>alert(1)</script>"]
    #["Step 9 of 9: a · b = c", "<img src=x onerror=alert(2)> & ' \""]
    (fun i _ => ExplorerFrame.ofPlane (oddAt i))

/-- The odd picture inline, under a label that starts with a digit. -/
@[figure]
def oddInline : Plane.Figure := oddAt 1

end Example
