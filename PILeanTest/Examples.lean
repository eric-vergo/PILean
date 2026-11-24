/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILeanTest.Graphs
import PILeanTest.ProvedExamples
import PILeanTest.PlaneExact
import PILean.Trust.Attr

/-!
# The example gallery

Figures specified as Lean values, written to `examples/` by `lake exe pilean-gallery` and
compared with those files by `lake test` (the files are the goldens). Data figures plot values
computed here, from the definitions below; "random" data come from a fixed linear congruential
generator, so they are the same on every run.
-/

namespace PILeanTest.Examples

open PILean PILean.Plot

/-- The number of primes up to `n` (trial division; `n` is small here). -/
def primeCount (n : Nat) : Nat :=
  ((List.range (n + 1)).filter fun k =>
    k ≥ 2 && (List.range (k.sqrt + 1)).all fun d => d < 2 || k % d != 0).length

/-- The number of steps of the Collatz map `n ↦ n/2` (even) or `3n + 1` (odd) that bring `n` to
1, with at most `fuel` steps. -/
def collatzSteps (n : Nat) (fuel : Nat := 1000) : Nat := Id.run do
  let mut m := n
  let mut k := 0
  for _ in [0:fuel] do
    if m ≤ 1 then break
    m := if m % 2 == 0 then m / 2 else 3 * m + 1
    k := k + 1
  return k

/-- The constant π. -/
def pi : Float := 3.141592653589793

/-- `n` uniform numbers in `[0, 1)` from a linear congruential generator with seed `seed`
(Knuth's MMIX constants). -/
def uniforms (seed n : Nat) : Array Float := Id.run do
  let mut s : UInt64 := seed.toUInt64
  let mut out := #[]
  for _ in [0:n] do
    s := s * 6364136223846793005 + 1442695040888963407
    out := out.push ((s >>> 11).toNat.toFloat / 9007199254740992.0)
  return out

/-- `n` approximately normal numbers (the sum of twelve uniforms, less six), scaled by `sd` and
moved to `mean`. -/
def normals (seed n : Nat) (mean : Float := 0) (sd : Float := 1) : Array Float :=
  let u := uniforms seed (12 * n)
  (List.range n).toArray.map fun i =>
    let s := (List.range 12).foldl (fun acc j => acc + (u[12 * i + j]?).getD 0) 0
    mean + sd * (s - 6)

/-- Two trigonometric functions and the cardinal sine on `[-2π, 2π]`. -/
@[figure illustration]
def functions : Figure where
  title := "Trigonometric functions"
  panels := #[{
      x := { label := "x", domain := some (-2 * pi, 2 * pi) },
      y := { label := "y", domain := some (-1.25, 1.25) },
      series := #[.function "sin x" Float.sin (-2 * pi) (2 * pi),
      .function "cos x" Float.cos (-2 * pi) (2 * pi),
      .function "sin x / x" (fun x => if x == 0 then 1 else x.sin / x) (-2 * pi) (2 * pi)] }]

/-- The prime-counting function against `n / ln n`. -/
def primes : Figure where
  title := "Counting primes"
  panels := #[{
      x := { label := "n" }, y := { label := "number of primes up to n" },
      series := #[.step "π(n)" ((List.range 101).toArray.map fun i =>
        ⟨(10 * i).toFloat, (primeCount (10 * i)).toFloat⟩),
      .function "n / ln n" (fun x => x / x.log) 3 1000 (dash := #[5, 4])] }]

/-- Collatz stopping times of 1 to 40, as a data line with markers. -/
def collatz : Figure where
  title := "Collatz stopping times"
  panels := #[{
      x := { label := "n" }, y := { label := "steps to reach 1" },
      series := #[.line "steps" ((List.range 40).toArray.map fun i =>
      ⟨(i + 1).toFloat, (collatzSteps (i + 1)).toFloat⟩) (markers := true)],
      notes := #[.point ⟨27, (collatzSteps 27).toFloat⟩ "27 takes 111 steps"] }]

/-- Pairs of numbers as points. -/
def pairs (a b : Array Float) : Array Point := (a.zip b).map fun (x, y) => ⟨x, y⟩

/-- Two clusters of points. -/
def scatter : Figure where
  title := "Two clusters"
  panels := #[{
      x := { label := "first measurement" }, y := { label := "second measurement" },
      series := #[.scatter "group A" (pairs (normals 1 80 2 0.7) (normals 2 80 3 0.5)),
      .scatter "group B" (pairs (normals 3 80 4.5 0.6) (normals 4 80 1.5 0.6))] }]

/-- The times of the band figure. -/
def bandXs : Array Float := (List.range 61).toArray.map fun i => i.toFloat / 6

/-- The middle line of the band figure. -/
def bandMid : Array Float := bandXs.map fun x => 2 + x.sin + 0.15 * x

/-- A smoothed series with its band, and an area. -/
def bands : Figure where
  title := "Mean and spread"
  panels := #[{
      x := { label := "time" }, y := { label := "value" },
      series := #[.band "mean ± spread" bandXs
        (bandMid.mapIdx fun i m => m - 0.4 - 0.05 * i.toFloat / 6)
        (bandMid.mapIdx fun i m => m + 0.4 + 0.05 * i.toFloat / 6) (some bandMid),
      .area "baseline" (bandXs.map fun x => ⟨x, 0.6 + 0.3 * (x / 2).cos⟩)],
      notes := #[.hline 3 "threshold"] }]

/-- Grouped bars. -/
def groupedBars : Figure where
  title := "Grouped bars"
  panels := #[{
      x := { label := "day" }, y := { label := "count" },
      series := #[.bars #["Mon", "Tue", "Wed", "Thu", "Fri"]
      #[("north", #[12, 15, 9, 17, 14]), ("south", #[8, 11, 13, 10, 16]),
        ("east", #[5, 7, 6, 9, 8])]] }]

/-- Stacked bars, with a negative part. -/
def stackedBars : Figure where
  title := "Stacked bars"
  panels := #[{
      x := { label := "quarter" }, y := { label := "balance" },
      series := #[.bars #["Q1", "Q2", "Q3", "Q4"]
      #[("income", #[30, 34, 28, 40]), ("grants", #[10, 8, 12, 9]),
        ("costs", #[-22, -25, -20, -27])] (stacked := true)] }]

/-- A histogram of 2000 approximately normal numbers. -/
def histogram : Figure where
  title := "A histogram"
  panels := #[{
      x := { label := "value" }, y := { label := "count" },
      series := #[.histogram "samples" (normals 7 2000)] }]

/-- Functions with poles and a jump, drawn without lines across them. -/
def poles : Figure where
  title := "Poles and jumps"
  panels := #[{
      x := { label := "x", domain := some (-2 * pi, 2 * pi) },
      y := { label := "y", domain := some (-4, 4) },
      series := #[.function "tan x" Float.tan (-2 * pi) (2 * pi),
      .function "1 / x" (fun x => 1 / x) (-2 * pi) (2 * pi),
      .function "⌊x⌋ / 2" (fun x => x.floor / 2) (-2 * pi) (2 * pi)] }]

/-- The doses of the error-bar figure. -/
def doses : Array Float := #[1, 2, 3, 4, 5, 6, 7, 8]

/-- Measurements with error bars and a fitted line. -/
def errors : Figure where
  title := "Measurements with error bars"
  panels := #[{
      x := { label := "dose" }, y := { label := "response" },
      series := #[.function "fit" (fun x => 0.8 + 0.55 * x) 0.5 8.5 (dash := #[5, 4]),
      .errorBars "measured"
        (doses.mapIdx fun i x => ⟨x, 0.8 + 0.55 * x + ((normals 11 8 0 0.35)[i]?).getD 0⟩)
        (doses.mapIdx fun i _ => (0.3 + 0.04 * i.toFloat, 0.3 + 0.05 * i.toFloat))] }]

/-- `n!` for the integer part of `x`. -/
def factorial (x : Float) : Float :=
  (List.range x.floor.toUInt64.toNat).foldl (fun acc k => acc * (k + 1).toFloat) 1

/-- Growth rates on a logarithmic axis. -/
def growth : Figure where
  title := "Growth on a logarithmic axis"
  panels := #[{
      x := { label := "n" }, y := { label := "value", scale := .log },
      series := #[
      .line "n³" ((List.range 20).toArray.map fun i => ⟨(i + 1).toFloat, (i + 1).toFloat ^ 3⟩)
        (markers := true),
      .line "2ⁿ" ((List.range 20).toArray.map fun i =>
        ⟨(i + 1).toFloat, (2 : Float) ^ (i + 1).toFloat⟩) (markers := true),
      .step "n!" ((List.range 20).toArray.map fun i =>
        ⟨(i + 1).toFloat, factorial (i + 1).toFloat⟩)] }]

/-- Four panels sharing their axes. -/
def smallMultiples : Figure where
  title := "Small multiples with shared axes"
  width := 720
  height := 480
  columns := 2
  shareX := true
  shareY := true
  legend := false
  panels := #[1, 2, 3, 4].map fun (k : Nat) =>
    { title := s!"harmonic {k}", x := { label := "t" }, y := { label := "amplitude" },
      series := #[.function s!"sin {k}t" (fun t => (k.toFloat * t).sin / k.toFloat) 0 (2 * pi)] }

/-- Data that does not fit: an empty panel, a constant series, huge values and non-finite
points. -/
def awkward : Figure where
  title := "Awkward data"
  width := 720
  height := 440
  columns := 2
  legend := false
  panels := #[
    { title := "no data", x := { label := "x" }, y := { label := "y" },
      series := #[.line "nothing" #[]] },
    { title := "constant", x := { label := "i" }, y := { label := "value" },
      series := #[.line "flat" ((List.range 10).toArray.map fun i =>
        ⟨i.toFloat, 5⟩) (markers := true)] },
    { title := "huge values", x := { label := "i" }, y := { label := "value" },
      series := #[.line "big" ((List.range 10).toArray.map fun i =>
        ⟨i.toFloat, 1e9 * (i.toFloat + 1)⟩)] },
    { title := "gaps (NaN, ∞)", x := { label := "i" }, y := { label := "sin(i/3)" },
      series := #[.line "broken" ((List.range 21).toArray.map fun i =>
        ⟨i.toFloat, if i == 7 then 0 / 0 else if i == 14 then 1 / 0 else (i.toFloat / 3).sin⟩)
        (markers := true)] }]

/-- A unit circle and its inscribed regular hexagon on equal axes, with a shaded horizontal band
(`|y| ≤ 1/2`) and a vertical band (`x ≥ 1/2`). -/
def equalAxes : Figure where
  title := "Equal axes and shaded bands"
  panels := #[{
      x := { label := "x", domain := some (-1.5, 1.5) },
      y := { label := "y", domain := some (-1.2, 1.2) },
      equalAspect := true,
      series := #[.line "unit circle" ((List.range 97).toArray.map fun i =>
            let a := 2 * pi * i.toFloat / 96
            ⟨a.cos, a.sin⟩),
        .line "hexagon" ((List.range 7).toArray.map fun i =>
            let a := 2 * pi * i.toFloat / 6
            ⟨a.cos, a.sin⟩) (dash := #[5, 4])],
      notes := #[.hband (-0.5) 0.5 "|y| ≤ 1/2", .vband 0.5 1.5 "x ≥ 1/2"] }]

/-- A figure in the dark style. -/
def dark (fig : Figure) : Figure := { fig with style := Style.dark }

/-- The figures of the gallery by name. -/
def figures : Array (String × Figure) :=
  #[("function-plot", functions), ("primes-step-plot", primes),
    ("collatz-data-plot", collatz), ("scatter-plot", scatter), ("band-area-plot", bands),
    ("grouped-bars", groupedBars), ("stacked-bars", stackedBars), ("histogram", histogram),
    ("poles", poles), ("error-bars", errors), ("log-axis", growth),
    ("small-multiples", smallMultiples), ("awkward-data", awkward), ("equal-axes", equalAxes),
    ("proved-function", ProvedExamples.provedFunction), ("proved-data", ProvedExamples.provedData)]

/-- The gallery: file name and figure; each figure light and dark. -/
def gallery : Array (String × Figure) :=
  figures.map (fun (n, f) => (n ++ ".svg", f)) ++
    figures.map (fun (n, f) => (n ++ "-dark.svg", dark f))

/-! ### Graphs -/

namespace GraphFigures

open PILean.Graph

/-- The modules of a small compiler, which import each other: a directed graph with two
clusters and a labelled edge. -/
@[figure illustration]
def compiler : PILean.Graph :=
  let names := #["Main", "Cli", "Config", "Log", "Parser", "Lexer", "Ast", "Error", "Eval",
    "Check", "Types", "Env", "Value", "Util", "Pretty"]
  let el := fun (a b : Nat) (l : String) => ({ src := a, dst := b, label := l } : Graph.Edge)
  let e := fun (a b : Nat) => el a b ""
  { nodes := names.map fun s => { label := s },
    edges := #[e 0 1, e 0 4, e 0 8, e 1 2, e 1 3, el 4 5 "tokens", e 4 6, e 4 7, e 8 9, e 8 11,
      e 8 12, e 9 10, e 9 11, e 9 6, e 10 12, e 11 12, e 2 13, e 3 13, e 5 13, e 7 13,
      e 14 6, e 0 14, e 12 13],
    clusters := #[{ name := "Front end", members := #[4, 5, 6, 7, 14] },
      { name := "Back end", members := #[8, 9, 10, 11, 12] }] }

/-- A module graph of 120 nodes: each depends on one or two of the few before it, a few cycles. -/
def modules : PILean.Graph := PILeanTest.Graphs.moduleGraph 5 120 (near := 8) (far := false)

/-- A small undirected graph: a ring of seven nodes with chords. -/
def ring : PILean.Graph :=
  Graph.ofNames #["a", "b", "c", "d", "e", "f", "g"]
    [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 0), (0, 3), (1, 5), (2, 6)]
    (directed := false)

/-- A binary tree of depth three, laid out as a tree. -/
def tree : PILean.Graph :=
  Graph.ofPairs [(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6), (3, 7), (3, 8), (6, 9)]

end GraphFigures

namespace GraphFigures

/-- A small graph to be drawn at given positions: a hub, a ring of four, and an edge that would
pass through the hub. -/
def fixedGraph : PILean.Graph :=
  PILean.Graph.ofNames #["hub", "north", "east", "south", "west"]
    [(1, 0), (2, 0), (3, 0), (4, 0), (1, 3), (4, 2)]

/-- The positions of `fixedGraph` (world coordinates, `y` up). -/
def fixedPositions : Array Point := #[⟨0, 0⟩, ⟨0, 1⟩, ⟨1.2, 0⟩, ⟨0, -1⟩, ⟨-1.2, 0⟩]

end GraphFigures

/-- A graph figure: how to lay it out in a style, and the scale of its PNG. -/
structure GraphEntry where
  /-- The file name without extension. -/
  name : String
  /-- The layout in a style. -/
  layout : Style → PILean.Graph.Layout
  /-- The scale of the PNG relative to the SVG. -/
  scale : Float := 1

/-- The graph figures by name. -/
def graphEntries : Array GraphEntry :=
  #[{ name := "graph-compiler", layout := fun st => GraphFigures.compiler.layout {} st },
    { name := "graph-modules", layout := fun st => GraphFigures.modules.layout {} st,
      scale := 0.75 },
    { name := "graph-compiler-bundled", layout := fun st =>
        GraphFigures.compiler.layout { routing := .bundled } st },
    { name := "graph-modules-bundled", layout := fun st =>
        GraphFigures.modules.layout { routing := .bundled } st, scale := 0.75 },
    { name := "graph-ring", layout := fun st => GraphFigures.ring.circularLayout {} st },
    { name := "graph-tree", layout := fun st => GraphFigures.tree.treeLayout 0 {} st },
    { name := "graph-proved", layout := fun st => ProvedExamples.provedGraph.layout {} st },
    { name := "graph-fixed", layout := fun st =>
        GraphFigures.fixedGraph.fixedLayoutAt GraphFigures.fixedPositions 150 .aroundNodes 6 {}
          st }]

/-- The graph gallery: file stem, entry and style, each entry light and dark. -/
def graphs : Array (String × GraphEntry × Style) :=
  graphEntries.flatMap fun e => #[(e.name, e, Style.light), (e.name ++ "-dark", e, Style.dark)]

/-- The SVG of a graph figure in a style. -/
def GraphEntry.svg (e : GraphEntry) (st : Style) : String := (e.layout st).toSvg st

/-- The PNG of a graph figure in a style (empty when it cannot be written). -/
def GraphEntry.png (e : GraphEntry) (st : Style) : ByteArray :=
  ((e.layout st).toImage st e.scale).writePng.toOption.getD ByteArray.empty

/-! ### Animations -/

namespace Animations

/-- The plot of a travelling wave at time `t`: fixed sampling, so that every frame has the same
path commands and the SVG interpolates them. -/
def waveFigure (t : Float) : Figure :=
  let xs := (List.range 241).toArray.map fun i => i.toFloat / 240 * 4 * pi
  let wave := fun (x : Float) => (x - 2 * pi * t / 2).sin * (-(x / 8)).exp
  { title := "A travelling wave", width := 640, height := 360,
    panels := #[{
      x := { label := "x", domain := some (0, 4 * pi) },
      y := { label := "u(x, t)", domain := some (-1.2, 1.2) },
      series := #[.line "u" (xs.map fun x => ⟨x, wave x⟩),
        .line "envelope" (xs.map fun x => ⟨x, (-(x / 8)).exp⟩) (some ⟨150, 150, 158, 255⟩)
          (dash := #[4, 4])] }] }

/-- A travelling wave, two seconds, looping. -/
@[figure illustration]
def wave : Animation :=
  { width := 640, height := 360, fps := 30, duration := 2, frame := fun t => (waveFigure t).draw,
    text := Style.light.text, fontFamily := Style.light.fontFamily }

/-- Bars growing to their values with an ease-out, holding at the end. -/
def barsFigure (t : Float) : Figure :=
  let p := min 1 (t / 1.4)
  let e := 1 - (1 - p) ^ 3
  let k := 0.02 + 0.98 * e
  { title := "Growing bars", width := 640, height := 360,
    panels := #[{
      x := { label := "day" }, y := { label := "count", domain := some (0, 20) },
      series := #[.bars #["Mon", "Tue", "Wed", "Thu", "Fri"]
        #[("north", #[12, 15, 9, 17, 14].map (· * k)), ("south", #[8, 11, 13, 10, 16].map (· * k))]
        ] }] }

/-- Growing bars, two seconds, played once. -/
def bars : Animation :=
  { width := 640, height := 360, fps := 30, duration := 2, loops := 1,
    frame := fun t => (barsFigure t).draw, text := Style.light.text,
    fontFamily := Style.light.fontFamily }

/-- The small graph building up layer by layer: every element is in every frame and only
opacities change (never reaching 1, so that every frame has the same shape and the SVG
interpolates). A node appears with its layer, an edge just before the node it points into, a
cluster with its first member. -/
def graphBuild : Animation :=
  let st := Style.light
  let l := GraphFigures.compiler.layout {} st
  let sorted := (l.nodes.map (·.box.y0)).qsort (· < ·)
  let distinct := sorted.foldl (fun acc y => if acc.back? == some y then acc else acc.push y) #[]
  let layerOf := fun (i : Nat) =>
    match l.nodes[i]? with
    | some n => (distinct.findIdx? (· == n.box.y0)).getD 0
    | none => 0
  let step : Float := 0.45
  let ramp := fun (t a b : Float) => min 0.999 (max 0 ((t - a) / (b - a)))
  let layers := distinct.size
  { width := l.width.toUInt64.toNat, height := l.height.toUInt64.toNat, fps := 15,
    duration := step * layers.toFloat + 1.2, loops := 1, background := st.background,
    fontFamily := st.fontFamily, text := st.text,
    frame := fun t =>
      let fade := fun (a b : Float) (s : Canvas.Shape) =>
        Canvas.Shape.group #[s] Affine.id (ramp t a b)
      .group (#[.path (Canvas.rect 0 0 l.width l.height) (some (.solid st.background)) none] ++
        l.clusters.map (fun c => fade (step * 0 - 0.2) 0.3 (c.draw st)) ++
        l.edges.map (fun e =>
          let k := (layerOf e.src).max (layerOf e.dst)
          fade (step * k.toFloat - 0.3) (step * k.toFloat + 0.1) (e.draw st)) ++
        l.nodes.map (fun n =>
          let k := layerOf n.index
          fade (step * k.toFloat) (step * k.toFloat + 0.35) (n.draw st))) }

end Animations

/-- The animations of the gallery by name. -/
def animations : Array (String × Animation) :=
  #[("wave", Animations.wave), ("growing-bars", Animations.bars),
    ("graph-build", Animations.graphBuild), ("proved-clock", ProvedExamples.provedClock)]

/-! ### Plane figures -/

namespace PlaneFigures

open PILean.Plane PILean.Exact

/-- `E = ζ - ζ²`, `ζ = e^{2πi/5}`, exact in ℤ[ζ₅]. -/
def chordEnd : Zeta5 := Zeta5.pow 1 - Zeta5.pow 2

/-- The centre `-1` of the left disk. -/
def leftCentre : Zeta5 := Zeta5.ofInt (-1)

/-- The centre `1` of the right disk. -/
def rightCentre : Zeta5 := Zeta5.ofInt 1

/-- `3 + φ` in ℚ(√5), `φ` the golden ratio. -/
def threePlusPhi : QSqrt5 := ⟨7 / 2, 1 / 2⟩

/-- The critical radius `√(3 + φ)`. -/
def critical : SqrtOf QSqrt5 := ⟨threePlusPhi⟩

/-- `ζ - ζ⁴ = 2i sin 72°`, where the two circles cross (and its negative). -/
def crossing : Zeta5 := Zeta5.pow 1 - Zeta5.pow 4

/-! The items of `disks`, each by name, so that its specification can say which is which. -/

namespace Disks

/-- The closed disk of radius `√(3 + φ)` about `-1`, in accent 0, titled by its circle. -/
def leftDisk : Item :=
  Plane.Exact.disk leftCentre critical |>.accent 0 |>.named "the left circle" |>.describedBy
    "the closed disk of radius √(3 + φ) about −1"

/-- The closed disk of radius `√(3 + φ)` about `1`, in accent 1, titled by its circle. -/
def rightDisk : Item :=
  Plane.Exact.disk rightCentre critical |>.accent 1 |>.named "the right circle" |>.describedBy
    "the closed disk of radius √(3 + φ) about 1"

/-- The chord from `-E` to `E`, through `0`. -/
def chord : Item :=
  Plane.Exact.segment (-chordEnd) chordEnd |>.width 3 |>.named "the chord"
    |>.declRef `PILeanTest.Examples.PlaneFigures.chordEnd

/-- The point `E`, on the left circle, in the left disk's colour. -/
def pointE : Item := Plane.Exact.point chordEnd |>.accent 0 |>.incident .on "the left circle"

/-- The point `-E`, on the right circle, in the right disk's colour. -/
def pointNegE : Item :=
  Plane.Exact.point (-chordEnd) |>.accent 1 |>.incident .on "the right circle"

/-- The point `0`, the chord's midpoint. -/
def pointZero : Item := Plane.Exact.point Zeta5.zero |>.incident .on "the chord"

/-- The upper crossing `ζ - ζ⁴` of the circles, as an open ring. -/
def upperCrossing : Item :=
  Plane.Exact.point crossing |>.marker .ring |>.faint |>.incident .on "the left circle"
    |>.incident .on "the right circle"

/-- The lower crossing `-(ζ - ζ⁴)` of the circles, as an open ring. -/
def lowerCrossing : Item :=
  Plane.Exact.point (-crossing) |>.marker .ring |>.faint |>.incident .on "the left circle"
    |>.incident .on "the right circle"

/-- The items, in drawing order. -/
def items : Array Item :=
  #[leftDisk, rightDisk, chord,
    angleMark ⟨-1, 0⟩ (deg 18) (deg 18 - deg 72) (some 46) |>.faint,
    label "72°" (⟨-1, 0⟩ + polar 0.68 (deg (-18))) .right (some 2) |>.size 12,
    upperCrossing, lowerCrossing, pointNegE, pointE,
    Plane.Exact.point leftCentre, Plane.Exact.point rightCentre, pointZero,
    Plane.Exact.label "−E" (-chordEnd) .belowLeft |>.accent 1,
    Plane.Exact.label "E" chordEnd .aboveRight |>.accent 0,
    Plane.Exact.label "−1" leftCentre .auto, Plane.Exact.label "+1" rightCentre .auto,
    Plane.Exact.label "0" Zeta5.zero .below]

end Disks

/-- Two closed disks of the critical radius `√(3 + φ)` about `-1` and `1`; the chord from `-E` to
`E` (`E = ζ - ζ²`) through `0`, `E` on the left circle and in its colour, `-E` on the right one
and in its colour; the circles' crossings `±(ζ - ζ⁴)` as rings; and a mark for a clockwise turn of
72° about the left centre. Every point is exact in ℤ[ζ₅]. -/
@[figure]
def disks : Plane.Figure where
  width := 520
  items := Disks.items
  info := { title := "Two closed disks and the critical chord" }

/-- What `disks` draws, item for item, and why its records and colours are right. The data are
`E = ζ - ζ²`, the crossing `ζ - ζ⁴`, the centres `-1` and `1` and the radius `√(3 + φ)`
(`3 + φ = 7/2 + √5/2`). The items are written out in drawing order, each with its colour (accent,
`faint` or the ink), its title, its marker and the incidences it records: the left disk about
`-1` in accent 0, titled "the left circle", the right one about `1` in accent 1, the chord from
`-E` to `E`, the faint mark of a clockwise turn of 72° about `-1` with its label "72°", the
crossings `±(ζ - ζ⁴)` as faint rings recording being on both circles, `-E` in accent 1 recording
being on the right circle, `E` in accent 0 recording being on the left one, the centres, `0`
recording being on the chord, and the labels "−E", "E", "−1", "+1" and "0", each at its point,
with its placement and colour. The records hold, exactly in ℚ(√5): `|E + 1|² = 3 + φ` and
`|E - 1|² < 3 + φ` (so `E` is on the left circle and inside the right disk), the same for `-E`
with the sides exchanged, `|ζ - ζ⁴ ± 1|² = 3 + φ` for both crossings, and `0` is the midpoint
of `-E` and `E`. Not stated: how the builders and modifiers draw (the library's code, with
`Plane.drawItem_point` and `Plane.Exact.IsPoint.draw` for points), the layout, the fonts, the
style's colour values and the pixels. -/
theorem disks_spec :
    disks.info.title = "Two closed disks and the critical chord" ∧
    chordEnd = Zeta5.pow 1 - Zeta5.pow 2 ∧ crossing = Zeta5.pow 1 - Zeta5.pow 4 ∧
    leftCentre = Zeta5.ofInt (-1) ∧ rightCentre = Zeta5.ofInt 1 ∧ critical = ⟨⟨7 / 2, 1 / 2⟩⟩ ∧
    disks.items = #[
      Plane.Exact.disk leftCentre critical |>.accent 0 |>.named "the left circle"
        |>.describedBy "the closed disk of radius √(3 + φ) about −1",
      Plane.Exact.disk rightCentre critical |>.accent 1 |>.named "the right circle"
        |>.describedBy "the closed disk of radius √(3 + φ) about 1",
      Plane.Exact.segment (-chordEnd) chordEnd |>.width 3 |>.named "the chord"
        |>.declRef `PILeanTest.Examples.PlaneFigures.chordEnd,
      angleMark ⟨-1, 0⟩ (deg 18) (deg 18 - deg 72) (some 46) |>.faint,
      label "72°" (⟨-1, 0⟩ + polar 0.68 (deg (-18))) .right (some 2) |>.size 12,
      Plane.Exact.point crossing |>.marker .ring |>.faint |>.incident .on "the left circle"
        |>.incident .on "the right circle",
      Plane.Exact.point (-crossing) |>.marker .ring |>.faint |>.incident .on "the left circle"
        |>.incident .on "the right circle",
      Plane.Exact.point (-chordEnd) |>.accent 1 |>.incident .on "the right circle",
      Plane.Exact.point chordEnd |>.accent 0 |>.incident .on "the left circle",
      Plane.Exact.point leftCentre, Plane.Exact.point rightCentre,
      Plane.Exact.point Zeta5.zero |>.incident .on "the chord",
      Plane.Exact.label "−E" (-chordEnd) .belowLeft |>.accent 1,
      Plane.Exact.label "E" chordEnd .aboveRight |>.accent 0,
      Plane.Exact.label "−1" leftCentre .auto, Plane.Exact.label "+1" rightCentre .auto,
      Plane.Exact.label "0" Zeta5.zero .below] ∧
    (chordEnd - leftCentre).normSq = critical.radicand ∧
    QSqrt.lt (chordEnd - rightCentre).normSq critical.radicand = true ∧
    (-chordEnd - rightCentre).normSq = critical.radicand ∧
    QSqrt.lt (-chordEnd - leftCentre).normSq critical.radicand = true ∧
    (crossing - leftCentre).normSq = critical.radicand ∧
    (crossing - rightCentre).normSq = critical.radicand ∧
    (-crossing - leftCentre).normSq = critical.radicand ∧
    (-crossing - rightCentre).normSq = critical.radicand ∧
    (-chordEnd + chordEnd == Zeta5.zero) = true := by
  refine ⟨rfl, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  repeat' apply And.intro
  all_goals decide +kernel

figure_links disks disks_spec

/-- Every kind of element: a line and a ray clipped to the frame, a dashed circle, an arc with an
arrowhead, a sector, a regular pentagon, a tinted triangle, a polyline, arrows, angle marks both
ways, and labels on all sides of a point. -/
@[figure illustration]
def constructions : Plane.Figure where
  width := 520
  view := some ⟨-3.2, -2.2, 3.2, 2.2⟩
  items := #[
    line ⟨-3, -1.8⟩ ⟨3, 1.4⟩ |>.faint |>.dashed,
    ray ⟨0, 0⟩ ⟨1, -0.4⟩ |>.faint,
    circle ⟨0, 0⟩ 1.6 |>.faint |>.dashed #[2, 4] |>.width 1.5 |>.named "the circle",
    sector ⟨0, 0⟩ 1.6 (deg 20) (deg 70) |>.accent 2 |>.named "the sector",
    arc ⟨0, 0⟩ 1.9 (deg 100) (deg 170) |>.accent 1 |>.withArrow,
    regularPolygon ⟨-1.9, -1.1⟩ 0.6 5 (pi / 2) |>.accent 0 |>.filled,
    polygon #[⟨1.4, -1.6⟩, ⟨2.8, -1.6⟩, ⟨2.1, -0.4⟩] |>.accent 1 |>.filled,
    polyline #[⟨-2.8, 1.9⟩, ⟨-2.2, 1.3⟩, ⟨-1.6, 1.8⟩, ⟨-1.0, 1.2⟩] |>.accent 0 |>.withArrow,
    arrow ⟨0, 0⟩ (polar 1.6 (deg 45)) |>.width 2.5,
    angleMark ⟨0, 0⟩ 0 (deg 45) none |>.accent 2,
    angleMark ⟨-1.9, -1.1⟩ (deg 90) (deg 18) (some 30) |>.faint,
    point ⟨0, 0⟩, point (polar 1.6 (deg 45)) |>.accent 2 |>.incident .on "the circle"
      |>.incident .on "the sector",
    label "N" ⟨2.3, 1.3⟩ .above |>.size 12, label "S" ⟨2.3, 1.3⟩ .below |>.size 12,
    label "E" ⟨2.3, 1.3⟩ .right |>.size 12, label "W" ⟨2.3, 1.3⟩ .left |>.size 12,
    point ⟨2.3, 1.3⟩ |>.faint,
    label "O" ⟨0, 0⟩ .belowLeft, label "P" (polar 1.6 (deg 45)) .aboveRight |>.accent 2]
  info := { title := "The elements of a plane figure" }

/-- The vertices of a small graph in a window, exact in ℚ(√3)²: the centre and a hexagonal ring of
radius 1, `(cos 60°k, sin 60°k)`. -/
def ringPositions : Array (QSqrt 3 × QSqrt 3) :=
  #[(⟨0, 0⟩, ⟨0, 0⟩), (⟨1, 0⟩, ⟨0, 0⟩), (⟨1 / 2, 0⟩, ⟨0, 1 / 2⟩), (⟨-1 / 2, 0⟩, ⟨0, 1 / 2⟩),
    (⟨-1, 0⟩, ⟨0, 0⟩), (⟨-1 / 2, 0⟩, ⟨0, -1 / 2⟩), (⟨1 / 2, 0⟩, ⟨0, -1 / 2⟩)]

/-- A ring of six around a centre, as a graph. -/
def ringGraph : PILean.Graph :=
  PILean.Graph.ofNames #["0", "a", "b", "c", "d", "e", "f"]
    ([(0, 1), (0, 3), (0, 5)] ++ (List.range 6).map fun k => (k + 1, (k + 1) % 6 + 1))
    (directed := false)

/-- The centre of the window, `(7/20, 0)`. -/
def windowCentre : Rat × Rat := (7 / 20, 0)

/-- The window disk of radius `r` over the ring, each vertex recording where it stands relative to
the window, decided exactly (`Exact.diskIncidence?`; every squared distance here is rational). -/
def windowAt (r : Rat) : Plane.Figure :=
  { width := 420,
    items := #[Plane.Exact.disk windowCentre r |>.accent 0 |>.named "the window"
        |>.describedBy s!"the closed disk of radius {r} about 7/20",
      Plane.Exact.graph ringGraph ringPositions (node := fun i it =>
        match ringPositions[i]?.bind fun p => diskIncidence? p windowCentre r with
        | some rel => it.incident rel "the window"
        | none => it)] }

/-- A graph among other geometry (`Plane.graph`): its vertices at given exact points, a window disk
over some of them, every vertex clear of its boundary and recording on which side it is. -/
@[figure illustration]
def graphInWindow : Plane.Figure :=
  { windowAt 1 with info := { title := "A graph in a window" } }

/-- The window of `graphInWindow` as its radius grows from 6/5 to 9/5 in steps of 1/10: a
parameter axis; each vertex records, exactly, on which side of the window it is. -/
@[figure illustration]
def windowRadius : Explorer :=
  Plane.slider "r" ((List.range 7).toArray.map fun k =>
    (s!"{12 + k}/10", windowAt ((12 + k : Nat) / 10)))

/-- The plane figures of the gallery by name. -/
def figures : Array (String × Plane.Figure) :=
  #[("plane-disks", disks), ("plane-constructions", constructions),
    ("plane-exact", PILeanTest.PlaneExact.zetaSteps), ("plane-graph", graphInWindow),
    ("plane-reference", PILeanTest.PlaneExact.reference)]

end PlaneFigures

/-- A plane figure in its dark twin's style: `Style.dark` with the figure's sizes and roles. -/
def darkPlane (f : Plane.Figure) : Plane.Figure :=
  { f with style := { Style.dark with plane := f.style.plane.withColoursOf PlaneStyle.dark } }

/-- The plane gallery: file name and figure; each figure light and dark, and at its narrow width
when it has one (`-narrow`). -/
def planes : Array (String × Plane.Figure) :=
  let named := PlaneFigures.figures.flatMap fun (n, f) =>
    #[(n, f)] ++ (match f.narrow with | some g => #[(n ++ "-narrow", g)] | none => #[])
  named.map (fun (n, f) => (n ++ ".svg", f)) ++
    named.map (fun (n, f) => (n ++ "-dark.svg", darkPlane f))

/-! ### Raster pictures

Pictures drawn directly with `PILean.Raster.Draw`, written as PNG only. -/

/-- Rounded cards with soft drop shadows (`Draw.dropShadow`, `Path.roundedRect`) on a light and a
dark ground, one card filled with a diagonal gradient: 480 × 200 pixels. -/
def shadowCards : Image :=
  let card := fun (d : Raster.Draw) (x y : Float) (fill : Raster.Paint) (shadow : Rgba) =>
    let p := Path.roundedRect x y 120 120 22
    (d.dropShadow p 0 8 9 shadow).fill p fill
  let gold : Raster.Paint := .linear ⟨300, 40⟩ ⟨420, 160⟩
    #[⟨0, ⟨255, 217, 138, 255⟩⟩, ⟨1, ⟨217, 149, 43, 255⟩⟩]
  let d := Raster.Draw.new 480 200 ⟨236, 236, 238, 255⟩ (space := .srgb)
  let d := d.rectangle 240 0 480 200 (fill := some (.solid ⟨30, 30, 34, 255⟩))
  let d := card d 60 34 (.solid ⟨255, 255, 255, 255⟩) ⟨0, 0, 0, 90⟩
  let d := card d 300 34 gold ⟨0, 0, 0, 160⟩
  d.toImage .rgb

/-- The raster pictures of the gallery by file name. -/
def rasters : Array (String × Image) := #[("shadow-cards.png", shadowCards)]

end PILeanTest.Examples
