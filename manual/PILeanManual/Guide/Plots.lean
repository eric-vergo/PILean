/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILean
import PILean.Trust.Attr
import PILeanVersoManual
import PILeanManual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open PILeanVerso.Manual
open PILeanManual

#doc (Manual) "Plots" =>
%%%
tag := "plots"
%%%

```lean -show
namespace PILeanManual.Plots
open PILean PILean.Plot
```

A plot is a {name}`PILean.Plot.Figure`: a size (640 × 400 pixels by default), a title, a
{name}`PILean.Style`, and {name}`PILean.Plot.Panel`s in a grid of `columns`. A panel has a title,
two {name}`PILean.Plot.Axis` values, a list of {name}`PILean.Plot.Series` drawn in order, and
{name}`PILean.Plot.Annotation`s drawn over them. {name}`PILean.Plot.Figure.draw` lays the figure
out as a drawing on the canvas; {name}`PILean.Plot.Figure.toSvg` and
{name}`PILean.Plot.Figure.toPng` write the same drawing.

The layout: the title, then the legend (drawn when more than one series has a label: one row of
swatches and labels, wrapped when long), then the grid of panels. The room for tick labels and axis
labels comes from measured text; plot areas have whole-pixel edges and one-pixel lines sit on
pixel centres. The data keep {name}`PILean.Style.plotPadding` from the frame at each end, so
curves and markers never touch it.

Every figure on this page is the declaration shown above it, drawn when the manual was built, in
the style of the page's theme.

# Kinds of Series
%%%
tag := "plot-kinds"
%%%

## Lines
%%%
tag := "plot-line"
%%%

{name}`PILean.Plot.Series.line` joins points in order, optionally with `markers` and a `dash`
pattern. Each series takes the next palette colour unless it names one.

```lean
/-- Two sequences as lines. -/
@[figure]
def lines : Figure where
  title := "Lines"
  panels := #[{
    x := { label := "n" }, y := { label := "value" },
    series := #[
      .line "n² / 10" ((List.range 21).toArray.map fun i => ⟨i.toFloat, i.toFloat ^ 2 / 10⟩),
      .line "3n" ((List.range 21).toArray.map fun i => ⟨i.toFloat, 3 * i.toFloat⟩)
        (dash := #[6, 4])] }]
```

:::figure PILeanManual.Plots.lines (alt := "Two lines over n from 0 to 20: a parabola n squared over 10 rising to 40, and a dashed straight line 3n rising to 60.")
:::

## Lines with Markers
%%%
tag := "plot-markers"
%%%

With `markers := true` every point gets a marker with a ring of the page colour. Annotations
mark single points or reference lines.

```lean
/-- The number of steps of the Collatz map that bring `n` to 1 (at most 1000 steps). -/
def collatzSteps (n : Nat) : Nat := Id.run do
  let mut m := n
  let mut k := 0
  for _ in [0:1000] do
    if m ≤ 1 then break
    m := if m % 2 == 0 then m / 2 else 3 * m + 1
    k := k + 1
  return k

/-- Collatz stopping times of 1 to 30, with markers and a labelled point. -/
@[figure]
def collatz : Figure where
  title := "Collatz stopping times"
  panels := #[{
    x := { label := "n" }, y := { label := "steps to reach 1" },
    series := #[.line "steps" ((List.range 30).toArray.map fun i =>
      ⟨(i + 1).toFloat, (collatzSteps (i + 1)).toFloat⟩) (markers := true)],
    notes := #[.point ⟨27, (collatzSteps 27).toFloat⟩ "27 takes 111 steps"] }]
```

:::figure PILeanManual.Plots.collatz (alt := "A jagged line with a marker at each n from 1 to 30, mostly below 25 steps, with a peak labelled '27 takes 111 steps' at n = 27.")
:::

## Scatter
%%%
tag := "plot-scatter"
%%%

{name}`PILean.Plot.Series.scatter` draws points as markers only.

```lean
/-- `n` numbers in `[0, 1)` from a fixed linear congruential generator, the same on every run. -/
def uniforms (seed n : Nat) : Array Float := Id.run do
  let mut s : UInt64 := seed.toUInt64
  let mut out := #[]
  for _ in [0:n] do
    s := s * 6364136223846793005 + 1442695040888963407
    out := out.push ((s >>> 11).toNat.toFloat / 9007199254740992.0)
  return out

/-- Points scattered around a centre. -/
def cloud (seed : Nat) (cx cy r : Float) : Array Point :=
  let u := uniforms seed 120
  (List.range 60).toArray.map fun i =>
    let a := 6.283185307179586 * u[2 * i]!
    let d := r * u[2 * i + 1]!.sqrt
    ⟨cx + d * a.cos, cy + d * a.sin⟩

/-- Two clusters of points. -/
@[figure]
def scatter : Figure where
  title := "Two clusters"
  panels := #[{
    x := { label := "first measurement" }, y := { label := "second measurement" },
    series := #[.scatter "group A" (cloud 1 2 3 1.2), .scatter "group B" (cloud 2 4.5 1.5 1)] }]
```

:::figure PILeanManual.Plots.scatter (alt := "Two round clouds of 60 markers each: group A centred near (2, 3), group B near (4.5, 1.5).")
:::

## Steps
%%%
tag := "plot-step"
%%%

{name}`PILean.Plot.Series.step` draws a step function through its points; the value changes after
each point (`.post`, the default), before it (`.pre`) or half-way (`.mid`).

```lean
/-- The number of primes up to `n`, by trial division. -/
def primeCount (n : Nat) : Nat :=
  ((List.range (n + 1)).filter fun k =>
    k ≥ 2 && (List.range (k.sqrt + 1)).all fun d => d < 2 || k % d != 0).length

/-- The prime-counting function as steps, against `n / ln n`. -/
@[figure]
def primes : Figure where
  title := "Counting primes"
  panels := #[{
    x := { label := "n" }, y := { label := "primes up to n" },
    series := #[
      .step "π(n)" ((List.range 51).toArray.map fun i =>
        ⟨(4 * i).toFloat, (primeCount (4 * i)).toFloat⟩),
      .function "n / ln n" (fun x => x / x.log) 3 200 (dash := #[5, 4])] }]
```

:::figure PILeanManual.Plots.primes (alt := "A staircase counting the primes up to n for n from 0 to 200, reaching 46, with the dashed curve n over ln n below it.")
:::

## Areas
%%%
tag := "plot-area"
%%%

{name}`PILean.Plot.Series.area` fills the region between a line and a `base` value (0 by default),
at the style's {name}`PILean.Style.areaOpacity`, and draws the line.

```lean
/-- A damped oscillation over its baseline. -/
@[figure]
def area : Figure where
  title := "An area"
  panels := #[{
    x := { label := "t" }, y := { label := "signal" },
    series := #[.area "signal" ((List.range 81).toArray.map fun i =>
      let t := i.toFloat / 8
      ⟨t, 2 + (-t / 4).exp * (2 * t).sin⟩) (base := 1)] }]
```

:::figure PILeanManual.Plots.area (alt := "A filled region between the level 1 and a damped oscillation that starts at 2, swings between about 1.3 and 2.8 and settles at 2.")
:::

## Bands
%%%
tag := "plot-band"
%%%

{name}`PILean.Plot.Series.band` fills between two curves over the same abscissae ("fill
between"), optionally with a middle line.

```lean
/-- The abscissae of the band. -/
def bandXs : Array Float := (List.range 61).toArray.map fun i => i.toFloat / 6

/-- The middle line of the band. -/
def bandMid : Array Float := bandXs.map fun x => 2 + x.sin + 0.15 * x

/-- A mean with a widening spread around it. -/
@[figure]
def band : Figure where
  title := "Mean and spread"
  panels := #[{
    x := { label := "time" }, y := { label := "value" },
    series := #[.band "mean ± spread" bandXs
      (bandMid.mapIdx fun i m => m - 0.4 - 0.05 * i.toFloat / 6)
      (bandMid.mapIdx fun i m => m + 0.4 + 0.05 * i.toFloat / 6) (some bandMid)],
    notes := #[.hline 3 "threshold"] }]
```

:::figure PILeanManual.Plots.band (alt := "A wavy middle line rising from 2 to about 3, inside a shaded band that widens from 0.8 to 1.8 across; a horizontal reference line at 3 labelled 'threshold'.")
:::

## Grouped Bars
%%%
tag := "plot-bars"
%%%

{name}`PILean.Plot.Series.bars` puts bars on a categorical horizontal axis: the categories, and one
array of values per group, side by side.

```lean
/-- Three groups of five values. -/
@[figure]
def groupedBars : Figure where
  title := "Grouped bars"
  panels := #[{
    x := { label := "day" }, y := { label := "count" },
    series := #[.bars #["Mon", "Tue", "Wed", "Thu", "Fri"]
      #[("north", #[12, 15, 9, 17, 14]), ("south", #[8, 11, 13, 10, 16]),
        ("east", #[5, 7, 6, 9, 8])]] }]
```

:::figure PILeanManual.Plots.groupedBars (alt := "Bars for Monday to Friday, three per day for north, south and east; north is highest on most days, at 17 on Thursday.")
:::

## Stacked Bars
%%%
tag := "plot-stacked"
%%%

With `stacked := true` the groups are stacked; negative values stack below the baseline.

```lean
/-- Income and grants above the line, costs below. -/
@[figure]
def stackedBars : Figure where
  title := "Stacked bars"
  panels := #[{
    x := { label := "quarter" }, y := { label := "balance" },
    series := #[.bars #["Q1", "Q2", "Q3", "Q4"]
      #[("income", #[30, 34, 28, 40]), ("grants", #[10, 8, 12, 9]),
        ("costs", #[-22, -25, -20, -27])] (stacked := true)] }]
```

:::figure PILeanManual.Plots.stackedBars (alt := "Four quarters, each a bar of income with grants stacked on top, between 40 and 49 high, and costs below the zero line, between -20 and -27.")
:::

## Histograms
%%%
tag := "plot-histogram"
%%%

{name}`PILean.Plot.Series.histogram` counts values in bins of a nice width
({name}`PILean.Plot.histogramBins`: near `(max - min) / k`, `k` the given number of bins or
`⌈√n⌉` clamped to 5 to 60), as counts or, with `density := true`, as a density.

```lean
/-- Approximately normal numbers: the sum of twelve uniforms, less six. -/
def normals (seed n : Nat) : Array Float :=
  let u := uniforms seed (12 * n)
  (List.range n).toArray.map fun i =>
    (List.range 12).foldl (fun acc j => acc + u[12 * i + j]!) 0 - 6

/-- A histogram of 1000 such numbers. -/
@[figure]
def histogram : Figure where
  title := "A histogram"
  panels := #[{
    x := { label := "value" }, y := { label := "count" },
    series := #[.histogram "samples" (normals 7 1000)] }]
```

:::figure PILeanManual.Plots.histogram (alt := "A bell-shaped histogram of values between about -3.5 and 3.5, highest around 0.")
:::

## Functions
%%%
tag := "plot-function"
%%%

{name}`PILean.Plot.Series.function` plots a `Float → Float` function on an interval, sampled for
the picture by {name}`PILean.Plot.sampleFunction`: 64 pieces, each halved while its midpoint is
more than a quarter pixel off the chord or it is wider than 8 pixels, down to 14 halvings and
within 6000 evaluations. Values far outside the visible range are clamped first, so a pole does
not draw the refinement out of sight; a piece at full depth whose ends are more than two pixels
apart is taken for a jump and breaks the curve. When the vertical domain is not given, the
automatic range leaves out the extreme 2 % of the samples at each end if they lie far beyond the
rest.

```lean
/-- π, for the interval. -/
def pi : Float := 3.141592653589793

/-- Functions with poles and a jump, drawn without lines across them. -/
@[figure]
def poles : Figure where
  title := "Poles and jumps"
  panels := #[{
    x := { label := "x", domain := some (-2 * pi, 2 * pi) },
    y := { label := "y", domain := some (-4, 4) },
    series := #[.function "tan x" Float.tan (-2 * pi) (2 * pi),
      .function "1 / x" (fun x => 1 / x) (-2 * pi) (2 * pi),
      .function "⌊x⌋ / 2" (fun x => x.floor / 2) (-2 * pi) (2 * pi)] }]
```

:::figure PILeanManual.Plots.poles (alt := "The tangent with its branches separated at the poles, the hyperbola 1/x in two branches, and a staircase floor(x)/2, all between -4 and 4.")
:::

The sampler is tested (refinement, poles, jumps, undefined regions), not proved; such a plot has
no theorem. Where the statement "these are exactly the values of this function on this grid"
matters, use an exact series ({ref "plot-exact"}[Exact Functions]).

## Error Bars
%%%
tag := "plot-errorbars"
%%%

{name}`PILean.Plot.Series.errorBars` draws points with vertical bars, `(below, above)` for each.

```lean
/-- Measurements with error bars and a fitted line. -/
@[figure]
def errors : Figure where
  title := "Measurements with error bars"
  panels := #[{
    x := { label := "dose" }, y := { label := "response" },
    series := #[.function "fit" (fun x => 0.8 + 0.55 * x) 0.5 8.5 (dash := #[5, 4]),
      .errorBars "measured"
        ((List.range 8).toArray.map fun i =>
          let x := (i + 1).toFloat
          ⟨x, 0.8 + 0.55 * x + 0.4 * (uniforms 11 8)[i]! - 0.2⟩)
        ((List.range 8).toArray.map fun i => (0.3 + 0.04 * i.toFloat, 0.3 + 0.05 * i.toFloat))] }]
```

:::figure PILeanManual.Plots.errors (alt := "Eight measured points from dose 1 to 8 with vertical error bars that grow slightly, scattered about a dashed straight line rising from about 1 to 5.5.")
:::

## Exact Functions
%%%
tag := "plot-exact"
%%%

{name}`PILean.Plot.Series.ofExact` plots a function on the rational numbers, `f : Rat → Rat`,
through its exact samples on a grid: the `n + 1` points `(x, f x)` with
`x = lo + k (hi - lo) / n` for `k = 0, …, n`, each coordinate converted to a floating-point number
by {name}`PILean.Exact.toFloat`. It is a line through those points and nothing else; between two
samples the picture is a straight segment.

```lean
/-- A cubic, exactly. -/
def cubic (x : Rat) : Rat := x * x * x - 2 * x

/-- The cubic through its 25 exact samples on `[-2, 2]`. -/
@[figure]
def exactCubic : Figure where
  title := "A cubic from exact samples"
  panels := #[{
    x := { label := "x" }, y := { label := "x³ - 2x" },
    series := #[.ofExact "x³ - 2x" cubic (-2) 2 24,
      .scatterOfSamples "samples" (Exact.samples cubic (-2) 2 24)] }]
```

:::figure PILeanManual.Plots.exactCubic (alt := "A cubic curve from (-2, -4) through a local maximum near (-0.8, 1.1) and a local minimum near (0.8, -1.1) to (2, 4), with a marker at each of its 25 samples.")
:::

The library proves what such a series holds: {name}`PILean.Plot.Series.ofExact_points` says its
points are the exact samples converted one by one, and the grid and sample theorems of
{api}`PILean.Exact` say what the samples are. {ref "proofs"}[What a Picture Proves] has the
statements and the
pictures of the gallery that carry them.

```lean (name := exactEx)
#eval Exact.grid (-2) 2 4
#eval Exact.samples cubic (-2) 2 4
#eval (Series.ofExact "c" cubic (-2) 2 4).points.size
```

```leanResult exactEx
```

## Exact Data
%%%
tag := "plot-exact-data"
%%%

{name}`PILean.Plot.Series.ofIntPoints` and {name}`PILean.Plot.Series.scatterOfIntPoints` plot a
list of integer points as a line or as markers, point for point: as many points as given, in the
given order, none added or dropped (the theorems are {name}`PILean.Plot.Series.ofIntPoints_points`
and {name}`PILean.Plot.Series.ofIntPairs_recover`).

```lean
/-- `k² mod 13` for `k = 0, …, 26`, as integer pairs. -/
def squaresMod13 : List (Int × Int) :=
  (List.range 27).map fun (k : Nat) => (Int.ofNat k, Int.ofNat (k * k % 13))

/-- The squares modulo 13, as a line and as markers. -/
@[figure]
def residues : Figure where
  title := "Squares modulo 13"
  panels := #[{
    x := { label := "k" }, y := { label := "k² mod 13" },
    series := #[.ofIntPoints "k² mod 13" squaresMod13,
      .scatterOfIntPoints "points" squaresMod13] }]
```

:::figure PILeanManual.Plots.residues (alt := "A zigzag line with markers through the points (k, k squared mod 13) for k from 0 to 26, between 0 and 12, repeating every 13 steps.")
:::

# Axes and Scales
%%%
tag := "plot-axes"
%%%

A linear axis takes ticks at 1, 2 or 5 times a power of ten ({name}`PILean.Plot.niceTicks`), as
many as the axis length calls for ({name}`PILean.Style.tickDensity` on 400 pixels), with minor
ticks; a domain from the data is widened to whole ticks, a given `domain` is kept. A logarithmic
axis (`scale := .log`) takes decades, thinned when there are many, with 2 to 9 times each as minor
ticks; values at or below zero have no position on it and are left out. Tick labels are plain
numbers, or, when a tick needs a power of ten, every tick of the axis as a multiple of the same
power.

```lean
/-- `n!`, `2ⁿ` and `n³` on a logarithmic axis. -/
@[figure]
def growth : Figure where
  title := "Growth on a logarithmic axis"
  panels := #[{
    x := { label := "n" }, y := { label := "value", scale := .log },
    series := #[
      .line "n³" ((List.range 16).toArray.map fun i => ⟨(i + 1).toFloat, (i + 1).toFloat ^ 3⟩)
        (markers := true),
      .line "2ⁿ" ((List.range 16).toArray.map fun i =>
        ⟨(i + 1).toFloat, (2 : Float) ^ (i + 1).toFloat⟩) (markers := true),
      .step "n!" ((List.range 16).toArray.map fun i =>
        ⟨(i + 1).toFloat, ((List.range (i + 1)).foldl (fun a k => a * (k + 1).toFloat) 1)⟩)] }]
```

:::figure PILeanManual.Plots.growth (alt := "Three series on a logarithmic vertical axis from 1 to about 10 to the 13: n cubed bending over, 2 to the n as a straight line, and n factorial as steps curving upwards past both.")
:::

The multipliers of the tick step are proved to ascend and to be exactly the integers of their
range ({name}`PILean.Plot.tickMultipliers_strictlyIncreasing`,
{name}`PILean.Plot.mem_tickMultipliers`); the floating-point tick values are tested.

```lean (name := ticksEx)
#eval (niceTicks 0 97 6).values
#eval (niceTicks 0.0013 0.0091 5).values
```

```leanResult ticksEx
```

# Panels
%%%
tag := "plot-panels"
%%%

Panels fill a grid of `columns` row by row. With `shareX` or `shareY` the panels share one domain
and the tick labels are drawn on the outer panels only.

```lean
/-- Four panels sharing their axes. -/
@[figure]
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
```

:::figure PILeanManual.Plots.smallMultiples (alt := "A two by two grid of panels titled harmonic 1 to 4, each one sine wave on 0 to 2 pi with 1 to 4 periods and amplitudes 1, 1/2, 1/3 and 1/4, on the same axes; tick labels only on the outer panels.")
:::

A panel with `equalAspect` gives one unit as many pixels across as down (its plot area narrowed
or shortened, centred), and the annotations {name}`PILean.Plot.Annotation.hband` and
{name}`PILean.Plot.Annotation.vband` shade a band of the vertical or horizontal axis, labelled,
under the series.

```lean
/-- A unit circle on equal axes with a shaded band. -/
@[figure]
def equalAxes : Figure where
  title := "Equal axes"
  width := 480
  height := 320
  panels := #[{
      equalAspect := true
      x := { label := "x", domain := some (-1.5, 1.5) }
      y := { label := "y", domain := some (-1.2, 1.2) }
      series := #[.line "unit circle" ((List.range 97).toArray.map fun i =>
        let a := 2 * pi * i.toFloat / 96
        ⟨a.cos, a.sin⟩)]
      notes := #[.hband (-0.5) 0.5 "|y| ≤ 1/2"] }]
```

:::figure PILeanManual.Plots.equalAxes (alt := "A round unit circle on axes from -1.5 to 1.5 and -1.2 to 1.2 with equal units, a grey band shaded between y = -1/2 and 1/2.")
:::

# Data That Does Not Fit
%%%
tag := "plot-awkward"
%%%

Plots are drawn from whatever they are given. Non-finite values are left out of the extents and
break a line where they occur; a panel without one finite value shows its axes on `[0, 1]` and the
note "No data"; a constant series gets an interval around its value; huge values are drawn
(their coordinates are clamped in the output) and labelled with powers of ten.

```lean
/-- An empty panel, a constant, huge values and a gap. -/
@[figure]
def awkward : Figure where
  title := "Awkward data"
  width := 720
  height := 440
  columns := 2
  legend := false
  panels := #[
    { title := "no data", x := { label := "x" }, y := { label := "y" } },
    { title := "a constant", x := { label := "i" }, y := { label := "value" },
      series := #[.line "c" #[⟨0, 5⟩, ⟨1, 5⟩, ⟨2, 5⟩]] },
    { title := "huge values", x := { label := "i" }, y := { label := "value" },
      series := #[.line "h" #[⟨0, 1e15⟩, ⟨1, 3e15⟩, ⟨2, 2e15⟩]] },
    { title := "a gap", x := { label := "i" }, y := { label := "value" },
      series := #[.line "g" #[⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 0 / 0⟩, ⟨3, 2⟩, ⟨4, 3⟩]] }]
```

:::figure PILeanManual.Plots.awkward (alt := "Four panels: 'no data' with axes from 0 to 1 and a note; 'a constant' with a flat line at 5; 'huge values' with ticks labelled as multiples of a power of ten; 'a gap' with a line broken where a value is not a number.")
:::

# Labels a Reader Needs
%%%
tag := "plot-checks"
%%%

A plot a reader cannot read without asking what its axes or its curves are is reported
({api}`PILean.Plot.Check`): a panel whose horizontal or vertical axis has no label, and a panel
with two or more series (each group of a bar series counts) that neither the legend nor direct
labels (an annotation whose text is the series' label) name. The figure's `checks` level, as
for plane figures, makes `pilean-build` and the Verso blocks warn about the problems (the default),
fail, or not
look for them; a panel that is bare on purpose says so ({name}`PILean.Plot.Panel.bare`) and is
not checked. Every plot on this page is labelled.

```lean (name := plotCheckEx)
/-- One series, no axis labels. -/
def unlabelled : Panel := { series := #[.line "a" #[⟨0, 0⟩, ⟨1, 1⟩]] }

/-- Labelled axes, two series. -/
def twoSeries : Panel :=
  { x := { label := "t" }, y := { label := "u" },
    series := #[.line "a" #[⟨0, 0⟩, ⟨1, 1⟩], .line "b" #[⟨0, 1⟩, ⟨1, 0⟩]] }

#eval (Figure.problems { panels := #[unlabelled] }).map (·.kind)
#eval (Figure.problems { panels := #[twoSeries], legend := false }).map (·.kind)
#eval (Figure.problems { panels := #[twoSeries] }).size
#eval (Figure.problems { panels := #[{ unlabelled with bare := true }] }).size
```

```leanResult plotCheckEx
```
