/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean

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
      y := { label := "count" },
      series := #[.bars #["Mon", "Tue", "Wed", "Thu", "Fri"]
      #[("north", #[12, 15, 9, 17, 14]), ("south", #[8, 11, 13, 10, 16]),
        ("east", #[5, 7, 6, 9, 8])]] }]

/-- Stacked bars, with a negative part. -/
def stackedBars : Figure where
  title := "Stacked bars"
  panels := #[{
      y := { label := "balance" },
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
    { title := "no data", series := #[.line "nothing" #[]] },
    { title := "constant", series := #[.line "flat" ((List.range 10).toArray.map fun i =>
        ⟨i.toFloat, 5⟩) (markers := true)] },
    { title := "huge values", series := #[.line "big" ((List.range 10).toArray.map fun i =>
        ⟨i.toFloat, 1e9 * (i.toFloat + 1)⟩)] },
    { title := "gaps (NaN, ∞)", series := #[.line "broken" ((List.range 21).toArray.map fun i =>
        ⟨i.toFloat, if i == 7 then 0 / 0 else if i == 14 then 1 / 0 else (i.toFloat / 3).sin⟩)
        (markers := true)] }]

/-- A figure in the dark style. -/
def dark (fig : Figure) : Figure := { fig with style := Style.dark }

/-- The figures of the gallery by name. -/
def figures : Array (String × Figure) :=
  #[("function-plot", functions), ("primes-step-plot", primes),
    ("collatz-data-plot", collatz), ("scatter-plot", scatter), ("band-area-plot", bands),
    ("grouped-bars", groupedBars), ("stacked-bars", stackedBars), ("histogram", histogram),
    ("poles", poles), ("error-bars", errors), ("log-axis", growth),
    ("small-multiples", smallMultiples), ("awkward-data", awkward)]

/-- The gallery: file name and figure; each figure light and dark. -/
def gallery : Array (String × Figure) :=
  figures.map (fun (n, f) => (n ++ ".svg", f)) ++
    figures.map (fun (n, f) => (n ++ "-dark.svg", dark f))

end PILeanTest.Examples
