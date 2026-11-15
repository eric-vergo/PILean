/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanTest.Examples

/-!
# Plot, canvas and animation checks

Named checks of the scales, the function sampler, histograms, the figure model on awkward data,
the canvas and the animation model.
-/

namespace PILeanTest.Plots

open PILean PILean.Plot PILean.Canvas PILeanTest.Examples

/-- Whether `s` contains `t`. -/
def has (s t : String) : Bool := (s.splitOn t).length > 1

/-- The checks of scales and ticks. -/
def scales : Array (String × Bool) :=
  let lg := Scale.ofDomain .log 3 4000 6 false
  let ln := Scale.ofDomain .linear 0 1 6 false
  #[("log: decades widened to whole powers of ten",
      lg.lo == 1 && lg.hi == 10000 && lg.major == #[1, 10, 100, 1000, 10000]),
    ("log: minor ticks at 2–9 times each decade", lg.minor.size == 32 &&
      lg.minor.all fun v => v > 1 && v < 10000),
    ("log: many decades are thinned", (Scale.ofDomain .log 1e-10 1e30 6 false).major.size ≤ 8),
    ("log: non-positive bounds are moved to positive values",
      (Scale.ofDomain .log (-5) 100 6 false).lo > 0),
    ("log: values at or below zero have no position", (lg.map 0 100 0).isNone &&
      (lg.map 0 100 (-1)).isNone && (lg.map 0 100 100).isSome),
    ("linear: minor ticks between majors, none on them",
      ln.minor.size > 0 && ln.minor.all fun v => !ln.major.any fun m => (m - v).abs < 1e-9),
    ("tick multipliers ascend", tickMultipliers (-3) 4 == [-3, -2, -1, 0, 1, 2, 3, 4] &&
      tickMultipliers 5 4 == []),
    ("labels: powers of ten in superscript for huge and tiny values",
      eNotation 2.5e7 == "2.5×10⁷" && eNotation 3e-6 == "3×10⁻⁶" && eNotation 1e10 == "10¹⁰"),
    ("labels: one style for every tick of a linear axis",
      let big := Scale.ofDomain .linear 0 1.2e10 5 false
      big.major.all (fun v => v == 0 || ((formatTick big v).splitOn "×10¹⁰").length > 1 ||
        formatTick big v == "10¹⁰")),
    ("labels: logarithmic labels as numbers within 10⁻³ to 10⁴",
      formatTick lg 1000 == "1000" && formatTick lg 10 == "10"),
    ("labels: logarithmic labels all as powers of ten past that",
      let wide := Scale.ofDomain .log 1 1e18 6 false
      wide.major.all fun v => (formatTick wide v).startsWith "10" &&
        !(formatTick wide v).contains 'e')]

/-- The largest vertical step between neighbouring points of polylines. -/
def maxStep (pls : Array (Array Point)) : Float :=
  pls.foldl (fun m pl => (List.range (pl.size - 1)).foldl (fun m i =>
    max m (((pl[i + 1]?).map (·.y)).getD 0 - ((pl[i]?).map (·.y)).getD 0 |>.abs)) m) 0

/-- The number of points of polylines. -/
def points (pls : Array (Array Point)) : Nat := pls.foldl (· + ·.size) 0

/-- The checks of the function sampler. -/
def sampler : Array (String × Bool) :=
  let tan := sampleFunction Float.tan (-2 * pi) (2 * pi) 50 50 400 (-4) 4
  let sqrt := sampleFunction Float.sqrt (-1) 1 300 300 300 (-1) 1
  let floor := sampleFunction Float.floor 0 5 100 100 300 0 5
  let sine := sampleFunction Float.sin 0 (2 * pi) 100 100 200 (-1) 1
  let nan := sampleFunction (fun _ => 0 / 0) 0 1 100 100 100 0 1
  #[("sampler: tan is broken at each of its four poles", tan.size == 5),
    ("sampler: no segment of tan crosses the plot (no line through a pole)",
      tan.all fun pl => maxStep #[pl.filter fun p => p.y.abs < 8] < 8),
    ("sampler: √x starts where it is defined", match sqrt[0]? >>= (·[0]?) with
      | some p => p.x ≥ 0 && p.x < 0.001
      | none => false),
    ("sampler: ⌊x⌋ has no risers", floor.size == 5 && maxStep floor < 0.01),
    ("sampler: a smooth curve is one polyline with few points",
      sine.size == 1 && points sine < 1200),
    ("sampler: a function defined nowhere gives nothing", nan.isEmpty),
    ("sampler: the budget bounds the work",
      points (sampleFunction (fun x => (1 / x).sin) 0.0001 1 1000 1000 300 (-1) 1 2000) ≤ 2100),
    ("sampler: an empty or non-finite interval gives nothing",
      (sampleFunction Float.sin 1 0 1 1 1 0 1).isEmpty &&
      (sampleFunction Float.sin 0 (1 / 0) 1 1 1 0 1).isEmpty)]

/-- The checks of histograms and the figure model. -/
def figures : Array (String × Bool) :=
  let bins := histogramBins (normals 7 2000) none
  let nanFig : Figure := { panels := #[{ series := #[.line "x" #[⟨0 / 0, 1⟩, ⟨1, 1 / 0⟩]] }] }
  let huge : Figure := { panels := #[{ series := #[.line "x" #[⟨0, 1e300⟩, ⟨1, -1e300⟩]] }] }
  let one : Figure := { panels := #[{ series := #[.line "only" #[⟨0, 0⟩, ⟨1, 1⟩]] }] }
  let svg := functions.toSvg
  #[("histogram: every value in a bin", bins.foldl (· + ·.2.2) 0 == 2000),
    ("histogram: bins are contiguous", (List.range (bins.size - 1)).all fun i =>
      match bins[i]?, bins[i + 1]? with
      | some (_, b, _), some (a, _, _) => (a - b).abs < 1e-9
      | _, _ => false),
    ("histogram: empty and non-finite input", (histogramBins #[] none).isEmpty &&
      (histogramBins #[0 / 0, 1 / 0] none).isEmpty),
    ("figure: non-finite data shows the note", has nanFig.toSvg "No data"),
    ("figure: huge values give finite output", !has huge.toSvg "NaN" && !has huge.toSvg "inf"),
    ("figure: one series has no legend", !one.showsLegend && functions.showsLegend),
    ("figure: deterministic", svg == functions.toSvg),
    ("figure: text is escaped", has ({ title := "a<b & c" } : Figure).toSvg "a&lt;b &amp; c"),
    ("figure: the dark style's page", has (dark functions).toSvg "#16181c"),
    ("figure: an empty figure", has ({} : Figure).toSvg "<svg"),
    ("figure: legend entries of grouped bars", groupedBars.legendEntries.size == 3)]

/-- The checks of the canvas. -/
def canvas : Array (String × Bool) :=
  let g : Shape := .group #[.path (rect 0 0 10 10) (some (.solid ⟨255, 0, 0, 255⟩))]
    (Affine.translate 5 5) 0.5 (some (rect 0 0 5 5))
  let svg := g.toSvg 20 20 "sans-serif"
  let grad : Shape := .path (rect 0 0 10 10)
    (some (.paint (.linear ⟨0, 0⟩ ⟨10, 0⟩ #[⟨0, ⟨255, 0, 0, 255⟩⟩, ⟨1, ⟨0, 0, 255, 255⟩⟩])))
  #[("canvas: transformations are applied to the geometry",
      has svg "M5 5 L15 5" && !has svg "transform"),
    ("canvas: clips become clip paths with numbered ids",
      has svg "clipPath id=\"c0\"" && has svg "clip-path=\"url(#c0)\""),
    ("canvas: opacity on the group", has svg "opacity=\"0.5\""),
    ("canvas: gradients are defined once and referenced",
      has (grad.toSvg 10 10 "x") "linearGradient id=\"p0\""),
    ("canvas: the image has the drawing", ((g.toImage 20 20 TextEngine.lettering).getpixel 7 7).r
      > 100),
    ("canvas: text as SVG text or as shapes",
      has ((Shape.text "Hi" ⟨1, 10⟩ 10 ⟨0, 0, 0, 255⟩).toSvg 20 20 "serif") "<text")]

/-- The checks of the animation model. -/
def animation : Array (String × Bool) :=
  let a := Animations.wave
  let svg := a.toSvg
  let dots := fun (t : Float) => Shape.group
    ((List.range (1 + (t * 4).toUInt64.toNat)).toArray.map fun i =>
      .path (circle ⟨5 + 8 * i.toFloat, 15⟩ 3) (some (.solid ⟨0, 0, 0, 255⟩)))
  let sw : Animation :=
    { width := 40, height := 30, fps := 4, duration := 1, frame := dots,
      text := TextEngine.lettering }
  #[("animation: frame count from duration and rate", a.frameCount == 60),
    ("animation: same-shaped frames are interpolated", has svg "calcMode=\"linear\"" &&
      !has svg "visibility"),
    ("animation: changing shapes switch frames", has sw.toSvg "attributeName=\"visibility\""),
    ("animation: no script", !has svg "<script" && !has sw.toSvg "<script"),
    ("animation: the graph build interpolates opacities, every frame the same shape",
      let gb := (Animations.graphBuild).toSvg
      has gb "calcMode=\"linear\"" && !has gb "visibility" && has gb "attributeName=\"opacity\""),
    ("animation: a poster for reduced motion",
      has svg "prefers-reduced-motion: reduce" && has svg "class=\"poster\""),
    ("animation: GIF and APNG decode to every frame",
      match sw.toGif, sw.toApng with
      | .ok g, .ok p => match Anim.readGif g, Anim.readApng p with
        | .ok fg, .ok fp => fg.frames.size == 4 && fp.frames.size == 4
        | _, _ => false
      | _, _ => false),
    ("animation: deterministic", sw.toSvg == sw.toSvg && sw.toGif.toOption == sw.toGif.toOption)]

/-- Whether values ascend strictly and lie in `[lo, hi]` (up to a relative 1e-9). -/
def ordered (vs : Array Float) (lo hi : Float) : Bool :=
  let eps := 1e-9 * max 1 (max lo.abs hi.abs)
  vs.all (fun v => v ≥ min lo hi - eps && v ≤ max lo hi + eps) &&
    (List.range (vs.size - 1)).all fun i => (vs[i]?.getD 0) < (vs[i + 1]?.getD 0)

/-- On every axis of every gallery figure, the ticks ascend strictly and lie in the axis's
range. -/
def galleryTicks : Array (String × Bool) :=
  gallery.map fun (name, fig) =>
    (s!"ticks of {name}: ascending, inside the axes",
      fig.layout.all fun l => ordered l.sx.major l.sx.lo l.sx.hi &&
        ordered l.sy.major l.sy.lo l.sy.hi && ordered l.sy.minor l.sy.lo l.sy.hi)

/-- Times a 120-frame animation (the travelling wave, 640 × 360, four seconds at 30 frames a
second) in each format: animated SVG, APNG and GIF, and drawing the frames alone; prints the
times and sizes with the load average. -/
def animBench : IO Unit := do
  let a : Animation := { Animations.wave with duration := 4 }
  let load ← try (IO.Process.output { cmd := "sysctl", args := #["-n", "vm.loadavg"] })
    catch _ => pure { exitCode := 1, stdout := "", stderr := "" }
  let t0 ← IO.monoNanosNow
  let frames : FrameSeq ← IO.lazyPure fun _ => a.frameSeq
  let t1 ← IO.monoNanosNow
  let svg : String ← IO.lazyPure fun _ => a.toSvg
  let t2 ← IO.monoNanosNow
  let apng ← IO.lazyPure fun _ => frames.toApng
  let t3 ← IO.monoNanosNow
  let gif ← IO.lazyPure fun _ => frames.toGif
  let t4 ← IO.monoNanosNow
  let ms := fun (a b : Nat) => (b - a) / 1000000
  let (tf, ts, ta, tg) := (ms t0 t1, ms t1 t2, ms t2 t3, ms t3 t4)
  IO.println s!"{a.frameCount} frames of {a.width} × {a.height} (load {load.stdout.trimAscii}):"
  IO.println s!"  draw the frames {tf} ms; SVG {ts} ms, {svg.utf8ByteSize} bytes"
  IO.println s!"  APNG encode {ta} ms, {(apng.toOption.map ByteArray.size).getD 0} bytes"
  IO.println s!"  GIF encode {tg} ms, {(gif.toOption.map ByteArray.size).getD 0} bytes"

/-- All the checks. -/
def checks : Array (String × Bool) :=
  scales ++ sampler ++ figures ++ canvas ++ animation ++ galleryTicks

end PILeanTest.Plots

#print axioms PILean.Plot.tickMultipliers_strictlyIncreasing
#print axioms PILean.Plot.mem_tickMultipliers
#print axioms PILean.Plot.tickMultipliers_length
