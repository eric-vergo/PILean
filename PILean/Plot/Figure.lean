/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plot.Scale
import PILean.Plot.Sample
import PILean.Canvas
import PILean.Style

/-!
# Figures

A figure is a Lean value: a size, a title, a style and panels in a grid; each panel has two
axes, series and annotations. `Figure.draw` lays it out as a drawing on the vector canvas
(`PILean.Canvas`), from which `Figure.toSvg` and `Figure.toPng` write the same picture.

* **Series**: lines (with markers), scatter points, steps, areas and bands (fill between two
  curves), bars (grouped or stacked, on a categorical axis), histograms, graphs of functions
  (sampled adaptively, broken at poles and jumps: `sampleFunction`) and error bars.
* **Axes**: linear or logarithmic (`ScaleKind`), domains from the data widened to whole ticks
  or given, major ticks with labels, minor ticks, a grid, an axis label.
* **Panels** in a grid of `columns`, with shared horizontal or vertical axes: one domain for all
  panels, tick labels only on the outer panels.
* **Legend**: one row (wrapped when long) under the title, each series' label after a swatch of
  its mark, drawn when a figure has more than one labelled series.
* **Annotations**: text at a point, horizontal and vertical reference lines with labels, a
  labelled point.
* **Craft**: plot areas on whole pixels and one-pixel lines on pixel centres; text measured with
  the style's text engine; nothing drawn in a series colour but the series' marks.

**Data that does not fit.** Non-finite values are left out (a line is broken there); points at
or below zero are left out on a logarithmic axis; a panel without a single finite value shows its
axes on `[0, 1]` and the note "No data"; a constant series gets an interval around its value
(`niceTicks`); huge values are drawn (coordinates are clamped in the output) and labelled in
E-notation; a function's automatic vertical domain leaves out the extreme 2 % of its samples at
each end when they lie far beyond the rest (a pole would otherwise flatten the curve).

## Main definitions

* `Series`, `Annotation`, `Axis`, `Panel`, `Figure`.
* `Figure.draw`, `Figure.toSvg`, `Figure.toImage`, `Figure.toPng`.
-/

namespace PILean.Plot

open PILean Canvas

/-- How a step series turns: after each point (`post`), before it (`pre`) or half-way. -/
inductive StepAt where
  /-- The value holds until the next point. -/
  | post
  /-- The value holds from the previous point. -/
  | pre
  /-- The value changes half-way between points. -/
  | mid
  deriving BEq, Inhabited, Repr

/-- What a panel draws. -/
inductive Series where
  /-- A line through points in order, with markers when `markers`. -/
  | line (label : String) (points : Array Point) (color : Option Rgba := none)
      (markers : Bool := false) (dash : Array Float := #[])
  /-- Points as markers. -/
  | scatter (label : String) (points : Array Point) (color : Option Rgba := none)
      (radius : Option Float := none)
  /-- A step function through points. -/
  | step (label : String) (points : Array Point) (color : Option Rgba := none)
      (at_ : StepAt := .post)
  /-- The region between a line through points and the value `base`, with the line. -/
  | area (label : String) (points : Array Point) (base : Float := 0)
      (color : Option Rgba := none)
  /-- The region between two curves over the same `xs` (fill between), optionally with the
  middle line `mid`. -/
  | band (label : String) (xs lo hi : Array Float) (mid : Option (Array Float) := none)
      (color : Option Rgba := none)
  /-- Bars on a categorical horizontal axis: the categories, and a series of values per group;
  grouped side by side, or stacked. -/
  | bars (categories : Array String) (groups : Array (String × Array Float))
      (stacked : Bool := false) (colors : Array Rgba := #[])
  /-- A histogram of values: `bins` bins (by default from the number of values), counts or a
  density. -/
  | histogram (label : String) (values : Array Float) (bins : Option Nat := none)
      (density : Bool := false) (color : Option Rgba := none)
  /-- The graph of `f` on `[x0, x1]`, sampled adaptively. Its guarantee is weaker than that of
  `Series.ofExact`: the sampler is tested (refinement, poles, jumps), not proved. -/
  | function (label : String) (f : Float → Float) (x0 x1 : Float) (color : Option Rgba := none)
      (dash : Array Float := #[])
  /-- Points with vertical error bars, `(below, above)` each. -/
  | errorBars (label : String) (points : Array Point) (err : Array (Float × Float))
      (color : Option Rgba := none)
  deriving Inhabited

/-- A note on a panel, in data coordinates. -/
inductive Annotation where
  /-- Text with its anchor at a point. -/
  | text (at_ : Point) (s : String) (anchor : Svg.Anchor := .start)
  /-- A horizontal reference line at `y`, labelled at its right end. -/
  | hline (y : Float) (label : String := "")
  /-- A vertical reference line at `x`, labelled at its top. -/
  | vline (x : Float) (label : String := "")
  /-- A point, marked and labelled. -/
  | point (at_ : Point) (label : String)
  deriving Inhabited

/-- An axis. -/
structure Axis where
  /-- The axis label. -/
  label : String := ""
  /-- The scale's kind. -/
  scale : ScaleKind := .linear
  /-- A fixed domain; by default the data's extent widened to whole ticks. -/
  domain : Option (Float × Float) := none
  /-- Whether the domain includes zero (bars and areas include their base anyway). -/
  includeZero : Bool := false
  deriving Inhabited

/-- A panel: a title, two axes, series and annotations. -/
structure Panel where
  /-- The panel's title. -/
  title : String := ""
  /-- The horizontal axis. -/
  x : Axis := {}
  /-- The vertical axis. -/
  y : Axis := {}
  /-- The series, drawn in order. -/
  series : Array Series := #[]
  /-- The annotations, drawn over the series. -/
  notes : Array Annotation := #[]
  deriving Inhabited

/-- A figure. -/
structure Figure where
  /-- Width. -/
  width : Float := 640
  /-- Height. -/
  height : Float := 400
  /-- The title. -/
  title : String := ""
  /-- The panels, row by row. -/
  panels : Array Panel := #[]
  /-- The number of columns of the grid. -/
  columns : Nat := 1
  /-- Whether the panels share one horizontal domain. -/
  shareX : Bool := false
  /-- Whether the panels share one vertical domain. -/
  shareY : Bool := false
  /-- Whether the legend is drawn (when there is more than one labelled series). -/
  legend : Bool := true
  /-- The style. -/
  style : Style := Style.light
  deriving Inhabited

/-! ### Data -/

/-- Whether both coordinates of a point are finite. -/
def finitePoint (p : Point) : Bool := finite p.x && finite p.y

/-- The bins of a histogram: their edges and counts. The bin width is a nice number near
`(max - min) / k` for `k` the given count or `⌈√n⌉` (between 5 and 60). -/
def histogramBins (values : Array Float) (bins : Option Nat) : Array (Float × Float × Nat) :=
  Id.run do
  let vs := values.filter finite
  if vs.isEmpty then return #[]
  let lo := vs.foldl min (vs[0]?.getD 0)
  let hi := vs.foldl max (vs[0]?.getD 0)
  let k := max 1 (bins.getD (max 5 (min 60 (vs.size.toFloat.sqrt.ceil.toUInt64.toNat))))
  let t := niceTicks lo hi k
  let w := t.step
  if !(w > 0) then return #[(lo - 0.5, lo + 0.5, vs.size)]
  let start := Float.ofInt (floorInt (lo / w + 1e-9)) * w
  let n := max 1 (ceilInt ((hi - start) / w - 1e-9)).toNat
  let n := if (start + n.toFloat * w) ≤ hi then n + 1 else n
  if n > 10000 then return #[]
  let mut counts := Array.replicate n 0
  for v in vs do
    let i := (floorInt ((v - start) / w)).toNat
    let i := if i ≥ n then n - 1 else i
    counts := counts.modify i (· + 1)
  return (List.range n).toArray.map fun i =>
    (start + i.toFloat * w, start + (i + 1).toFloat * w, counts[i]?.getD 0)

/-- The extent of some values, `none` for none. -/
def extentOf (vs : Array Float) : Option (Float × Float) :=
  if vs.isEmpty then none else some (vs.foldl min (vs[0]?.getD 0), vs.foldl max (vs[0]?.getD 0))

/-- The points a series spans (its function series span only their interval's ends). -/
def Series.points : Series → Array Point
  | .line _ ps .. | .scatter _ ps .. | .step _ ps .. => ps
  | .area _ ps base _ => ps ++ ps.map fun p => ⟨p.x, base⟩
  | .band _ xs lo hi _ _ => (xs.zip lo).map (fun (x, y) => ⟨x, y⟩) ++
      (xs.zip hi).map (fun (x, y) => ⟨x, y⟩)
  | .errorBars _ ps err _ => (ps.zip err).foldl (fun acc (p, (l, h)) =>
      (acc.push ⟨p.x, p.y - l⟩).push ⟨p.x, p.y + h⟩) #[]
  | .histogram _ vs bins density _ =>
      let total := (vs.filter finite).size.toFloat
      (histogramBins vs bins).foldl (fun acc (a, b, c) =>
        let h := if density then c.toFloat / (total * (b - a)) else c.toFloat
        (acc.push ⟨a, 0⟩).push ⟨b, h⟩) #[]
  | .bars cats groups stacked _ => Id.run do
      let mut out : Array Point := #[⟨0, 0⟩]
      for i in [0:cats.size] do
        let vals := groups.map fun (_, vs) => (vs[i]?).getD 0
        let vals := vals.filter finite
        let (t, b) := if stacked then
            (vals.foldl (fun a v => a + max 0 v) 0, vals.foldl (fun a v => a + min 0 v) 0)
          else (vals.foldl max 0, vals.foldl min 0)
        out := (out.push ⟨i.toFloat, t⟩).push ⟨i.toFloat, b⟩
      return out
  | .function _ _ x0 x1 _ _ => #[⟨x0, 0⟩, ⟨x1, 0⟩]

/-- A series' horizontal and vertical extents on axes of kinds `xk` and `yk` (values that have no
position left out); a function series has no vertical extent of its own here. -/
def Series.extent (s : Series) (xk yk : ScaleKind) :
    Option (Float × Float) × Option (Float × Float) :=
  let okX := fun (v : Float) => finite v && (xk != .log || v > 0)
  let okY := fun (v : Float) => finite v && (yk != .log || v > 0)
  match s with
  | .function _ _ x0 x1 _ _ => (extentOf (#[x0, x1].filter okX), none)
  | _ =>
    -- only points with a position on both axes count
    let pts := s.points.filter fun p => okX p.x && okY p.y
    (extentOf (pts.map (·.x)), extentOf (pts.map (·.y)))

/-- The union of two optional intervals. -/
def unionExt : Option (Float × Float) → Option (Float × Float) → Option (Float × Float)
  | some (a, b), some (c, d) => some (min a c, max b d)
  | some e, none | none, some e => some e
  | none, none => none

/-- The vertical extent of a function's samples over `[x0, x1]` (400 equal steps), leaving out
the extreme 2 % at each end when they lie far beyond the rest. -/
def functionExtent (f : Float → Float) (x0 x1 : Float) (yk : ScaleKind) :
    Option (Float × Float) := Id.run do
  if !(finite x0 && finite x1) || x1 < x0 then return none
  let n := 400
  let ys := ((List.range (n + 1)).toArray.map fun i =>
    f (x0 + (x1 - x0) * i.toFloat / n.toFloat)).filter fun v => finite v && (yk != .log || v > 0)
  if ys.isEmpty then return none
  let s := ys.qsort (· < ·)
  let at_ := fun (q : Float) => (s[(q * (s.size - 1).toFloat).round.toUInt64.toNat]?).getD 0
  let (lo, hi) := (s[0]?.getD 0, s.back?.getD 0)
  let core := at_ 0.95 - at_ 0.05
  if core > 0 && (hi - lo) > 12 * core then return some (at_ 0.02, at_ 0.98)
  return some (lo, hi)

/-! ### Layout -/

/-- A panel laid out: its plot area, scales, and whether its tick labels show. -/
structure PanelLayout where
  /-- The plot area. -/
  area : Box
  /-- The horizontal scale (for bars, the categories' indices `0 … n - 1` at band centres). -/
  sx : Scale
  /-- The vertical scale. -/
  sy : Scale
  /-- The categories of a bar panel. -/
  categories : Array String := #[]
  /-- Whether the horizontal tick labels and axis label show. -/
  xLabels : Bool := true
  /-- Whether the vertical tick labels and axis label show. -/
  yLabels : Bool := true
  /-- Whether the panel has data. -/
  hasData : Bool := true
  deriving Inhabited

/-- A panel's data extents on both axes. -/
def Panel.extents (p : Panel) : Option (Float × Float) × Option (Float × Float) :=
  p.series.foldl (init := (none, none)) fun (ex, ey) s =>
    let (a, b) := s.extent p.x.scale p.y.scale
    (unionExt ex a, unionExt ey b)

/-- A panel's vertical extent including its functions' samples over the horizontal domain. -/
def Panel.yExtent (p : Panel) (xd : Float × Float) : Option (Float × Float) :=
  p.series.foldl (init := p.extents.2) fun acc s => match s with
    | .function _ f x0 x1 _ _ =>
      unionExt acc (functionExtent f (max x0 xd.1) (min x1 xd.2) p.y.scale)
    | _ => acc

/-- The categories of a panel's bars, if it has bars. -/
def Panel.categories (p : Panel) : Array String :=
  p.series.foldl (init := #[]) fun acc s => match s with
    | .bars cats .. => if acc.isEmpty then cats else acc
    | _ => acc

/-- The target number of ticks for an axis `len` pixels long. -/
def tickTarget (st : Style) (len : Float) : Nat :=
  max 2 ((st.tickDensity.toFloat * len / 400).round.toUInt64.toNat)

/-- A legend entry: label, colour, dashed, and the swatch's kind (`line`, `line-marker`,
`marker`, `fill`). -/
abbrev LegendEntry := String × Rgba × Bool × String

/-- The labelled series of a figure for its legend, in order, without repeats. -/
def Figure.legendEntries (fig : Figure) : Array LegendEntry := Id.run do
  let mut out : Array LegendEntry := #[]
  for p in fig.panels do
    let mut i := 0
    for s in p.series do
      match s with
      | .bars _ groups _ colors =>
        for h : j in [0:groups.size] do
          let name := groups[j].1
          let (c, d) := fig.style.seriesColor (i + j)
          let c := (colors[j]?).getD c
          if !name.isEmpty && !out.any (·.1 == name) then out := out.push (name, c, d, "fill")
        i := i + groups.size
      | _ =>
        let (c0, d) := fig.style.seriesColor i
        let (label, c, kind) := match s with
          | .line l _ c m _ => (l, c.getD c0, if m then "line-marker" else "line")
          | .scatter l _ c _ => (l, c.getD c0, "marker")
          | .step l _ c _ => (l, c.getD c0, "line")
          | .area l _ _ c => (l, c.getD c0, "fill")
          | .band l _ _ _ _ c => (l, c.getD c0, "fill")
          | .histogram l _ _ _ c => (l, c.getD c0, "fill")
          | .function l _ _ _ c _ => (l, c.getD c0, "line")
          | .errorBars l _ _ c => (l, c.getD c0, "marker")
          | .bars .. => ("", c0, "fill")
        if !label.isEmpty && !out.any (·.1 == label) then out := out.push (label, c, d, kind)
        i := i + 1
  return out

/-- The legend's rows: entries with their x offsets, wrapped to `width`. -/
def legendRows (st : Style) (entries : Array LegendEntry) (width : Float) :
    Array (Array (Float × LegendEntry)) := Id.run do
  let mut rows := #[]
  let mut row := #[]
  let mut x : Float := 0
  for e in entries do
    let w := st.swatch + 6 + st.text.measure e.1 st.legendSize
    if x > 0 && x + w > width then
      rows := rows.push row; row := #[]; x := 0
    row := row.push (x, e)
    x := x + w + st.legendGap
  if !row.isEmpty then rows := rows.push row
  return rows

/-- The height of a line of text of `size`. -/
def lineHeight (st : Style) (size : Float) : Float :=
  size * (st.text.ascent + st.text.descent) * 1.15

/-- Whether a figure draws its legend. -/
def Figure.showsLegend (fig : Figure) : Bool := fig.legend && fig.legendEntries.size > 1

/-- The top of the panel grid: below the title and the legend. -/
def Figure.gridTop (fig : Figure) : Float := Id.run do
  let st := fig.style
  let mut top := st.margin
  if !fig.title.isEmpty then top := top + lineHeight st st.titleSize + st.titleGap
  if fig.showsLegend then
    let rws := legendRows st fig.legendEntries (fig.width - 2 * st.margin)
    top := top + rws.size.toFloat * lineHeight st st.legendSize * 1.25 + st.titleGap * 0.5
  return top

/-- The figure's panels laid out. -/
def Figure.layout (fig : Figure) : Array PanelLayout := Id.run do
  let st := fig.style
  let n := fig.panels.size
  if n == 0 then return #[]
  let cols := max 1 (min fig.columns n)
  let rows := (n + cols - 1) / cols
  let tx := st.text
  let top := fig.gridTop
  let xExt := fig.panels.map (·.extents.1)
  let sharedX := xExt.foldl unionExt none
  let xDomain := fun (i : Nat) (p : Panel) =>
    match p.x.domain with
    | some d => (d, true)
    | none =>
      let e := (if fig.shareX then sharedX else (xExt[i]?).join).getD (0, 1)
      -- the interval of graphs of functions alone is shown as given, not widened to ticks
      let onlyFunctions := !p.series.isEmpty && p.series.all fun s => match s with
        | .function .. => true | _ => false
      (if p.x.includeZero then (min e.1 0, max e.2 0) else e, onlyFunctions)
  let yExts := fig.panels.mapIdx fun i p => p.yExtent (xDomain i p).1
  let sharedY := yExts.foldl unionExt none
  let cellW := (fig.width - 2 * st.margin - (cols - 1).toFloat * st.panelGap) / cols.toFloat
  let cellH := (fig.height - top - st.margin - (rows - 1).toFloat * st.panelGap) / rows.toFloat
  let mut scales : Array (Scale × Scale × Array String × Bool) := #[]
  let mut leftG : Float := 0
  let anyPanelTitle := fig.panels.any (!·.title.isEmpty)
  let anyXLabel := fig.panels.any (!·.x.label.isEmpty)
  let anyYLabel := fig.panels.any (!·.y.label.isEmpty)
  for h : i in [0:n] do
    let p := fig.panels[i]
    let cats := p.categories
    let (xd, xfixed) := xDomain i p
    let sx := if cats.isEmpty then
        Scale.ofDomain p.x.scale xd.1 xd.2 (tickTarget st cellW) xfixed
      else { lo := -0.5, hi := cats.size.toFloat - 0.5, major := #[] }
    let ye := if fig.shareY then sharedY else (yExts[i]?).join
    let hasData := ye.isSome || !cats.isEmpty
    let (yd, yfixed) := match p.y.domain with
      | some d => (d, true)
      | none =>
        let e := ye.getD (0, 1)
        let needsZero := p.y.includeZero || p.series.any fun s => match s with
          | .bars .. | .histogram .. | .area .. => true | _ => false
        (if needsZero && p.y.scale == ScaleKind.linear then (min e.1 0, max e.2 0) else e, false)
    let sy := Scale.ofDomain p.y.scale yd.1 yd.2 (tickTarget st cellH) yfixed
    let widest := sy.major.foldl (fun m v => max m (tx.measure (formatTick sy v) st.tickSize)) 0
    leftG := max leftG widest
    scales := scales.push (sx, sy, cats, hasData)
  let left := leftG + st.tickLength + st.tickLabelGap +
    (if anyYLabel then lineHeight st st.labelSize + st.labelGap else 0)
  let bottom := st.tickLength + st.tickLabelGap + lineHeight st st.tickSize +
    (if anyXLabel then lineHeight st st.labelSize + st.labelGap * 0.5 else 0)
  let titleH := if anyPanelTitle then lineHeight st st.panelTitleSize + st.titleGap * 0.6
    else 0
  -- the last horizontal tick label reaches past the area's right edge
  let right := st.tickSize * 1.4
  let mut out := #[]
  for i in [0:n] do
    let (sx, sy, cats, hasData) := (scales[i]?).getD default
    let r := i / cols
    let c := i % cols
    let showX := !fig.shareX || r == rows - 1 || i + cols ≥ n
    let showY := !fig.shareY || c == 0
    let x0 := st.margin + c.toFloat * (cellW + st.panelGap)
    let y0 := top + r.toFloat * (cellH + st.panelGap)
    let area : Box := ⟨(x0 + left).round, (y0 + titleH).round, (x0 + cellW - right).round,
      (y0 + cellH - bottom).round⟩
    let pl : PanelLayout :=
      { area, sx, sy, categories := cats, xLabels := showX, yLabels := showY, hasData }
    out := out.push pl
  return out

/-! ### Drawing -/

/-- The pixel of a data point on a laid-out panel (`none` when it has no position); coordinates
far outside the area are clamped, so that output numbers stay finite and small. -/
def PanelLayout.toPx (l : PanelLayout) (p : Point) : Option Point := do
  let x ← l.sx.map l.area.x0 l.area.x1 p.x
  let y ← l.sy.map l.area.y1 l.area.y0 p.y
  let cl := fun (v lo hi : Float) => max (lo - 1e5) (min (hi + 1e5) v)
  some ⟨cl x l.area.x0 l.area.x1, cl y l.area.y0 l.area.y1⟩

/-- A one-pixel line's coordinate on the pixel centre nearest `v`. -/
def crisp (v : Float) : Float := v.floor + 0.5

/-- The runs of present values in a list, each of at least two values, broken at every `none`
and in the order of the list. The accumulator `cur` holds the current run, last value first. -/
def runs {α : Type} : List (Option α) → List α → List (List α)
  | [], cur => if 1 < cur.length then [cur.reverse] else []
  | none :: xs, cur => (if 1 < cur.length then [cur.reverse] else []) ++ runs xs []
  | some a :: xs, cur => runs xs (a :: cur)

/-- Polylines through the points that `pos` gives a position, broken where one has none; a run of
a single point is dropped. -/
def polylinesWith (pos : Point → Option Point) (ps : Array Point) : Array (Array Point) :=
  ((runs (ps.toList.map pos) []).map List.toArray).toArray

/-- The position of a data point on a laid-out panel: `none` when it is not finite or has no
position. -/
def PanelLayout.pos (l : PanelLayout) (p : Point) : Option Point :=
  if finitePoint p then l.toPx p else none

/-- Polylines through the points that have positions, broken where one has none. -/
def PanelLayout.polylines (l : PanelLayout) (ps : Array Point) : Array (Array Point) :=
  polylinesWith l.pos ps

/-- A marker: a disc of the series' colour with a ring of the page colour. -/
def marker (st : Style) (q : Point) (c : Rgba) (r : Float) : Shape :=
  .path (circle q r) (some (.solid c)) (some { ink := st.background, width := st.markerRing })

/-- A rectangle from `(x0, y0)` to `(x1, y1)` (`y0` above `y1`) with the two corners away from the
baseline rounded by `rad`: the top ones when `up`, else the bottom ones. -/
def barPath (x0 y0 x1 y1 rad : Float) (up : Bool) : Path :=
  let r := max 0 (min rad (min ((x1 - x0) / 2) ((y1 - y0).abs / 2)))
  let k := Path.kappa * r
  if r ≤ 0 then Path.rect x0 y0 (x1 - x0) (y1 - y0)
  else if up then
    ((((((Path.empty.moveTo ⟨x0, y1⟩).lineTo ⟨x0, y0 + r⟩).cubicTo ⟨x0, y0 + r - k⟩
      ⟨x0 + r - k, y0⟩ ⟨x0 + r, y0⟩).lineTo ⟨x1 - r, y0⟩).cubicTo ⟨x1 - r + k, y0⟩
      ⟨x1, y0 + r - k⟩ ⟨x1, y0 + r⟩).lineTo ⟨x1, y1⟩).close
  else
    ((((((Path.empty.moveTo ⟨x0, y0⟩).lineTo ⟨x0, y1 - r⟩).cubicTo ⟨x0, y1 - r + k⟩
      ⟨x0 + r - k, y1⟩ ⟨x0 + r, y1⟩).lineTo ⟨x1 - r, y1⟩).cubicTo ⟨x1 - r + k, y1⟩
      ⟨x1, y1 - r + k⟩ ⟨x1, y1 - r⟩).lineTo ⟨x1, y0⟩).close

/-- The points of a step line through `ps`. -/
def stepPoints (ps : Array Point) (at_ : StepAt) : Array Point := Id.run do
  let mut out : Array Point := #[]
  for p in ps do
    match out.back?, at_ with
    | some q, .post => out := (out.push ⟨p.x, q.y⟩).push p
    | some q, .pre => out := (out.push ⟨q.x, p.y⟩).push p
    | some q, .mid =>
      let m := (q.x + p.x) / 2
      out := ((out.push ⟨m, q.y⟩).push ⟨m, p.y⟩).push p
    | none, _ => out := out.push p
  return out

/-- The data line of a series. -/
def dataLine (st : Style) (c : Rgba) (dash : Array Float) : Line :=
  { ink := c, width := st.lineWidth, cap := "round", join := "round", dash }

/-- The shapes of bars on a laid-out panel; `index` is the first group's colour slot. -/
def drawBars (st : Style) (l : PanelLayout) (cats : Array String)
    (groups : Array (String × Array Float)) (stacked : Bool) (colors : Array Rgba)
    (index : Nat) : Array Shape := Id.run do
  let a := l.area
  let n := cats.size
  let g := max groups.size 1
  let band := a.width / (max n 1).toFloat
  let inner := band * (1 - st.groupGap)
  let barW := if stacked then inner else inner / g.toFloat
  let mut out := #[]
  for i in [0:n] do
    let cx := a.x0 + band * (i.toFloat + 0.5)
    let mut posAcc : Float := 0
    let mut negAcc : Float := 0
    for h : j in [0:groups.size] do
      let v := (groups[j].2[i]?).getD 0
      if !finite v || v == 0 then continue
      let c := (colors[j]?).getD (st.seriesColor (index + j)).1
      let (b0, b1) := if stacked then
          if v ≥ 0 then (posAcc, posAcc + v) else (negAcc + v, negAcc)
        else (0, v)
      if stacked then
        if v ≥ 0 then posAcc := posAcc + v else negAcc := negAcc + v
      let some p0 := l.toPx ⟨0, b0⟩ | continue
      let some p1 := l.toPx ⟨0, b1⟩ | continue
      let x0 := if stacked then cx - barW / 2 else cx - inner / 2 + j.toFloat * barW
      let gap := st.fillGap / 2
      let (ytop, ybot) := (min p0.y p1.y, max p0.y p1.y)
      let (ytop, ybot) := if stacked && b0 != 0 then
          (if v ≥ 0 then (ytop, ybot - gap) else (ytop + gap, ybot)) else (ytop, ybot)
      out := out.push (.path (barPath (x0 + gap) ytop (x0 + barW - gap) ybot st.barRadius (v ≥ 0))
        (some (.solid c)) none)
  return out

/-- The shapes of one series on a laid-out panel; `index` is its colour slot. -/
def drawSeries (st : Style) (l : PanelLayout) (s : Series) (index : Nat) : Array Shape :=
  Id.run do
  let (c0, dashed0) := st.seriesColor index
  let dashOf := fun (d : Array Float) => if !d.isEmpty then d else if dashed0 then #[6, 4] else #[]
  let a := l.area
  let toPx := l.pos
  match s with
  | .line _ ps c markers dash =>
    let c := c.getD c0
    let mut out := (l.polylines ps).map fun pl =>
      Shape.path (Path.polyline pl) none (some (dataLine st c (dashOf dash)))
    if markers then
      for p in ps do
        if let some q := toPx p then out := out.push (marker st q c st.markerRadius)
    return out
  | .scatter _ ps c r =>
    let c := c.getD c0
    return ps.filterMap fun p =>
      (toPx p).map fun q => marker st q c (r.getD (st.markerRadius + 0.5))
  | .step _ ps c at_ =>
    let c := c.getD c0
    return (l.polylines (stepPoints ps at_)).map fun pl =>
      Shape.path (Path.polyline pl) none (some (dataLine st c (dashOf #[])))
  | .area _ ps base c =>
    let c := c.getD c0
    let mut out := #[]
    let some b0 := l.toPx ⟨(ps[0]?.map (·.x)).getD 0, base⟩ | return #[]
    for pl in l.polylines ps do
      let first := (pl[0]?).getD ⟨0, 0⟩
      let last := pl.back?.getD first
      let region := ((pl.foldl (fun (p : Path) q => p.lineTo q)
        (Path.empty.moveTo ⟨first.x, b0.y⟩)).lineTo ⟨last.x, b0.y⟩).close
      out := out.push (.path region (some (.solid c)) none st.areaOpacity)
      out := out.push (.path (Path.polyline pl) none (some (dataLine st c #[])))
    return out
  | .band _ xs lo hi mid c =>
    let c := c.getD c0
    let tq := (xs.zip hi).filterMap fun (x, y) => toPx ⟨x, y⟩
    let bq := ((xs.zip lo).filterMap fun (x, y) => toPx ⟨x, y⟩).reverse
    let mut out := #[]
    if tq.size > 1 && bq.size > 1 then
      out := out.push (.path (Path.polyline (tq ++ bq)).close (some (.solid c)) none
        (st.areaOpacity * 1.3))
    if let some m := mid then
      for pl in l.polylines ((xs.zip m).map fun (x, y) => ⟨x, y⟩) do
        out := out.push (.path (Path.polyline pl) none (some (dataLine st c #[])))
    return out
  | .bars cats groups stacked colors => return drawBars st l cats groups stacked colors index
  | .histogram _ vs bins density c =>
    let c := c.getD c0
    let total := (vs.filter finite).size.toFloat
    return (histogramBins vs bins).filterMap fun (x0, x1, k) =>
      let hgt := if density then k.toFloat / (total * (x1 - x0)) else k.toFloat
      match l.toPx ⟨x0, 0⟩, l.toPx ⟨x1, hgt⟩ with
      | some p0, some p1 =>
        if k == 0 then none else
        some (.path (barPath (p0.x + st.fillGap / 2) p1.y (p1.x - st.fillGap / 2) p0.y
          (st.barRadius / 2) true) (some (.solid c)) none)
      | _, _ => none
  | .function _ f x0 x1 c dash =>
    let c := c.getD c0
    let (lo, hi) := (max x0 (min l.sx.lo l.sx.hi), min x1 (max l.sx.lo l.sx.hi))
    let sx := if l.sx.hi == l.sx.lo then 1 else a.width / (l.sx.hi - l.sx.lo).abs
    let pls := match l.sy.kind with
      | .linear =>
        let span := (l.sy.hi - l.sy.lo).abs
        sampleFunction f lo hi sx (if span == 0 then 1 else a.height / span) a.height
          l.sy.lo l.sy.hi
      | .log =>
        let span := (l.sy.hi.log10 - l.sy.lo.log10).abs
        (sampleFunction (fun x => (f x).log10) lo hi sx
          (if span == 0 then 1 else a.height / span) a.height l.sy.lo.log10 l.sy.hi.log10).map
          (fun (pl : Array Point) =>
            pl.map fun (p : Point) => (⟨p.x, (10 : Float) ^ p.y⟩ : Point))
    return pls.foldl (fun acc pl => acc ++ (l.polylines pl).map fun q =>
      Shape.path (Path.polyline q) none (some (dataLine st c (dashOf dash)))) #[]
  | .errorBars _ ps err c =>
    let c := c.getD c0
    let mut out := #[]
    for (p, (dl, dh)) in ps.zip err do
      match toPx ⟨p.x, p.y - dl⟩, toPx ⟨p.x, p.y + dh⟩, toPx p with
      | some q0, some q1, some q =>
        let cap := st.errorCap
        let bar := (((((Path.empty.moveTo q0).lineTo q1).moveTo ⟨q0.x - cap, q0.y⟩).lineTo
          ⟨q0.x + cap, q0.y⟩).moveTo ⟨q1.x - cap, q1.y⟩).lineTo ⟨q1.x + cap, q1.y⟩
        out := out.push (.path bar none (some { ink := c, width := 1.25, cap := "round" }))
        out := out.push (marker st q c st.markerRadius)
      | _, _, _ => pure ()
    return out

/-- A hairline. -/
def hairline (c : Rgba) : Line := { ink := c, width := 1 }

/-- The shapes of a panel's frame: the grid (drawn under the data) and the axes, ticks, labels
and title (drawn over it). -/
def drawFrame (st : Style) (l : PanelLayout) (p : Panel) : Array Shape × Array Shape := Id.run do
  let a := l.area
  let tx := st.text
  let mut grid : Array Shape := #[]
  let mut front : Array Shape := #[]
  let xPos := fun (v : Float) => l.sx.map a.x0 a.x1 v
  let yPos := fun (v : Float) => l.sy.map a.y1 a.y0 v
  let hline := fun (y : Float) (c : Rgba) =>
    Shape.path (Path.polyline #[⟨a.x0, crisp y⟩, ⟨a.x1, crisp y⟩]) none (some (hairline c))
  let vline := fun (x : Float) (c : Rgba) =>
    Shape.path (Path.polyline #[⟨crisp x, a.y0⟩, ⟨crisp x, a.y1⟩]) none (some (hairline c))
  if st.minorGrid then
    for v in l.sy.minor do
      if let some y := yPos v then grid := grid.push (hline y st.gridMinor)
    if l.categories.isEmpty then
      for v in l.sx.minor do
        if let some x := xPos v then grid := grid.push (vline x st.gridMinor)
  if st.majorGrid then
    for v in l.sy.major do
      if let some y := yPos v then grid := grid.push (hline y st.grid)
    if l.categories.isEmpty then
      for v in l.sx.major do
        if let some x := xPos v then grid := grid.push (vline x st.grid)
  let bottom := crisp a.y1
  let left := crisp a.x0
  front := front.push (.path (Path.polyline #[⟨left - 0.5, bottom⟩, ⟨a.x1, bottom⟩]) none
    (some (hairline st.axis)))
  if l.categories.isEmpty then
    front := front.push (.path (Path.polyline #[⟨left, a.y0⟩, ⟨left, bottom⟩]) none
      (some (hairline st.axis)))
  let mut ticks := Path.empty
  let labelY := a.y1 + st.tickLength + st.tickLabelGap + st.tickSize * tx.ascent
  if l.categories.isEmpty then
    for v in l.sx.major do
      if let some x := xPos v then
        ticks := (ticks.moveTo ⟨crisp x, bottom⟩).lineTo ⟨crisp x, bottom + st.tickLength⟩
        if l.xLabels then
          front := front.push (.text (formatTick l.sx v) ⟨crisp x, labelY⟩ st.tickSize
            st.inkMuted .middle)
    if st.minorTicks then
      for v in l.sx.minor do
        if let some x := xPos v then
          ticks :=
            (ticks.moveTo ⟨crisp x, bottom⟩).lineTo ⟨crisp x, bottom + st.minorTickLength⟩
  else if l.xLabels then
    let band := a.width / (max l.categories.size 1).toFloat
    for h : i in [0:l.categories.size] do
      front := front.push (.text l.categories[i] ⟨a.x0 + band * (i.toFloat + 0.5), labelY⟩
        st.tickSize st.inkMuted .middle)
  let tickX := left - st.tickLength - st.tickLabelGap
  for v in l.sy.major do
    if let some y := yPos v then
      if l.categories.isEmpty then
        ticks := (ticks.moveTo ⟨left - st.tickLength, crisp y⟩).lineTo ⟨left, crisp y⟩
      if l.yLabels then
        front := front.push (.text (formatTick l.sy v) ⟨tickX, crisp y + st.tickSize * 0.36⟩
          st.tickSize st.inkMuted .finish)
  if st.minorTicks && l.categories.isEmpty then
    for v in l.sy.minor do
      if let some y := yPos v then
        ticks := (ticks.moveTo ⟨left - st.minorTickLength, crisp y⟩).lineTo ⟨left, crisp y⟩
  if !ticks.cmds.isEmpty then front := front.push (.path ticks none (some (hairline st.axis)))
  if l.xLabels && !p.x.label.isEmpty then
    let y := labelY + st.tickSize * tx.descent + st.labelGap * 0.5 + st.labelSize * tx.ascent
    front := front.push (.text p.x.label ⟨(a.x0 + a.x1) / 2, y⟩ st.labelSize st.inkSecondary
      .middle)
  if l.yLabels && !p.y.label.isEmpty then
    let widest := l.sy.major.foldl (fun m v => max m (tx.measure (formatTick l.sy v) st.tickSize))
      0
    let x := tickX - widest - st.labelGap - st.labelSize * tx.descent
    front := front.push (.text p.y.label ⟨x, (a.y0 + a.y1) / 2⟩ st.labelSize st.inkSecondary
      .middle 1 (-1.5707963267948966))
  if !p.title.isEmpty then
    front := front.push (.text p.title ⟨a.x0, a.y0 - st.titleGap * 0.6⟩ st.panelTitleSize
      st.inkPrimary .start 1.15)
  if !l.hasData then
    front := front.push (.text "No data" ⟨(a.x0 + a.x1) / 2, (a.y0 + a.y1) / 2⟩ st.noteSize
      st.inkMuted .middle)
  return (grid, front)

/-- The shapes of a panel's annotations. -/
def drawNotes (st : Style) (l : PanelLayout) (p : Panel) : Array Shape := Id.run do
  let a := l.area
  let mut out := #[]
  let ref : Line := { ink := st.inkMuted, width := 1, dash := #[4, 3] }
  for n in p.notes do
    match n with
    | .text at_ s anchor =>
      if let some q := l.toPx at_ then
        out := out.push (.text s q st.noteSize st.inkSecondary anchor)
    | .hline y label =>
      if let some y := l.sy.map a.y1 a.y0 y then
        out := out.push (.path (Path.polyline #[⟨a.x0, crisp y⟩, ⟨a.x1, crisp y⟩]) none
          (some ref))
        if !label.isEmpty then
          out := out.push (.text label ⟨a.x1 - 4, crisp y - 5⟩ st.noteSize st.inkSecondary
            .finish)
    | .vline x label =>
      if let some x := l.sx.map a.x0 a.x1 x then
        out := out.push (.path (Path.polyline #[⟨crisp x, a.y0⟩, ⟨crisp x, a.y1⟩]) none
          (some ref))
        if !label.isEmpty then
          out := out.push (.text label ⟨crisp x + 5, a.y0 + st.noteSize⟩ st.noteSize
            st.inkSecondary .start)
    | .point at_ label =>
      if let some q := l.toPx at_ then
        out := out.push (.path (circle q (st.markerRadius + 2)) none
          (some { ink := st.inkPrimary, width := 1.25 }))
        out := out.push (.text label ⟨q.x + 9, q.y - 8⟩ st.noteSize st.inkPrimary .start)
  return out

/-- The legend's swatch for an entry at `x` on the line through `mid`. -/
def swatchShapes (st : Style) (x mid : Float) (e : LegendEntry) : Array Shape :=
  let (_, c, dashed, kind) := e
  let sw := st.swatch
  let ln : Line :=
    { ink := c, width := st.lineWidth, cap := "round", dash := if dashed then #[6, 4] else #[] }
  let lineShape := Shape.path (Path.polyline #[⟨x, mid⟩, ⟨x + sw, mid⟩]) none (some ln)
  match kind with
  | "fill" => #[.path (barPath x (mid - 5) (x + sw) (mid + 5) 2 true) (some (.solid c)) none]
  | "marker" => #[marker st ⟨x + sw / 2, mid⟩ c st.markerRadius]
  | "line-marker" => #[lineShape, marker st ⟨x + sw / 2, mid⟩ c st.markerRadius]
  | _ => #[lineShape]

/-- The figure as a drawing on the canvas (see the module docstring). -/
def Figure.draw (fig : Figure) : Shape := Id.run do
  let st := fig.style
  let tx := st.text
  let mut out : Array Shape :=
    #[.path (rect 0 0 fig.width fig.height) (some (.solid st.background)) none]
  let mut top := st.margin
  if !fig.title.isEmpty then
    out := out.push (.text fig.title ⟨st.margin, top + st.titleSize * tx.ascent⟩ st.titleSize
      st.inkPrimary .start st.titleWeight)
    top := top + lineHeight st st.titleSize + st.titleGap
  if fig.showsLegend then
    for row in legendRows st fig.legendEntries (fig.width - 2 * st.margin) do
      let base := top + st.legendSize * tx.ascent
      let mid := base - st.legendSize * 0.33
      for (x, e) in row do
        let x := st.margin + x
        out := out ++ swatchShapes st x mid e
        out := out.push (.text e.1 ⟨x + st.swatch + 6, base⟩ st.legendSize st.inkSecondary
          .start)
      top := top + lineHeight st st.legendSize * 1.25
  for (p, l) in fig.panels.zip fig.layout do
    let (grid, front) := drawFrame st l p
    out := out ++ grid
    let pad := st.markerRadius + st.lineWidth + 1
    let clip := rect (l.area.x0 - pad) (l.area.y0 - pad) (l.area.width + 2 * pad)
      (l.area.height + 2 * pad)
    let mut marks := #[]
    let mut idx := 0
    for s in p.series do
      marks := marks ++ drawSeries st l s idx
      idx := idx + (match s with | .bars _ g .. => g.size | _ => 1)
    out := out.push (.group marks (clip := some clip))
    out := out ++ front
    out := out ++ drawNotes st l p
  return .group out

/-- The figure as an SVG document, text as SVG text (or as shapes when `outlines`). -/
def Figure.toSvg (fig : Figure) (outlines : Bool := false) : String :=
  fig.draw.toSvg fig.width fig.height fig.style.fontFamily
    (if outlines then some fig.style.text else none)

/-- The figure as an RGB image of its size in pixels, text drawn by the style's text engine. -/
def Figure.toImage (fig : Figure) : Image :=
  let w := fig.width.round.toUInt64.toNat
  let h := fig.height.round.toUInt64.toNat
  (Raster.Svg.rasterize w h (fig.draw.render (.shapes fig.style.text)) fig.style.background
    ).toImage .rgb

/-- The figure as PNG bytes (deterministic); `none` for a figure of no pixels. -/
def Figure.toPng (fig : Figure) (md : Png.Metadata := {}) : Option ByteArray :=
  match fig.toImage.writePng md with
  | .ok b => some b
  | .error _ => none

end PILean.Plot
