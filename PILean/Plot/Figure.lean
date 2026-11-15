/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plot.Ticks
import PILean.Svg

/-!
# Figures

A figure is a Lean value: a size, a title, axis labels and marks (lines through data points,
graphs of functions). `Figure.toSvg` lays it out and writes it as an SVG document.

## Main definitions

* `Theme`: the visual constants (palette, inks, type sizes, margins, stroke widths).
* `Mark`, `Figure`: the specification.
* `Figure.layout`: the plot area and the scales.
* `Figure.render`, `Figure.toSvg`: the SVG nodes and the document.

## Implementation notes

* The plot area has whole-pixel edges, and every one-pixel line (grid, axes, ticks) is drawn on a
  pixel centre (`crisp`), so that hairlines rasterise as one sharp pixel row or column.
* A function is sampled at `samples` equally spaced points; a sample whose value is not finite
  breaks the curve there. Data and curves are clipped to the plot area.
* The legend is drawn when a figure has more than one mark, inside the plot area at its top
  left, on a translucent plate whose width estimates the labels' width. Labels are plain SVG
  text in the theme's font family; measuring text waits for the text layer, so every label is
  anchored (start, middle or end) rather than measured.
-/

namespace PILean.Plot

open PILean Svg

/-- The visual constants of a figure. -/
structure Theme where
  /-- Colours of successive marks without their own: Okabe and Ito's colour-blind-safe palette
  (blue, vermilion, bluish green, reddish purple, orange, sky blue). -/
  palette : Array Rgba := #[⟨0, 114, 178, 255⟩, ⟨213, 94, 0, 255⟩, ⟨0, 158, 115, 255⟩,
    ⟨204, 121, 167, 255⟩, ⟨230, 159, 0, 255⟩, ⟨86, 180, 233, 255⟩]
  /-- The page. -/
  background : Rgba := ⟨255, 255, 255, 255⟩
  /-- Title ink. -/
  titleInk : Rgba := ⟨26, 26, 26, 255⟩
  /-- Axis label ink. -/
  labelInk : Rgba := ⟨51, 51, 51, 255⟩
  /-- Tick label ink. -/
  tickInk : Rgba := ⟨92, 92, 92, 255⟩
  /-- Axis lines and ticks. -/
  axisInk : Rgba := ⟨64, 64, 64, 255⟩
  /-- Grid lines. -/
  gridInk : Rgba := ⟨232, 232, 232, 255⟩
  /-- The font family of all text. -/
  fontFamily : String := "Helvetica Neue, Helvetica, Arial, sans-serif"
  /-- Title size (px). -/
  titleSize : Float := 15
  /-- Axis label size (px). -/
  labelSize : Float := 12.5
  /-- Tick label size (px). -/
  tickSize : Float := 11
  /-- Margins left, top, right, bottom (px), the top one without a title. -/
  margins : Float × Float × Float × Float := (64, 20, 24, 52)
  /-- The extra top margin a title takes. -/
  titleSpace : Float := 30
  /-- Tick length outwards (px). -/
  tickLength : Float := 5
  /-- Stroke width of data lines and curves (px). -/
  lineWidth : Float := 1.75
  /-- Marker radius of data points (px). -/
  markerRadius : Float := 2.75
  /-- The target number of ticks on each axis. -/
  ticks : Nat := 6
  deriving Inhabited

/-- What a figure draws. -/
inductive Mark where
  /-- A line through data points in order, with markers at the points when `markers`. -/
  | line (label : String) (points : Array Point) (color : Option Rgba := none)
      (markers : Bool := false)
  /-- The graph of `f` on `[x0, x1]`, sampled at `samples` points. -/
  | function (label : String) (f : Float → Float) (x0 x1 : Float) (samples : Nat := 400)
      (color : Option Rgba := none)
  deriving Inhabited

/-- A figure's specification. -/
structure Figure where
  /-- Width (px). -/
  width : Float := 640
  /-- Height (px). -/
  height : Float := 400
  /-- The title (none if empty). -/
  title : String := ""
  /-- The horizontal axis label. -/
  xLabel : String := ""
  /-- The vertical axis label. -/
  yLabel : String := ""
  /-- The marks, drawn in order. -/
  marks : Array Mark := #[]
  /-- The horizontal interval; by default the marks' extent widened to whole ticks. -/
  xDomain : Option (Float × Float) := none
  /-- The vertical interval; by default the marks' extent widened to whole ticks. -/
  yDomain : Option (Float × Float) := none
  /-- The theme. -/
  theme : Theme := {}
  deriving Inhabited

/-- The polylines a mark draws, in data coordinates. -/
def Mark.polylines : Mark → Array (Array Point)
  | .line _ ps _ _ => #[ps.filter fun p => !(p.x.isNaN || p.y.isNaN || p.x.isInf || p.y.isInf)]
  | .function _ f x0 x1 n _ => Id.run do
    let n := max n 2
    let mut out : Array (Array Point) := #[]
    let mut cur : Array Point := #[]
    for i in [0:n] do
      let x := x0 + (x1 - x0) * i.toFloat / (n - 1).toFloat
      let y := f x
      if y.isNaN || y.isInf then
        if cur.size > 1 then out := out.push cur
        cur := #[]
      else cur := cur.push ⟨x, y⟩
    if cur.size > 1 then out := out.push cur
    return out

/-- The mark's label. -/
def Mark.label : Mark → String
  | .line l .. | .function l .. => l

/-- The mark's own colour, if it has one. -/
def Mark.color? : Mark → Option Rgba
  | .line _ _ c _ => c
  | .function _ _ _ _ _ c => c

/-- The position `v` of `[lo, hi]` mapped onto `[a, b]` (the middle for an empty interval). -/
def mapLinear (lo hi a b v : Float) : Float :=
  if hi == lo then (a + b) / 2 else a + (v - lo) / (hi - lo) * (b - a)

/-- A one-pixel line's coordinate on the pixel centre nearest `v`. -/
def crisp (v : Float) : Float := v.floor + 0.5

/-- A figure laid out: the plot area (whole pixels) and the ticks of both axes. -/
structure Layout where
  /-- The plot area. -/
  area : Box
  /-- The horizontal ticks (their interval is the horizontal domain). -/
  xTicks : Ticks
  /-- The vertical ticks. -/
  yTicks : Ticks

/-- The extent of the marks' points, `none` without points. -/
def Figure.extent (fig : Figure) : Option Box :=
  Box.ofPoints (fig.marks.foldl (fun acc m => acc ++ (m.polylines.foldl (· ++ ·) #[])) #[])

/-- The figure's plot area and ticks. -/
def Figure.layout (fig : Figure) : Layout :=
  let th := fig.theme
  let (ml, mt, mr, mb) := th.margins
  let top := mt + (if fig.title.isEmpty then 0 else th.titleSpace)
  let area : Box := ⟨ml.round, top.round, (fig.width - mr).round, (fig.height - mb).round⟩
  let ext := fig.extent.getD ⟨0, 0, 1, 1⟩
  let xt := match fig.xDomain with
    | some (a, b) => niceTicks a b th.ticks (snap := false)
    | none => niceTicks ext.x0 ext.x1 th.ticks
  let yt := match fig.yDomain with
    | some (a, b) => niceTicks a b th.ticks (snap := false)
    | none => niceTicks ext.y0 ext.y1 th.ticks
  ⟨area, xt, yt⟩

/-- The point of the plot area showing data point `p`. -/
def Layout.toPx (l : Layout) (p : Point) : Point :=
  ⟨mapLinear l.xTicks.lo l.xTicks.hi l.area.x0 l.area.x1 p.x,
    mapLinear l.yTicks.lo l.yTicks.hi l.area.y1 l.area.y0 p.y⟩

/-- The id of the plot area's clip path. -/
def clipId : String := "plot-area"

/-- The figure as SVG nodes (the children of the document's root). -/
def Figure.render (fig : Figure) : Array Node := Id.run do
  let th := fig.theme
  let l := fig.layout
  let a := l.area
  let mut out : Array Node := #[rect 0 0 fig.width fig.height (some th.background)]
  -- The clip leaves room for half a stroke and a marker beyond the area, so that marks at the
  -- edge of the domain are drawn whole.
  let pad := th.markerRadius + th.lineWidth
  out := out.push (el "defs" #[] #[el "clipPath" #[("id", clipId)]
    #[rect (a.x0 - pad) (a.y0 - pad) (a.width + 2 * pad) (a.height + 2 * pad) none]])
  -- grid
  let mut grid : Array Node := #[]
  for v in l.xTicks.values do
    let x := crisp (l.toPx ⟨v, 0⟩).x
    grid := grid.push (line ⟨x, a.y0⟩ ⟨x, a.y1⟩ th.gridInk 1)
  for v in l.yTicks.values do
    let y := crisp (l.toPx ⟨0, v⟩).y
    grid := grid.push (line ⟨a.x0, y⟩ ⟨a.x1, y⟩ th.gridInk 1)
  out := out.push (group #[("class", "grid")] grid)
  -- marks
  let mut marks : Array Node := #[]
  for i in [0:fig.marks.size] do
    let some m := fig.marks[i]? | continue
    let ink := m.color?.getD (th.palette[i % max th.palette.size 1]?.getD th.axisInk)
    for pl in m.polylines do
      marks := marks.push (Svg.path (Path.polyline (pl.map l.toPx)) none (some ink) th.lineWidth
        #[("stroke-linejoin", "round"), ("stroke-linecap", "round")])
    if let .line _ ps _ true := m then
      for p in ps do
        let q := l.toPx p
        marks := marks.push (Svg.path (Path.ellipse q th.markerRadius th.markerRadius)
          (some th.background) (some ink) 1.25)
  out := out.push (group #[("class", "marks"), ("clip-path", s!"url(#{clipId})")] marks)
  -- axes and ticks
  let left := crisp a.x0
  let bottom := crisp a.y1
  let mut axes : Array Node := #[line ⟨left, a.y0⟩ ⟨left, a.y1 + 0.5⟩ th.axisInk 1,
    line ⟨left - 0.5, bottom⟩ ⟨a.x1, bottom⟩ th.axisInk 1]
  let mut labels : Array Node := #[]
  for v in l.xTicks.values do
    let x := crisp (l.toPx ⟨v, 0⟩).x
    axes := axes.push (line ⟨x, bottom⟩ ⟨x, bottom + th.tickLength⟩ th.axisInk 1)
    labels := labels.push (text x (a.y1 + th.tickLength + th.tickSize + 3) (tickLabel l.xTicks v)
      th.tickSize th.tickInk .middle)
  for v in l.yTicks.values do
    let y := crisp (l.toPx ⟨0, v⟩).y
    axes := axes.push (line ⟨left - th.tickLength, y⟩ ⟨left, y⟩ th.axisInk 1)
    labels := labels.push (text (left - th.tickLength - 4) (y + th.tickSize * 0.35)
      (tickLabel l.yTicks v) th.tickSize th.tickInk .finish)
  out := out.push (group #[("class", "axes")] axes)
  out := out.push (group #[("class", "tick-labels"), ("font-variant-numeric", "tabular-nums")]
    labels)
  -- axis labels and title
  let mut texts : Array Node := #[]
  if !fig.xLabel.isEmpty then
    texts := texts.push (text ((a.x0 + a.x1) / 2) (fig.height - 12) fig.xLabel th.labelSize
      th.labelInk .middle)
  if !fig.yLabel.isEmpty then
    let cy := (a.y0 + a.y1) / 2
    texts := texts.push (text 18 cy fig.yLabel th.labelSize th.labelInk .middle
      #[("transform", s!"rotate(-90 18 {fmtNum cy})")])
  if !fig.title.isEmpty then
    texts := texts.push (text a.x0 (th.margins.2.1 + th.titleSize) fig.title th.titleSize
      th.titleInk .start #[("font-weight", "600")])
  -- legend
  if fig.marks.size > 1 then
    let x := a.x0 + 14
    -- A plate behind the legend; its width estimates the labels at 0.56 em a character.
    let longest := fig.marks.foldl (fun m mk => max m mk.label.length) 0
    let w := 26 + 0.56 * th.tickSize * longest.toFloat + 22
    let h := 18 * fig.marks.size.toFloat + 10
    texts := texts.push (rect (x - 10) (a.y0 + 6) w.round h (some th.background)
      #[("fill-opacity", "0.88"), ("rx", "3")])
    for i in [0:fig.marks.size] do
      let some m := fig.marks[i]? | continue
      let ink := m.color?.getD (th.palette[i % max th.palette.size 1]?.getD th.axisInk)
      let y := a.y0 + 16 + 18 * i.toFloat
      texts := texts.push (Svg.path (Path.polyline #[⟨x, y⟩, ⟨x + 18, y⟩]) none (some ink)
        th.lineWidth #[("stroke-linecap", "round")])
      texts := texts.push (text (x + 26) (y + th.tickSize * 0.35) m.label th.tickSize th.labelInk
        .start)
  out := out.push (group #[("class", "text")] texts)
  return #[group #[("font-family", th.fontFamily)] out]

/-- The figure as an SVG document. -/
def Figure.toSvg (fig : Figure) : String := document fig.width fig.height fig.render

end PILean.Plot
