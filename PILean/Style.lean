/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Color
import PILean.Text.Engine

/-!
# Styles

Every visual constant of PILean's plots and graphs in one record, `Style`, so that a change of
look is a change of one field. `Style.light` is the default and `Style.dark` its counterpart for
dark surfaces; both are built from the same rules:

* **Ink.** Text in three steps (primary for titles, secondary for axis labels and legends,
  muted for tick labels), never in a series colour. Axes are a mid grey and the grid a hairline
  barely darker than the page, so that data marks carry the contrast.
* **Palette.** The colours of Okabe and Ito's colour-blind-safe set, in an order whose
  neighbours stay apart under the common colour-vision deficiencies (checked for the light and
  the dark surface with a palette validator: lightness band, chroma, CVD and normal-vision
  separation of adjacent colours); the dark palette is the same hues stepped for the dark
  surface. A seventh series takes the first colour again with a dash.
* **Measure.** Sizes in pixels at 1×: 15 px titles, 12.5 px axis labels, 11 px tick labels;
  1-pixel hairlines on pixel centres; 2-pixel data lines with round joins; 3-pixel markers with
  a ring of the page colour; margins on an 8-pixel grid.

## Main definitions

* `Style`, `Style.light`, `Style.dark`, `Style.seriesColor`.
-/

namespace PILean

/-- The visual constants of plots and graphs (see the module docstring). Every length is in
pixels. -/
structure Style where
  /-- The page. -/
  background : Rgba := ⟨255, 255, 255, 255⟩
  /-- Titles. -/
  inkPrimary : Rgba := ⟨24, 24, 27, 255⟩
  /-- Axis labels, legend labels, annotations. -/
  inkSecondary : Rgba := ⟨72, 72, 80, 255⟩
  /-- Tick labels, notes. -/
  inkMuted : Rgba := ⟨112, 112, 120, 255⟩
  /-- Axis lines and ticks. -/
  axis : Rgba := ⟨150, 150, 158, 255⟩
  /-- Major grid lines. -/
  grid : Rgba := ⟨234, 234, 238, 255⟩
  /-- Minor grid lines (drawn when `minorGrid`). -/
  gridMinor : Rgba := ⟨244, 244, 247, 255⟩
  /-- The series colours, in order. -/
  palette : Array Rgba := #[⟨0, 114, 178, 255⟩, ⟨230, 159, 0, 255⟩, ⟨0, 158, 115, 255⟩,
    ⟨213, 94, 0, 255⟩, ⟨204, 121, 167, 255⟩, ⟨86, 180, 233, 255⟩]
  /-- The font family of SVG text. -/
  fontFamily : String := "Inter, \"Helvetica Neue\", Helvetica, Arial, sans-serif"
  /-- The engine that measures text (for layout) and draws it as shapes (for images). -/
  text : TextEngine := TextEngine.lettering
  /-- Title size. -/
  titleSize : Float := 15
  /-- Weight of titles (1 is the regular stroke). -/
  titleWeight : Float := 1.3
  /-- Panel title size. -/
  panelTitleSize : Float := 12.5
  /-- Axis label size. -/
  labelSize : Float := 12
  /-- Tick label size. -/
  tickSize : Float := 11
  /-- Legend label size. -/
  legendSize : Float := 11.5
  /-- Annotation size. -/
  noteSize : Float := 11
  /-- Outer margin. -/
  margin : Float := 16
  /-- Gap between a title and what follows. -/
  titleGap : Float := 10
  /-- Gap between panels. -/
  panelGap : Float := 24
  /-- The room, in pixels, between the extreme data of a plot and its frame: the vertical
  scale (and the horizontal one of a panel with data points) is widened by this much at each
  end, so that curves and markers never touch or cross the frame; not below a zero baseline of
  bars or areas, nor beside categories. -/
  plotPadding : Float := 8
  /-- Gap between tick labels and the axis. -/
  tickLabelGap : Float := 6
  /-- Gap between an axis label and the tick labels. -/
  labelGap : Float := 8
  /-- Major tick length (outwards). -/
  tickLength : Float := 4
  /-- Minor tick length. -/
  minorTickLength : Float := 2
  /-- Data line width. -/
  lineWidth : Float := 2
  /-- Marker radius. -/
  markerRadius : Float := 3
  /-- Ring of page colour around markers. -/
  markerRing : Float := 1.25
  /-- Opacity of area fills. -/
  areaOpacity : Float := 0.18
  /-- Gap between bars of a group, as a fraction of the band. -/
  barGap : Float := 0.08
  /-- Gap between groups of bars, as a fraction of the band. -/
  groupGap : Float := 0.28
  /-- Corner radius of bar ends away from the baseline. -/
  barRadius : Float := 2
  /-- Gap of page colour between adjacent filled marks. -/
  fillGap : Float := 1
  /-- Error bar cap half-width. -/
  errorCap : Float := 3.5
  /-- Whether major grid lines are drawn. -/
  majorGrid : Bool := true
  /-- Whether minor grid lines are drawn. -/
  minorGrid : Bool := false
  /-- Whether minor ticks are drawn. -/
  minorTicks : Bool := true
  /-- Target number of major ticks on an axis of 400 px (scaled by the axis length). -/
  tickDensity : Nat := 6
  /-- Legend swatch length. -/
  swatch : Float := 18
  /-- Gap between legend entries. -/
  legendGap : Float := 16
  /-- Nodes of graphs: fill. -/
  nodeFill : Rgba := ⟨248, 248, 250, 255⟩
  /-- Nodes of graphs: outline. -/
  nodeStroke : Rgba := ⟨120, 120, 130, 255⟩
  /-- Edges of graphs. -/
  edge : Rgba := ⟨130, 130, 140, 255⟩
  /-- Node label size. -/
  nodeLabelSize : Float := 11
  /-- Edge width. -/
  edgeWidth : Float := 1.25
  /-- Corner radius of node boxes. -/
  nodeRadius : Float := 5
  deriving Inhabited

namespace Style

/-- The default style, for light surfaces. -/
def light : Style := {}

/-- The style for dark surfaces: the same rules, the ink and palette stepped for the dark
page. -/
def dark : Style :=
  { background := ⟨22, 24, 28, 255⟩, inkPrimary := ⟨236, 236, 240, 255⟩,
    inkSecondary := ⟨196, 198, 204, 255⟩, inkMuted := ⟨150, 154, 162, 255⟩,
    axis := ⟨104, 108, 118, 255⟩, grid := ⟨40, 44, 52, 255⟩, gridMinor := ⟨32, 35, 41, 255⟩,
    palette := #[⟨61, 143, 217, 255⟩, ⟨191, 130, 0, 255⟩, ⟨20, 163, 127, 255⟩,
      ⟨226, 103, 44, 255⟩, ⟨199, 111, 168, 255⟩, ⟨157, 144, 32, 255⟩],
    nodeFill := ⟨34, 37, 43, 255⟩, nodeStroke := ⟨120, 126, 138, 255⟩,
    edge := ⟨112, 118, 130, 255⟩ }

/-- The colour of series `i` (wrapping round the palette) and whether it is dashed (from the
second round on). -/
def seriesColor (s : Style) (i : Nat) : Rgba × Bool :=
  let n := max s.palette.size 1
  ((s.palette[i % n]?).getD s.inkPrimary, i ≥ n)

end Style

end PILean
