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

**Plane figures** (`PILean.Plane`) take their colours from `Style.plane`, a `PlaneStyle`: an ink
for points, lines and labels, three accents, a faint colour for construction lines, the
opacity of tinted fills, and the sizes of strokes, markers, arrowheads and labels in pixels. The
background is the style's `background`. A figure can name further colour roles (`PlaneRole`:
`"left"`, `"chord"`), each with a light and a dark colour, so that its dark twin needs nothing
more. Light and dark values meet the WCAG contrast requirements on their backgrounds (checked by
the tests with `contrast`): the ink at least 7:1 and every accent and the faint colour at least
4.5:1 on the background, so that each can colour a label; on a fill tinted with one accent at
`fillOpacity` (mixed in sRGB, as both PILean's images of plane figures and browsers composite),
the ink at least 7:1, that accent at least 4.5:1 and the faint colour at least 3:1. The accents are
Okabe and Ito's blue, vermilion and bluish green, darkened (light) or lightened (dark) to meet
these ratios. A figure's own colours are checked where they are drawn (`PILean.Plane.Check`).

## Main definitions

* `Style`, `Style.light`, `Style.dark`, `Style.seriesColor`, `Style.darkTwin?`,
  `Style.darkColourPairs`.
* `PlaneRole`, `PlaneStyle`, `PlaneStyle.light`, `PlaneStyle.dark`, `PlaneStyle.accent`,
  `PlaneStyle.role?`.
-/

namespace PILean

/-- A named colour role of plane figures (`"left"`, `"chord"`, `"region"`) with its colour for
light and for dark surfaces. -/
structure PlaneRole where
  /-- The role's name. -/
  name : String
  /-- The colour on light surfaces. -/
  light : Rgba
  /-- The colour on dark surfaces. -/
  dark : Rgba
  deriving Inhabited, BEq, Repr

/-- The colours and sizes of plane figures (see the module docstring). Lengths are in pixels,
whatever the scale of the figure. -/
structure PlaneStyle where
  /-- Points, lines, outlines and labels. -/
  ink : Rgba := ⟨24, 24, 27, 255⟩
  /-- The accent colours, in order (`PlaneStyle.accent` wraps round). -/
  accents : Array Rgba := #[⟨0, 104, 166, 255⟩, ⟨180, 68, 0, 255⟩, ⟨0, 120, 82, 255⟩]
  /-- Construction lines and inactive elements. -/
  faint : Rgba := ⟨116, 116, 126, 255⟩
  /-- The opacity of the tint that fills disks, sectors and filled polygons. -/
  fillOpacity : Float := 0.12
  /-- The width of lines and outlines. -/
  lineWidth : Float := 2
  /-- The radius of a point's marker. -/
  markerRadius : Float := 3.5
  /-- The ring of background colour around a marker. -/
  markerRing : Float := 1.25
  /-- The length of an arrowhead. -/
  arrowLength : Float := 10
  /-- The half-width of an arrowhead at its base. -/
  arrowHalfWidth : Float := 4.5
  /-- The size of labels. -/
  labelSize : Float := 15
  /-- The gap between a label and the point it labels. -/
  labelOffset : Float := 6
  /-- The radius of an angle mark. -/
  angleRadius : Float := 24
  /-- The length of a tick mark across a line. -/
  tickLength : Float := 9
  /-- Named colour roles, each with a light and a dark colour (`Tone.role`). -/
  roles : Array PlaneRole := #[]
  /-- Whether these are the colours for dark surfaces (roles then take their dark colour). -/
  onDark : Bool := false
  deriving Inhabited, BEq

namespace PlaneStyle

/-- The plane colours for light surfaces. -/
def light : PlaneStyle := {}

/-- The plane colours for dark surfaces (the background of `Style.dark`). -/
def dark : PlaneStyle :=
  { ink := ⟨236, 236, 240, 255⟩,
    accents := #[⟨104, 182, 236, 255⟩, ⟨244, 142, 82, 255⟩, ⟨64, 192, 146, 255⟩],
    faint := ⟨140, 144, 154, 255⟩, fillOpacity := 0.1, onDark := true }

/-- Accent `i`, wrapping round the accents (the ink when there are none). -/
def accent (p : PlaneStyle) (i : Nat) : Rgba :=
  (p.accents[i % max p.accents.size 1]?).getD p.ink

/-- The colour of the role `name` (light or dark as the style is), if the style has it. -/
def role? (p : PlaneStyle) (name : String) : Option Rgba :=
  (p.roles.find? (·.name == name)).map fun r => if p.onDark then r.dark else r.light

/-- Whether two plane styles have the same colours, fill opacity and surface (sizes and roles,
which carry both colours, are not compared). -/
def sameColours (a b : PlaneStyle) : Bool :=
  a.ink == b.ink && a.accents == b.accents && a.faint == b.faint &&
    a.fillOpacity == b.fillOpacity && a.onDark == b.onDark

/-- `p` with the colours, fill opacity and surface of `q`; its sizes and roles kept. -/
def withColoursOf (p q : PlaneStyle) : PlaneStyle :=
  { p with ink := q.ink, accents := q.accents, faint := q.faint, fillOpacity := q.fillOpacity,
           onDark := q.onDark }

end PlaneStyle

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
  /-- The colours and sizes of plane figures. -/
  plane : PlaneStyle := PlaneStyle.light
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
    edge := ⟨112, 118, 130, 255⟩, plane := PlaneStyle.dark }

/-- Whether two styles have the same colours (background, inks, axis, grid, palette, the graph
colours and the plane colours); sizes, fonts and the text engine are not compared. -/
def sameColours (a b : Style) : Bool :=
  a.background == b.background && a.inkPrimary == b.inkPrimary &&
    a.inkSecondary == b.inkSecondary && a.inkMuted == b.inkMuted && a.axis == b.axis &&
    a.grid == b.grid && a.gridMinor == b.gridMinor && a.palette == b.palette &&
    a.nodeFill == b.nodeFill && a.nodeStroke == b.nodeStroke && a.edge == b.edge &&
    a.plane.sameColours b.plane

/-- The dark twin of a style in the light colours: the colours of `Style.dark` (and the dark
colours of its plane roles), everything else kept; `none` for a style in other colours, which an
author chose for one background. -/
def darkTwin? (s : Style) : Option Style :=
  if sameColours s light then
    let d := dark
    some { s with
      background := d.background, inkPrimary := d.inkPrimary, inkSecondary := d.inkSecondary,
      inkMuted := d.inkMuted, axis := d.axis, grid := d.grid, gridMinor := d.gridMinor,
      palette := d.palette, nodeFill := d.nodeFill, nodeStroke := d.nodeStroke, edge := d.edge,
      plane := s.plane.withColoursOf d.plane }
  else none

/-- The colours of a light style paired with those of its dark twin, as `#rrggbb` text, each
light colour once (the first pairing kept): what a page restyles an inline picture with in the
dark theme. Empty for a style without a dark twin. -/
def darkColourPairs (s : Style) : Array (String × String) :=
  match s.darkTwin? with
  | none => #[]
  | some d =>
    let hex := Rgba.rgbHex
    let pairs : Array (Rgba × Rgba) :=
      #[(s.background, d.background), (s.inkPrimary, d.inkPrimary),
        (s.inkSecondary, d.inkSecondary), (s.inkMuted, d.inkMuted), (s.axis, d.axis),
        (s.grid, d.grid), (s.gridMinor, d.gridMinor), (s.nodeFill, d.nodeFill),
        (s.nodeStroke, d.nodeStroke), (s.edge, d.edge), (s.plane.ink, d.plane.ink),
        (s.plane.faint, d.plane.faint)] ++ s.palette.zip d.palette ++
        s.plane.accents.zip d.plane.accents ++ s.plane.roles.map (fun r => (r.light, r.dark))
    pairs.foldl (init := #[]) fun acc (a, b) =>
      if acc.any (·.1 == hex a) then acc else acc.push (hex a, hex b)

/-- The colour of series `i` (wrapping round the palette) and whether it is dashed (from the
second round on). -/
def seriesColor (s : Style) (i : Nat) : Rgba × Bool :=
  let n := max s.palette.size 1
  ((s.palette[i % n]?).getD s.inkPrimary, i ≥ n)

end Style

end PILean
