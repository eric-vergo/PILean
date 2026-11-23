/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plot.Figure

/-!
# Labelling checks of plots

A plot a reader cannot read without asking what its axes or its curves are is reported, in the
manner of the layout checks of plane figures (`PILean.Plane.Check`), as a list of problems, one
panel at a time:

* `noXLabel`, `noYLabel`: the panel's horizontal or vertical axis has no label (`Axis.label`).
* `unnamedSeries`: the panel has two or more series (each group of a bar series counts as one),
  and not every one of them is named by the legend (a figure's legend is drawn, and lists a
  series by its label, when the figure has more than one labelled series) or by a direct label
  in the panel (an annotation `text` or `point` whose text is the series' label).

* `darkThemeClash`: a page that shows the plot inline in its dark theme restyles each colour by
  its light value (`Style.darkColourPairs`, the first pairing of a light colour kept), so a fixed
  colour (a series', a bar group's or a band's `color`) equal to a colour of the style comes out
  as that colour's dark twin, as for the fixed colours of plane figures (`PILean.Plane.Check`).
  (A style has a dark twin only when its colours are the default light ones, whose light values
  each have one dark twin, so a plot's own colours do not clash.)

A panel that is bare on purpose (`Panel.bare`) is not checked for labels; a figure's `checks` level
(`CheckLevel`) says whether the problems are reported (`warn`, the default), stop its rendering
(`fail`) or are not looked for (`ignore`), as for plane figures.

## Main definitions

* `ProblemKind`, `Problem`, `Panel.seriesNames`, `Panel.fixedColours`, `Figure.problems`,
  `Figure.checkMessages`.
-/

namespace PILean.Plot

/-- The kinds of problem (see the module docstring). -/
inductive ProblemKind where
  /-- The horizontal axis has no label. -/
  | noXLabel
  /-- The vertical axis has no label. -/
  | noYLabel
  /-- Several series, not all of them named. -/
  | unnamedSeries
  /-- A colour would come out other than its dark twin's in the dark theme of a page that shows
  the plot inline. -/
  | darkThemeClash
  deriving BEq, Inhabited, Repr

/-- A problem: its kind, the panel's position in `Figure.panels` and a message. -/
structure Problem where
  /-- The kind. -/
  kind : ProblemKind
  /-- The panel, by position. -/
  panel : Nat
  /-- What is wrong, in words. -/
  message : String
  deriving Inhabited, Repr

/-- The names of a panel's series as a legend lists them, one for each series and one for each
group of a bar series (empty for a series without a label). -/
def Panel.seriesNames (p : Panel) : Array String :=
  p.series.flatMap fun s => match s with
    | .bars _ groups .. => groups.map (·.1)
    | .line l .. | .scatter l .. | .step l .. | .area l .. | .band l .. | .histogram l ..
    | .function l .. | .errorBars l .. => #[l]

/-- The texts of a panel's direct labels: its `text` and `point` annotations. -/
def Panel.directLabels (p : Panel) : Array String :=
  p.notes.filterMap fun a => match a with
    | .text _ s _ | .point _ s => some s
    | _ => none

/-- The colours a panel's series and bands fix (`color`, a bar series' `colors`), in order. -/
def Panel.fixedColours (p : Panel) : Array Rgba :=
  (p.series.flatMap fun s => match s with
    | .bars _ _ _ cs => cs
    | .line _ _ c .. | .scatter _ _ c .. | .step _ _ c .. | .area _ _ _ c | .band _ _ _ _ _ c
    | .histogram _ _ _ _ c | .function _ _ _ _ c .. | .errorBars _ _ _ c => c.toArray) ++
  p.notes.flatMap fun a => match a with
    | .hband _ _ _ c | .vband _ _ _ c => c.toArray
    | _ => #[]

/-- How a panel is named in a message: its title, or its position. -/
def Panel.name (p : Panel) (i : Nat) : String :=
  if p.title.isEmpty then s!"panel {i}" else s!"panel {i} (“{p.title}”)"

/-- The labelling problems of a figure (see the module docstring). -/
def Figure.problems (fig : Figure) : Array Problem := Id.run do
  let mut out : Array Problem := #[]
  let legend := fig.showsLegend
  for h : i in [0:fig.panels.size] do
    let p := fig.panels[i]
    if p.bare then continue
    if p.x.label.isEmpty then
      out := out.push ⟨.noXLabel, i, s!"{p.name i}: the horizontal axis has no label \
        (Axis.label; Panel.bare for a panel bare on purpose)"⟩
    if p.y.label.isEmpty then
      out := out.push ⟨.noYLabel, i, s!"{p.name i}: the vertical axis has no label \
        (Axis.label; Panel.bare for a panel bare on purpose)"⟩
    let names := p.seriesNames
    let named := legend && names.all (!·.isEmpty)
    let direct := names.all fun n => !n.isEmpty && p.directLabels.contains n
    if names.size ≥ 2 && !named && !direct then
      out := out.push ⟨.unnamedSeries, i, s!"{p.name i}: {names.size} series, which neither \
        the legend nor direct labels with their labels name (Figure.legend, Annotation.text)"⟩
  -- colours the dark theme of an inline picture would restyle wrongly
  let pairs := fig.style.darkColourPairs
  for h : i in [0:fig.panels.size] do
    for c in fig.panels[i].fixedColours do
      if let some (_, shown) := pairs.find? (·.1 == c.rgbHex) then
        if shown != c.rgbHex then
          out := out.push ⟨.darkThemeClash, i, s!"{fig.panels[i].name i}: the fixed colour \
            {c.rgbHex} equals a colour of the style and comes out {shown} in the dark theme of \
            an inline picture; choose a colour the style does not have"⟩
  return out

/-- The messages of the figure's labelling problems, unless its `checks` level is `ignore`. -/
def Figure.checkMessages (fig : Figure) : Array String :=
  if fig.checks == .ignore then #[] else fig.problems.map (·.message)

end PILean.Plot
