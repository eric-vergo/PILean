/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plane.MotionOutput

/-!
# Several motions as panels of one picture, on one clock

A `MotionPanels` value puts several motions of plane figures (`Motion`, each a *panel* with its
own key figures, steps and moves and its own view) side by side, or one above another, in one
`<svg>` and on one timeline: step `k` of the picture is step `k` of every panel, so that what the
panels show at a key is shown at the same moment. The captions, the pacing and the title and
description are the picture's.

* **One timeline.** All panels have the same number of keys. Step `j` of the picture is idle when
  every panel's step `j` is idle; otherwise it takes the duration of the longest kind of move any
  panel makes in it (a panel without moves in a step idles while the others move), or the
  picture's own duration for the step (`MotionPanels.timing`); a panel's step does not set a
  duration or an easing of its own. A morph sampled in one panel (`Motion.between`) divides the
  step for every panel at the same times (`sampledSegments`), so the other panels' turns follow
  their eased motion piecewise linearly there, as in a single motion; two panels that sample one
  step in different numbers of intervals are an error. Every panel is laid out on this timeline
  (`Motion.planOn`), so every animation element of the picture has its timing
  (`MotionPanelsReport.panel_anim_eq`).
* **The layout.** Each panel gets a share of the width (`beside`, proportional to its content, or
  the shares given) or the whole width (`stacked`), a title above it, and a frame of its own: at
  one common scale for all panels (`PanelScale.common`: the smallest of the scales at which each
  fits its share, every panel centred again at that scale, so that a unit length is as long in
  every panel), or each at its own (`PanelScale.independent`, for a panel that zooms in). The
  panels are placed by shifting the origin of each panel's frame on the page; no `transform` is
  written. The narrow rendition (`MotionPanels.narrow`) stacks the panels at the narrow width.
* **Ids.** Every id, every reference to one and every `data-pilean-actor` of panel `i` carries the
  prefix `p{i + 1}-` (`panelPrefix`; the poster's `poster-p{i + 1}-`), so that two panels may use
  the same actor ids: prefixed ids of different panels differ (`panelPrefix_append_ne`).
* **Stills.** Key `k` of the picture (`MotionPanelsReport.stillShape`, `keyStillSvg`,
  `keyStillPng`) is the composition of the panels' key-`k` stills (`Motion.keyFigure` of each
  panel as laid out, `MotionPanelsReport.panelKeyFigure?`), each drawn in its panel's shifted
  frame, under the titles.
* **Checks.** `MotionPanels.report` gives every problem of every panel as a motion (the arrival
  and step checks, the layout checks of its keys, the stacking order, the rest check of its whole
  drawing against its stills and its writer against its baker, all on the shared timeline),
  labelled with the panel, then the problems of the picture: unequal numbers of keys, captions
  that are not one per key, sampling the panels disagree on, two panels with one title, a panel
  whose content does not fit its share, a panel's own step timing, a line or a ray in a panel
  (drawn to the edge of the whole page), panels on different backgrounds, and the composed
  picture's own rest check and writer against baker. `checks := .fail` by default: then
  `svg?` and `animation?` write nothing for a picture with errors; the routes that write whatever
  the problems say end in `Unchecked`.

## Main definitions

* `MotionPanel`, `PanelTiming`, `PanelScale`, `PanelArrangement`, `MotionPanels`,
  `MotionPanels.WellFormed`, `MotionPanels.narrow`, `panelPrefix`, `prefixPanel`.
* `MotionPanels.stepAt`, `MotionPanels.animSteps`, `MotionPanels.baseTimeline`,
  `MotionPanels.timelineOf`.
* `PanelPlace`, `PanelsLayout`, `MotionPanels.layout`, `MotionPanels.panelMotion`.
* `PanelReport`, `MotionPanelsReport`, `MotionPanels.report`, `MotionPanelsReport.svg?`,
  `MotionPanelsReport.animation?`, `MotionPanelsReport.svgRootUnchecked`,
  `MotionPanelsReport.figureAtUnchecked`, `MotionPanelsReport.stillShape`,
  `MotionPanelsReport.keyStillSvg`, `MotionPanelsReport.keyStillPng`.

## Main results

* `MotionPanels.timelineOf_keys`, `MotionPanelsReport.timeline_keys`: the shared timeline has the
  picture's number of keys.
* `MotionPanels.report_timeline`: every panel's plans are laid out on the shared timeline.
* `MotionPanelsReport.panel_anim_eq`: every animation element a panel's plan builds has the timing
  of the shared timeline.
* `panelPrefix_append_ne`: ids prefixed for different panels differ.
-/

namespace PILean.Plane

open Canvas Anim Svg

/-! ### The model -/

/-- How the panels are scaled. -/
inductive PanelScale where
  /-- One unit length for all panels: the smallest of the scales at which each fits its share. -/
  | common
  /-- Each panel fitted to its share on its own (a panel that zooms in). -/
  | independent
  deriving Inhabited, Repr, DecidableEq

/-- How the panels are arranged. -/
inductive PanelArrangement where
  /-- Side by side, from left to right. -/
  | beside
  /-- One above another, from top to bottom, each the whole width. -/
  | stacked
  deriving Inhabited, Repr, DecidableEq

/-- A panel: a motion with a title shown above it. The motion's own captions, pacing, title,
description, level of checks and poster are not used: those of the picture are. -/
structure MotionPanel where
  /-- The title shown above the panel (none when empty). -/
  title : String := ""
  /-- The motion. -/
  motion : Motion
  deriving Inhabited

/-- The timing of a step of the picture, where it is not the pacing's. -/
structure PanelTiming where
  /-- The duration in seconds. -/
  duration : Option Rat := none
  /-- The easing. -/
  easing : Option Easing := none
  deriving Inhabited

/-- Several motions as panels of one picture on one clock (see the module docstring). -/
structure MotionPanels where
  /-- The panels, in order (from left to right, or from top to bottom). -/
  panels : Array MotionPanel
  /-- One caption per key (`"Step 3 of 5: …"`), for the whole picture. -/
  captions : Array String := #[]
  /-- The durations, easing and seam. -/
  pacing : Pacing := {}
  /-- The timing of each step where it is not the pacing's: empty, or one per step. -/
  timing : Array PanelTiming := #[]
  /-- The title and description of the whole picture. -/
  info : ShapeInfo := {}
  /-- How the problems apply when the picture is rendered: by default an error stops it. -/
  checks : CheckLevel := .fail
  /-- The key shown as the still (under reduced motion, and as the poster). -/
  poster : Nat := 0
  /-- The room between two panels, in pixels. -/
  gap : Float := 24
  /-- How the panels are scaled. -/
  scale : PanelScale := .common
  /-- How the panels are arranged. -/
  arrangement : PanelArrangement := .beside
  /-- The width of the picture in pixels. -/
  width : Float := 720
  /-- A narrower width at which the picture is also rendered with its panels stacked. -/
  narrowWidth : Option Float := none
  /-- The shares of the width of the panels side by side (any positive numbers, one per panel);
  empty: proportional to their content (at one scale under `common`, to the width of each
  panel's key `0` under `independent`). -/
  shares : Array Float := #[]
  deriving Inhabited

/-- The id of panel `i` in the picture's SVG: `p1`, `p2`, …. -/
def panelId (i : Nat) : String := "p" ++ toString (i + 1)

/-- The prefix of the ids of panel `i`: `p1-`, `p2-`, …. -/
def panelPrefix (i : Nat) : String := panelId i ++ "-"

private theorem digits_dash {a b x y : List Char} (ha : ∀ c ∈ a, c.isDigit = true)
    (hb : ∀ c ∈ b, c.isDigit = true) (h : a ++ '-' :: x = b ++ '-' :: y) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons c b =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      have := hb c (by simp)
      rw [← h.1] at this
      exact absurd this (by decide)
  | cons c a ih =>
    cases b with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      have := ha c (by simp)
      rw [h.1] at this
      exact absurd this (by decide)
    | cons d b =>
      simp only [List.cons_append, List.cons.injEq] at h
      rw [h.1, ih (fun c hc => ha c (by simp [hc])) (fun c hc => hb c (by simp [hc])) h.2]

/-- Ids prefixed for two different panels differ, whatever they were: so the ids of a picture of
panels are unique when they are unique within each panel. -/
theorem panelPrefix_append_ne {i j : Nat} (h : i ≠ j) (x y : String) :
    panelPrefix i ++ x ≠ panelPrefix j ++ y := by
  intro e
  have e := congrArg String.toList e
  simp [panelPrefix, panelId, Nat.repr] at e
  have := digits_dash (fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)
    (fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc) e
  apply h
  have hi := @Nat.ofDigitChars_toDigits 10 (i + 1) (by decide) (by decide)
  have hj := @Nat.ofDigitChars_toDigits 10 (j + 1) (by decide) (by decide)
  have : i + 1 = j + 1 := by rw [← hi, ← hj, this]
  omega

/-- The tree with the prefix `pre` on every `id` and `data-pilean-actor`, and in every reference
`url(#…)`, at most `fuel` deep. -/
def prefixPanel (pre : String) : Nat → Node → Node
  | 0, n => n
  | _, .text t => .text t
  | fuel + 1, .element name attrs children =>
    let attrs := attrs.map fun (k, v) =>
      if k == "id" || k == "data-pilean-actor" then (k, pre ++ v)
      else if v.startsWith "url(#" then (k, "url(#" ++ pre ++ (v.drop 5).toString)
      else (k, v)
    .element name attrs (children.map (prefixPanel pre fuel))

namespace MotionPanels

variable (P : MotionPanels)

/-- The number of keys of the picture: that of its first panel. -/
def keyCount : Nat := ((P.panels[0]?).map (·.motion.keys.size)).getD 0

/-- The number of steps of the picture: one fewer than its keys. -/
def stepCount : Nat := P.keyCount - 1

/-- The picture has a panel; every panel has the picture's number of keys and one step fewer; a
caption per key; its poster among the keys; and the timing of no step or of every step. -/
def WellFormed : Prop :=
  0 < P.panels.size ∧
    (∀ p ∈ P.panels.toList, p.motion.keys.size = P.keyCount ∧
      p.motion.steps.size + 1 = P.keyCount) ∧
    P.captions.size = P.keyCount ∧ P.poster < P.keyCount ∧
    (P.timing.size = 0 ∨ P.timing.size = P.stepCount)

/-- Whether a picture of panels is well formed is decided by comparing sizes. -/
instance : Decidable P.WellFormed := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The name of panel `i` in messages: its title, or its number from 1. -/
def name (i : Nat) : String :=
  let t := (P.panels.getD i default).title
  if t.isEmpty then toString (i + 1) else t

/-- The narrow rendition: the picture at its `narrowWidth`, its panels stacked (and scaled as
the picture asks), if it has one. -/
def narrow : Option MotionPanels :=
  P.narrowWidth.map fun w =>
    { P with width := w, arrangement := .stacked, narrowWidth := none, shares := #[] }

/-! ### The shared timeline -/

/-- The timing of step `j` of the picture: idle when every panel's step `j` is idle, taking the
picture's duration for the step or the pacing's `idle` time, not eased; otherwise the picture's
duration for the step or the longest of the panels' (each as `Motion.animStep` times a step that
moves, a panel idle in it giving none), eased with the picture's easing for the step or the
pacing's. -/
def stepAt (j : Nat) : Step :=
  let o := P.timing.getD j {}
  let ss := P.panels.filterMap (·.motion.steps[j]?)
  if ss.all (·.kind == .idle) then
    { kind := .idle, dur := o.duration.getD P.pacing.idle, easing := o.easing.getD .linear }
  else
    let durs := (ss.filter (·.kind != .idle)).map fun s =>
      (Motion.animStep P.pacing { s with duration := none, easing := none }).dur
    { dur := o.duration.getD (durs.foldl max 0), easing := o.easing.getD P.pacing.easing }

/-- The steps of the picture's timeline. -/
def animSteps : Array Step := (Array.range P.stepCount).map P.stepAt

/-- The picture's timeline before any step is divided for a sampled morph. -/
def baseTimeline : Timeline := Timeline.build P.animSteps P.pacing

/-- The picture's timeline with the move of each step `j` divided into `samples j` segments
(`sampledSegments`). -/
def timelineOf (samples : Nat → Nat) : Timeline :=
  { P.baseTimeline with segments := (sampledSegments P.baseTimeline samples).map (·.1) }

/-- The shared timeline has one key more than the picture has steps. -/
theorem timelineOf_keys (samples : Nat → Nat) :
    (P.timelineOf samples).keys = P.stepCount + 1 := by
  simp [timelineOf, baseTimeline, Timeline.build, animSteps]

/-- The shared timeline of a well-formed picture has as many keys as each of its panels. -/
theorem timelineOf_keys_panel (h : P.WellFormed) (samples : Nat → Nat) {p : MotionPanel}
    (hp : p ∈ P.panels.toList) : (P.timelineOf samples).keys = p.motion.keys.size := by
  have h2 := h.2.1 p hp
  rw [timelineOf_keys, h2.1, stepCount]
  omega

end MotionPanels

/-! ### The layout -/

/-- Where a panel is: its frame on a page of its own (origin at its top left corner), the page
point of that corner, the baseline centre of its title, and whether its content fits its share
at its scale. -/
structure PanelPlace where
  /-- The frame on the panel's own page. -/
  frame : Frame
  /-- The page abscissa of the panel's top left corner. -/
  x : Float
  /-- The page ordinate of the panel's top left corner. -/
  y : Float
  /-- The baseline centre of the title. -/
  titleAt : Point
  /-- Whether the content fits the panel at its scale. -/
  fits : Bool
  deriving Inhabited

/-- The layout of a picture of panels: its size, the height of the band of titles, and each
panel's place. -/
structure PanelsLayout where
  /-- The width in pixels. -/
  width : Float
  /-- The height in pixels. -/
  height : Float
  /-- The height of the band of titles above each panel (`0` when no panel has a title). -/
  band : Float
  /-- The panels' places. -/
  places : Array PanelPlace
  deriving Inhabited

/-- The reaches of a motion's keys (`Figure.frame`): the items' reaches, or the corners of a key's
view; the box `[-1, 1]²` when none is finite. -/
def motionReaches (m : Motion) : Array Reach :=
  let rs := m.keys.flatMap fun f => match f.view with
    | some b => #[Reach.around ⟨b.x0, b.y0⟩ 0, Reach.around ⟨b.x1, b.y1⟩ 0]
    | none => f.items.flatMap (itemReaches f.style)
  let fin := rs.filter (·.finite)
  if fin.isEmpty then #[Reach.around ⟨-1, -1⟩ 0, Reach.around ⟨1, 1⟩ 0] else fin

/-- The padding of a motion: that of its key `0`. -/
def motionPadding (m : Motion) : Float := ((m.keys[0]?).map (·.padding)).getD 12

/-- The style of a motion: that of its key `0`. -/
def motionStyle (m : Motion) : Style := ((m.keys[0]?).map (·.style)).getD {}

/-- The least page width at which the reaches fit across at the scale `s` inside `pad`. -/
def widthAt (rs : Array Reach) (s pad : Float) : Float :=
  rs.foldl (fun a r => max a (s * r.at_.x + r.off.x1)) (-1e300) -
    rs.foldl (fun a r => min a (s * r.at_.x + r.off.x0)) 1e300 + 2 * pad

/-- The least page height at which the reaches fit down at the scale `s` inside `pad`. -/
def heightAt (rs : Array Reach) (s pad : Float) : Float :=
  2 * pad + rs.foldl (fun a r => max a (s * r.at_.y - r.off.y0)) (-1e300) +
    rs.foldl (fun a r => max a (r.off.y1 - s * r.at_.y)) (-1e300)

/-- Whether the reaches fit across a page `w` wide at the scale `s` inside `pad`. -/
def fitsAt (rs : Array Reach) (s w pad : Float) : Bool :=
  let (lo, hi) := originRange rs s w pad 1 (·.at_.x) (·.off.x0) (·.off.x1)
  lo ≤ hi + 1e-6

/-- The frame at the scale `s` of a page `w × h` with the reaches centred in it across, and down in
the height they need (`heightAt`), as `Frame.fit` centres them. -/
def frameAt (rs : Array Reach) (s w h pad : Float) : Frame :=
  let (lx, hx) := originRange rs s w pad 1 (·.at_.x) (·.off.x0) (·.off.x1)
  let ox := if lx ≤ hx then (lx + hx) / 2 else lx
  let top := rs.foldl (fun a r => max a (pad + s * r.at_.y - r.off.y0)) (-1e300)
  { scale := s, ox, oy := top + (h - heightAt rs s pad) / 2, width := w, height := h }

/-- The positive numbers `xs` scaled to add up to `total` (equal parts when they add up to no
more than zero). -/
def toShares (xs : Array Float) (total : Float) : Array Float :=
  let sum := xs.foldl (· + ·) 0
  if sum > 0 then xs.map (· * total / sum) else xs.map fun _ => total / xs.size.toFloat

namespace MotionPanels

variable (P : MotionPanels)

/-- The height of the band of titles: the largest title size and title gap of the panels' styles,
rounded up to a whole pixel; `0` when no panel has a title. -/
def band : Float :=
  if P.panels.all (·.title.isEmpty) then 0
  else (P.panels.foldl (fun a p =>
    let st := motionStyle p.motion
    max a (st.panelTitleSize + st.titleGap)) 0).ceil

/-- The widths of the panels side by side, `avail` pixels in all: the shares given; else, under
`common`, the least widths at which each panel fits at one scale (the largest scale at which they
add up to no more than `avail`), scaled to add up to `avail`; under `independent`, proportional to
the width of each panel's key `0`. -/
def besideWidths (avail : Float) : Array Float :=
  let ms := P.panels.map (·.motion)
  if !P.shares.isEmpty && P.shares.size == ms.size then toShares P.shares avail
  else match P.scale with
    | .independent => toShares (ms.map fun m => ((m.keys[0]?).map (·.width)).getD 1) avail
    | .common =>
      let fits := ms.map fun m => (motionReaches m, motionPadding m)
      let ok := fun (s : Float) =>
        (fits.map fun (rs, pad) => widthAt rs s pad).foldl (· + ·) 0 ≤ avail
      let sMax := (fits.map fun (rs, pad) => (Frame.fit rs avail none pad).scale).foldl min 1e300
      let s := largestScale ok sMax
      toShares (fits.map fun (rs, pad) => widthAt rs s pad) avail

/-- The layout of the picture (see the module docstring): each panel's width (`besideWidths`, or
the whole width when stacked) and scale (each panel's scale fitted to its width, `Frame.fit`, or
the smallest of them for all under `common`); side by side, every panel as tall as the tallest
needs at its scale, its content centred in it; stacked, each as tall as it needs. -/
def layout : PanelsLayout := Id.run do
  let ms := P.panels.map (·.motion)
  let n := ms.size
  let band := P.band
  let g := P.gap
  let titleSize := fun (m : Motion) => (motionStyle m).panelTitleSize
  let widths := match P.arrangement with
    | .stacked => ms.map fun _ => P.width
    | .beside => P.besideWidths (P.width - g * (n - 1).toFloat)
  let own := (ms.zip widths).map fun (m, w) =>
    (Frame.fit (motionReaches m) w none (motionPadding m)).scale
  let least := own.foldl min 1e300
  let scales := if P.scale == .common then own.map fun _ => least else own
  let heights := (ms.zip scales).map fun (m, s) =>
    (heightAt (motionReaches m) s (motionPadding m)).ceil
  let tallest := heights.foldl max 0
  let mut places : Array PanelPlace := #[]
  let mut x := 0
  let mut y := 0
  for i in [0:n] do
    let m := ms.getD i default
    let rs := motionReaches m
    let pad := motionPadding m
    let w := widths.getD i 0
    let s := scales.getD i 1
    match P.arrangement with
    | .stacked =>
      let h := heights.getD i 0
      let place : PanelPlace :=
        { frame := frameAt rs s w h pad, x := 0, y := y + band, titleAt := ⟨w / 2, y + titleSize m⟩,
          fits := fitsAt rs s w pad }
      places := places.push place
      y := y + band + h + g
    | .beside =>
      let place : PanelPlace :=
        { frame := frameAt rs s w tallest pad, x, y := band, titleAt := ⟨x + w / 2, titleSize m⟩,
          fits := fitsAt rs s w pad }
      places := places.push place
      x := x + w + g
  let height := match P.arrangement with
    | .stacked => max 0 (y - g)
    | .beside => band + tallest
  return { width := P.width, height, band, places }

/-- Panel `i` laid out as a motion on its own page: its keys in the frame of its place (`view`,
size, no padding), the picture's pacing, level of checks and poster, and its name as its title
and description (the picture's title, description and captions are checked once, for the
picture). -/
def panelMotion (L : PanelsLayout) (i : Nat) : Motion :=
  let m := (P.panels.getD i default).motion
  let f := (L.places.getD i default).frame
  { m with
    keys := m.keys.map fun k =>
      { k with view := some f.view, width := f.width, height := some f.height, padding := 0 },
    captions := m.keys.map fun _ => "", pacing := P.pacing, checks := P.checks,
    poster := if P.poster < m.keys.size then P.poster else 0,
    info := { title := P.name i, description := P.name i } }

end MotionPanels

/-- The environment `e` with the origin of its frame moved by `(x, y)` on the page. -/
def shiftEnv (e : Env) (x y : Float) : Env :=
  { e with frame := { e.frame with ox := e.frame.ox + x, oy := e.frame.oy + y } }

/-! ### The report -/

instance : Inhabited Env := ⟨{ frame := {}, style := {} }⟩

instance : Inhabited MotionKeys :=
  ⟨{ viewed := #[], placed := #[], figs := #[], env := { frame := {}, style := {} },
     mode := .native "" }⟩

instance : Inhabited MotionPlan :=
  ⟨{ env := { frame := {}, style := {} }, mode := .native "", timeline := default, phases := #[],
     clock := default, layers := #[], runs := #[], seam := none, background := default,
     keys := 0 }⟩

/-- A panel of a picture checked and laid out: its motion as laid out (`panelMotion`), its keys as
drawn, the prefix of its ids, its environment on the picture's page (its frame shifted to its
place), and its plan on the shared timeline in its own frame (for its checks) and on the page. -/
structure PanelReport where
  /-- The motion as laid out. -/
  motion : Motion
  /-- Its keys as drawn. -/
  keys : MotionKeys
  /-- The prefix of its ids (`panelPrefix`). -/
  idPrefix : String
  /-- Its environment on the picture's page. -/
  env : Env
  /-- Its plan on its own page. -/
  ownPlan : MotionPlan
  /-- Its plan on the picture's page. -/
  plan : MotionPlan
  deriving Inhabited

/-- A picture of panels with its layout, its shared timeline and its panels laid out on it, and
its problems, computed once (`MotionPanels.report`). -/
structure MotionPanelsReport where
  /-- The picture. -/
  figure : MotionPanels
  /-- Its layout. -/
  layout : PanelsLayout
  /-- The number of intervals each step's move is divided into. -/
  samples : Array Nat
  /-- The steps whose sampling the panels disagree on, with each panel's number of intervals. -/
  conflicts : Array (Nat × Array Nat)
  /-- The shared timeline. -/
  timeline : Timeline
  /-- The phase at each boundary of the shared timeline. -/
  phases : Array MotionPhase
  /-- The panels. -/
  panels : Array PanelReport
  /-- The problems. -/
  problems : Array MotionProblem

namespace MotionPanels

variable (P : MotionPanels)

/-- Panel `i` of the motions laid out `m` with its keys `K`, on the timeline `tl` with the phases
`phases`, placed as the layout `L` has it. -/
def panelReport (L : PanelsLayout) (tl : Timeline) (phases : Array MotionPhase) (i : Nat)
    (mK : Motion × MotionKeys) : PanelReport :=
  let (m, K) := mK
  let place := L.places.getD i default
  let e := shiftEnv K.env place.x place.y
  { motion := m, keys := K, idPrefix := panelPrefix i, env := e,
    ownPlan := m.planOn K K.env tl phases, plan := m.planOn K e tl phases }

/-- The number of intervals of step `j` for the panels laid out `mks`: the number of every panel
that samples a morph in it (`Motion.samplesOf`), when they agree; else one, with the numbers. -/
def sharedSamples (mks : Array (Motion × MotionKeys)) (j : Nat) : Nat × Option (Array Nat) :=
  let all := mks.map fun (m, K) => m.samplesOf K j
  let ns := all.filter (· > 1)
  match ns[0]? with
  | none => (1, none)
  | some n => if ns.all (· == n) then (n, none) else (1, some all)

/-- The picture laid out, before its problems. -/
def laidOut : MotionPanelsReport :=
  let L := P.layout
  let mks := (Array.range P.panels.size).map fun i =>
    let m := P.panelMotion L i
    (m, m.keysOf)
  let shared := (Array.range P.stepCount).map (sharedSamples mks)
  let samples := shared.map (·.1)
  let segs := sampledSegments P.baseTimeline fun j => samples.getD j 1
  let tl := P.timelineOf fun j => samples.getD j 1
  let phases := Motion.phasesOf segs
  { figure := P, layout := L, samples,
    conflicts := (shared.zipIdx.filterMap fun ((_, c), j) => c.map (j, ·)),
    timeline := tl, phases, problems := #[],
    panels := mks.mapIdx (panelReport L tl phases) }

/-- Every panel of the laid-out picture has its plans on the shared timeline. -/
theorem laidOut_timeline {pr : PanelReport} (h : pr ∈ P.laidOut.panels) :
    pr.plan.timeline = P.laidOut.timeline ∧ pr.ownPlan.timeline = P.laidOut.timeline := by
  simp only [laidOut, Array.mem_mapIdx] at h
  obtain ⟨i, _, rfl⟩ := h
  exact ⟨rfl, rfl⟩

end MotionPanels

namespace MotionPanelsReport

variable (r : MotionPanelsReport)

/-- The panels' styles: that of the first panel's key `0`. -/
def style : Style := ((r.panels[0]?).map (·.keys.env.style)).getD {}

/-- The text mode of the first panel. -/
def mode : TextMode := ((r.panels[0]?).map (·.keys.mode)).getD (.native "sans-serif")

/-- The page filled with the first panel's background colour. -/
def background : Shape :=
  .path (Canvas.rect 0 0 r.layout.width r.layout.height) (some (.solid r.style.background))

/-- The title of each panel that has one, as a shape centred above it in its style's panel title
size and weight and its ink, with its text mode. -/
def titles : Array (Shape × TextMode) :=
  (r.panels.zip r.figure.panels).zipIdx.filterMap fun ((pr, p), i) =>
    if p.title.isEmpty then none
    else
      let st := pr.keys.env.style
      let place := r.layout.places.getD i default
      some (.text (labelText p.title) place.titleAt st.panelTitleSize st.plane.ink .middle
        st.titleWeight, pr.keys.mode)

/-- The SVG nodes of the titles. -/
def titleNodes : Array Node := r.titles.flatMap fun (s, mode) => s.render mode

/-- Key `k` of panel `pr` drawn in its environment on the page, without its background. -/
def panelStill (pr : PanelReport) (k : Nat) : Shape :=
  .group ((pr.keys.figure k).items.flatMap (drawItem pr.env))

/-- Key `k` of the picture: the background, the titles, then each panel's key-`k` still
(`Motion.keyFigure` of the panel as laid out, without its background) drawn in its frame shifted
to its place. -/
def stillShape (k : Nat) : Shape :=
  .group (#[r.background] ++ r.titles.map (·.1) ++ r.panels.map (panelStill · k))

/-- The SVG nodes of key `k` of panel `pr`, its ids prefixed with `pre`. -/
def panelStillNodes (pr : PanelReport) (k : Nat) (pre : String) : Array Node :=
  ((panelStill pr k).render pr.keys.mode).map (prefixPanel pre 256)

/-- The SVG nodes of key `k` of the picture (`stillShape`), each panel's ids prefixed with its
prefix (`panelPrefix`). -/
def stillNodes (k : Nat) : Array Node :=
  r.background.render r.mode ++ r.titleNodes ++
    r.panels.flatMap fun pr => panelStillNodes pr k pr.idPrefix

/-- Key `k` of the picture as an SVG document (`stillNodes`). -/
def keyStillSvg (k : Nat) : String :=
  Svg.document r.layout.width.round r.layout.height.round (r.stillNodes k)

/-- The size of the picture in whole pixels. -/
def pixelSize : Nat × Nat :=
  (r.layout.width.round.toUInt64.toNat, r.layout.height.round.toUInt64.toNat)

/-- Key `k` of the picture as an RGB image, its text drawn by each panel's text engine,
composited in sRGB (as `Figure.toImage`). -/
def keyStillImage (k : Nat) : Image :=
  let (w, h) := r.pixelSize
  let nodes := r.background.render (.shapes r.style.text) ++
    r.titles.flatMap (fun (s, _) => s.render (.shapes r.style.text)) ++
    r.panels.flatMap fun pr => (panelStill pr k).render (.shapes pr.keys.env.style.text)
  (Raster.Svg.rasterize w h nodes r.style.background (space := .srgb)).toImage .rgb

/-- Key `k` of the picture as PNG bytes; `none` for a picture of no pixels. -/
def keyStillPng (k : Nat) : Option ByteArray := (r.keyStillImage k).writePng.toOption

/-- Key `k` of panel `i` as a figure on its own page (`Motion.keyFigure` of the panel as laid
out). -/
def panelKeyFigure? (i k : Nat) : Option Figure := (r.panels[i]?).map (·.keys.figure k)

/-- The text alternative of the picture: its description and the captions. -/
def description : String :=
  " ".intercalate ((if r.figure.info.description.isEmpty then [] else
    [r.figure.info.description]) ++ r.figure.captions.toList)

/-- The moving picture: each panel's (`MotionPlan.contentNodes`, its ids prefixed) in a group
marked `data-pilean-panel` with the panel's id, all inside the seam's fades when there are some
(built by the first panel's plan, on the shared timeline). -/
def liveNodes : Array Node :=
  let content := r.panels.mapIdx fun i pr =>
    el "g" #[("data-pilean-panel", panelId i)]
      (pr.plan.contentNodes.map (prefixPanel pr.idPrefix 256))
  match r.panels[0]? with
  | some pr =>
    match (seamOf r.timeline).bind fun s =>
        pr.plan.anim "animate" #[("attributeName", "opacity")] (s.map (fmtNum · 4)) with
    | some a => #[Smil.group a content]
    | none => content
  | none => content

/-- The root of the picture's animated SVG, whatever its problems: the title and the description
with the captions, the reduced-motion rule, the background, the titles, the moving picture
(`liveNodes`) in a group of class `pilean-motion-live`, and the poster key of the picture (each
panel's still, its ids prefixed with `poster-` and the panel's prefix) in a group of class
`pilean-motion-poster`. The root has `role="img"`. -/
def svgRootUnchecked : Node :=
  let w := r.layout.width.round
  let h := r.layout.height.round
  let poster := r.panels.flatMap fun pr =>
    panelStillNodes pr r.figure.poster ("poster-" ++ pr.idPrefix)
  let head := (if r.figure.info.title.isEmpty then #[] else
      #[el "title" #[] #[.text r.figure.info.title]]) ++
    (if r.description.isEmpty then #[] else #[el "desc" #[] #[.text r.description]])
  el "svg" #[("xmlns", "http://www.w3.org/2000/svg"), ("width", fmtNum w),
    ("height", fmtNum h), ("viewBox", s!"0 0 {fmtNum w} {fmtNum h}"), ("role", "img")]
    (head ++ #[Animation.reducedMotionStyle] ++ r.background.render r.mode ++ r.titleNodes ++
      #[el "g" #[("class", Animation.liveClass)] r.liveNodes,
        el "g" #[("class", Animation.posterClass)] poster])

/-- The picture as an animated SVG document, whatever its problems. -/
def toSvgUnchecked : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++ Svg.render 0 r.svgRootUnchecked ++ "\n"

/-- The opacity of the seam at the time `t` (the first panel's, on the shared timeline). -/
def seamAt (t : Float) : Float := ((r.panels[0]?).map (·.plan.seamAt t)).getD 1

/-- The picture at the time `t` (seconds) as a drawing, whatever its problems: the background,
the titles, then every panel's moving picture (`MotionPlan.contentAt`) inside the seam's
opacity. -/
def figureAtUnchecked (t : Float) : Shape :=
  .group (#[r.background] ++ r.titles.map (·.1) ++
    #[.group (r.panels.flatMap (·.plan.contentAt t)) Affine.id (r.seamAt t)])

/-- The marked points of every panel at the time `t` (`MotionPlan.markersAt`), actors named with
their panel's prefix, in the order of the document. -/
def markersAt (t : Float) : Array (String × Point × Float × Affine) :=
  r.panels.flatMap fun pr => (pr.plan.markersAt t).map fun (n, q, o, M) =>
    (if n.startsWith "actor " then "actor " ++ pr.idPrefix ++ (n.drop 6).toString else n, q, o, M)

/-- The number of actor layers and of upright groups of all panels. -/
def markerCounts : Nat × Nat :=
  (r.panels.foldl (fun a pr => a + (pr.plan.layers.filter fun L => L.version.actor.isSome).size)
    0, r.panels.foldl (fun a pr => a + (pr.plan.layers.map (·.uprights.size)).foldl (· + ·) 0) 0)

/-- The composed picture against its stills: at the middle of each key's rest, the whole baked
drawing (`figureAtUnchecked`) must be the picture's still of that key (`stillShape`) within the
rest tolerance (`drawingDiff`). -/
def restProblems : Array MotionProblem :=
  (Array.range r.figure.keyCount).filterMap fun k =>
    let t := Exact.toFloat (r.timeline.restTime k)
    (drawingDiff (drawnOf 256 Affine.id 1 (r.figureAtUnchecked t))
        (drawnOf 256 Affine.id 1 (r.stillShape k))).map fun why =>
      { severity := .error, message := s!"at the rest on key {k} the picture {why}" }

/-- The composed writer against the composed baker: at the middle of every segment of the shared
timeline, the written moving picture (`liveNodes`) read with `Smil.valueAt` must show what the
panels' bakers draw (`markersAt`, `markersDiff`). -/
def writerProblems : Array MotionProblem :=
  let nodes := r.liveNodes
  let (actors, ups) := r.markerCounts
  match r.timeline.segments.findSome? fun s =>
      let t := Exact.toFloat (s.start + s.dur / 2)
      (markersDiff (r.markersAt t) actors ups nodes t).map fun why =>
        s!"at {fmtNum t 3} s the written picture {why}" with
  | some msg => #[{ severity := .error, message := msg }]
  | none => #[]

/-- The problems of the picture as a whole (see the module docstring). -/
def figureProblems : Array MotionProblem := Id.run do
  let P := r.figure
  let err := fun (s : String) => ({ severity := .error, message := s } : MotionProblem)
  let strict := fun (s : String) =>
    ({ severity := if P.checks == .fail then .error else .note, message := s } : MotionProblem)
  let mut out : Array MotionProblem := #[]
  if P.panels.isEmpty then return #[err "the picture has no panels"]
  let n := P.keyCount
  for (p, i) in P.panels.zipIdx do
    if i > 0 && p.motion.keys.size != n then
      out := out.push (err s!"panel {P.name i} has {p.motion.keys.size} keys where panel \
        {P.name 0} has {n}; all panels need the same number of keys")
  if P.captions.size != n then
    out := out.push (err s!"the picture has {P.captions.size} captions for {n} keys")
  if !(P.poster < n) then
    out := out.push (err s!"the poster is key {P.poster}, which the picture does not have")
  if P.timing.size != 0 && P.timing.size != P.stepCount then
    out := out.push (err s!"the picture gives the timing of {P.timing.size} steps; it has \
      {P.stepCount}")
  if !P.shares.isEmpty then
    if P.shares.size != P.panels.size then
      out := out.push (err s!"the picture gives {P.shares.size} shares for {P.panels.size} \
        panels")
    else if P.shares.any fun s => !(s > 0) || !s.isFinite then
      out := out.push (err "a share of the width is not a positive number")
  if !(P.width - P.gap * (P.panels.size - 1).toFloat > 0) then
    out := out.push (err "the gaps leave no width for the panels")
  let mut titles : Array String := #[]
  for p in P.panels do
    if !p.title.isEmpty then
      if titles.contains p.title then
        out := out.push (err s!"two panels have the title {p.title}")
      titles := titles.push p.title
  let bg := r.style.background
  for (pr, i) in r.panels.zipIdx do
    let p := P.panels.getD i default
    for (s, j) in p.motion.steps.zipIdx do
      if s.duration.isSome || s.easing.isSome then
        out := out.push (err s!"panel {P.name i}: step {j + 1} sets its own duration or easing; \
          the timing of a step is the picture's (`MotionPanels.timing`)")
    for (fig, k) in p.motion.keys.zipIdx do
      if fig.items.any fun it => it.leaves.any (·.geom.clipped) then
        out := out.push (err s!"panel {P.name i}: key {k} has a line or a ray, which would be \
          drawn to the edge of the whole picture, not of the panel; draw a segment")
    if pr.keys.env.style.background != bg then
      out := out.push (err s!"panel {P.name i} is drawn on another background than panel \
        {P.name 0}")
    if !(r.layout.places.getD i default).fits then
      out := out.push (err s!"panel {P.name i}: its content does not fit its share of the width \
        ({fmtNum (r.layout.places.getD i default).frame.width 1} px) at its scale")
  for (j, ns) in r.conflicts do
    out := out.push (err s!"step {j + 1}: the panels sample a morph in different numbers of \
      intervals ({", ".intercalate (ns.toList.map toString)}); give them the same morphSamples")
  if P.info.title.isEmpty then
    out := out.push (strict "the picture has no title (it has role=\"img\")")
  if P.info.description.isEmpty && P.captions.all (·.isEmpty) then
    out := out.push (strict "the picture has neither a description nor captions (it has \
      role=\"img\")")
  return out

/-- The problems of every panel as a motion (`Motion.keyProblems`, and for a well-formed picture
`Motion.restProblems` and `Motion.writerProblems` of its plan on its own page, on the shared
timeline), each labelled with its panel. -/
def panelProblems : Array MotionProblem :=
  let P := r.figure
  r.panels.zipIdx.flatMap fun (pr, i) =>
    let own := pr.motion.keyProblems ++ (if !decide P.WellFormed then #[] else
      pr.motion.restProblems pr.keys pr.ownPlan ++ Motion.writerProblems pr.ownPlan)
    own.map fun p => { p with message := s!"panel {P.name i}: {p.message}" }

/-- All the problems: the picture's (`figureProblems`), every panel's (`panelProblems`), and, for
a well-formed picture without errors so far, the composed picture's rest check (`restProblems`)
and writer against baker (`writerProblems`). -/
def computeProblems : Array MotionProblem :=
  let base := r.figureProblems ++ r.panelProblems
  if !decide r.figure.WellFormed || base.any (·.severity == .error) then base
  else base ++ r.restProblems ++ r.writerProblems

end MotionPanelsReport

namespace MotionPanels

variable (P : MotionPanels)

/-- The picture checked (see the module docstring): laid out, with its problems. -/
def report : MotionPanelsReport := let r := P.laidOut; { r with problems := r.computeProblems }

/-- Every panel of the picture has its plans, on its own page and on the picture's, on the shared
timeline: one clock across the panels holds by construction. -/
theorem report_timeline {pr : PanelReport} (h : pr ∈ P.report.panels) :
    pr.plan.timeline = P.report.timeline ∧ pr.ownPlan.timeline = P.report.timeline :=
  P.laidOut_timeline h

/-- The problems of the picture (`report`). -/
def problems : Array MotionProblem := P.report.problems

end MotionPanels

namespace MotionPanelsReport

variable (r : MotionPanelsReport)

/-- The messages of the problems a build reports (unless the level is `ignore`), each with its
severity. -/
def checkMessages : Array String :=
  if r.figure.checks == .ignore then #[]
  else r.problems.map fun p => match p.severity with
    | .error => p.message
    | .note => s!"note: {p.message}"

/-- Whether the problems stop the picture from being rendered: an error under `CheckLevel.fail`
(the default). -/
def problemsFail : Bool := r.figure.checks == .fail && r.problems.any (·.severity == .error)

/-- The messages of the errors. -/
def errors : Array String := (r.problems.filter (·.severity == .error)).map (·.message)

/-- The picture's animated SVG, or, when its problems stop it (`problemsFail`), the messages of its
errors. -/
def svg? : Except (Array String) String :=
  if r.problemsFail then .error r.errors else .ok r.toSvgUnchecked

/-- The picture as an `Animation` of its baked drawings, whatever its problems (they travel with
it): one cycle at `fps` frames a second, the poster at the middle of the poster key's rest. -/
def toAnimationUnchecked (fps : Nat := 30) : Animation :=
  let st := r.style
  let (w, h) := r.pixelSize
  { width := w, height := h, fps, duration := Exact.toFloat r.timeline.cycle,
    frame := r.figureAtUnchecked,
    posterTime := some (Exact.toFloat (r.timeline.restTime r.figure.poster)),
    background := st.background, fontFamily := st.fontFamily, text := st.text, srgb := true,
    textAsShapes := ((r.panels[0]?).bind fun pr => (pr.keys.figs[0]?).map (·.textAsShapes)).getD
      true,
    problems := fun _ => r.checkMessages, problemsFail := r.problemsFail }

/-- The picture as an `Animation` (`toAnimationUnchecked`), or the messages of the errors that stop
it. -/
def animation? (fps : Nat := 30) : Except (Array String) Animation :=
  if r.problemsFail then .error r.errors else .ok (r.toAnimationUnchecked fps)

/-- The shared timeline has one key more than the picture has steps. -/
theorem timeline_keys (P : MotionPanels) : P.report.timeline.keys = P.stepCount + 1 :=
  P.timelineOf_keys _

/-- Every animation element that a panel's plan builds (`MotionPlan.anim`: the turns, slides,
counter-rotations, opacities and morphs of every panel, and the seam) has the timing of the
picture's shared timeline: every element of the picture's SVG is built so (that it is, is how the
writer is written), so all of them run on one clock. -/
theorem panel_anim_eq (P : MotionPanels) {pr : PanelReport} (hp : pr ∈ P.report.panels)
    {tag : String} {head : Array (String × String)} {vals : Array String} {n : Node}
    (h : pr.plan.anim tag head vals = some n) :
    n = el tag (head ++ #[("values", ";".intercalate vals.toList)] ++
      Smil.smilTiming P.report.timeline) := by
  rw [MotionPlan.anim_eq pr.plan h, (P.report_timeline hp).1]

end MotionPanelsReport

namespace MotionPanels

variable (P : MotionPanels)

/-- The messages of the picture's problems (`MotionPanelsReport.checkMessages`). -/
def checkMessages : Array String := P.report.checkMessages

/-- Whether the picture's problems stop it (`MotionPanelsReport.problemsFail`). -/
def problemsFail : Bool := P.report.problemsFail

/-- The picture's animated SVG, or the messages of the errors that stop it
(`MotionPanelsReport.svg?`). -/
def svg? : Except (Array String) String := P.report.svg?

/-- The picture as an `Animation`, or the messages of the errors that stop it
(`MotionPanelsReport.animation?`). -/
def animation? (fps : Nat := 30) : Except (Array String) Animation := P.report.animation? fps

/-- The picture's animated SVG, whatever its problems (`MotionPanelsReport.toSvgUnchecked`). -/
def toSvgUnchecked : String := P.report.toSvgUnchecked

end MotionPanels

end PILean.Plane
