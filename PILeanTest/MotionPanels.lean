/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILeanTest.Motion

/-!
# Tests of motions as panels of one picture

Several motions as panels on one clock (`PILean.Plane.MotionPanels`):

* the shared timeline: two panels with different moves in the same steps (one turning, one
  sliding), a step where only one panel moves, an idle step, a sampled morph in one panel that
  divides the step for the other, sampling the panels disagree on;
* the layout: panels of different sizes (shares given), common against independent scale (a unit
  length has the same number of pixels in every panel at the common scale), the stacked narrow
  rendition;
* ids: two panels with the same actor id give distinct ids in the document;
* the stills: key `k` of the picture is, byte for byte, the panels' key figures composed in their
  frames, and each panel's part of it is that panel's still moved to its place;
* every problem of the picture, and a panel's own problems labelled with the panel;
* every output is inert, keeps the invariant of the SMIL builders, runs on one clock, and its
  written moving picture shows what the composed baker draws;
* the golden picture `examples/motion-panels.svg` and the files `tools/motion-browser-check.py`
  reads (`writeBrowserFiles`).
-/

namespace PILeanTest.MotionPanelsChecks

open PILean PILean.Plane PILean.Anim PILean.Svg
open PILeanTest.MotionChecks (Q elements attrOf has sampleTimes corners testInfo)

/-! ### The golden picture: a point turned about two centres beside the centres turned -/

/-- The point `p` turned about `c` by `q` of a full turn, counterclockwise. -/
def turnPoint (c p : Point) (q : Float) : Point :=
  let θ := 2 * Plane.pi * q
  let d := p - c
  ⟨c.x + d.x * θ.cos - d.y * θ.sin, c.y + d.x * θ.sin + d.y * θ.cos⟩

/-- The centres at the start. -/
def centreA : Point := ⟨-0.4, 0⟩

/-- The second centre at the start. -/
def centreB : Point := ⟨0.4, 0⟩

/-- The radius of the disks. -/
def radius : Float := 1.4

/-- The point at the start. -/
def start : Point := ⟨0.1, 0.5⟩

/-- The point `P` with its label, an actor. -/
def pointP (p : Point) : Item :=
  (group #[Plane.point p |>.accent 0, Plane.label "P" p .aboveRight |>.accent 0]).actor "P"

/-- The positions of the point in the left panel at the five keys: turned a fifth about `A`,
then about `B`, then not at all (an idle step), then about `A` again. -/
def leftPositions : Array Point :=
  let p1 := turnPoint centreA start 0.2
  let p2 := turnPoint centreB p1 0.2
  #[start, p1, p2, p2, turnPoint centreA p2 0.2]

/-- The left panel: the disks fixed (their boundary circles), the point turned by fifths about
the active centre. -/
def leftPanel : Motion where
  keys := leftPositions.map fun p =>
    { items := #[Plane.circle centreA radius |>.faint, Plane.circle centreB radius |>.faint,
        Plane.point centreA, Plane.label "A" centreA .below, Plane.point centreB,
        Plane.label "B" centreB .below, pointP p] }
  steps := #[{ moves := #[("P", .turn centreA (1 / 5))] },
    { moves := #[("P", .turn centreB (1 / 5))] }, MotionStep.idle,
    { moves := #[("P", .turn centreA (1 / 5))] }]

/-- The rigid body of the right panel: the two disks, the edge between the centres and the
centres with their labels, five actors that move together. -/
def body (a b : Point) : Array Item :=
  #[Plane.disk a radius |>.accent 1 |>.actor "DA", Plane.disk b radius |>.accent 2 |>.actor "DB",
    Plane.segment a b |>.actor "E",
    (group #[Plane.point a |>.accent 1, Plane.label "A" a .above]).actor "A",
    (group #[Plane.point b |>.accent 2, Plane.label "B" b .below]).actor "B"]

/-- The ids of the body's actors. -/
def bodyIds : Array String := #["DA", "DB", "E", "A", "B"]

/-- The centres of the right panel at the five keys: the pair turned a fifth backwards about `A`,
then about `B` where it is then, then not at all, then about `A` where it is then. -/
def rightCentres : Array (Point × Point) :=
  let b1 := turnPoint centreA centreB (-0.2)
  let a2 := turnPoint b1 centreA (-0.2)
  #[(centreA, centreB), (centreA, b1), (a2, b1), (a2, b1), (a2, turnPoint a2 b1 (-0.2))]

/-- The right panel: the point fixed, the pair of centres with their disks and edge turned by
fifths about whichever centre is active. -/
def rightPanel : Motion where
  keys := rightCentres.map fun (a, b) =>
    { items := body a b ++ #[Plane.point start |>.accent 0, Plane.label "P" start .below] }
  steps :=
    let all := fun (c : Point) => { moves := bodyIds.map fun id => (id, Move.turn c (-1 / 5)) }
    #[all centreA, all (rightCentres[1]!.2), MotionStep.idle, all (rightCentres[3]!.1)]

/-- The golden picture: the two panels at one scale on one clock. -/
def framesPanels : MotionPanels where
  panels := #[{ title := "The point turns", motion := leftPanel },
    { title := "The centres turn", motion := rightPanel }]
  captions := #["Key 1 of 5: the start.", "Key 2 of 5: a fifth of a turn about A.",
    "Key 3 of 5: a fifth of a turn about B.", "Key 4 of 5: nothing moves.",
    "Key 5 of 5: a fifth of a turn about A."]
  info := { title := "Two frames on one clock",
            description := "Left: the point P turns by fifths about the active centre while the \
              disks stay. Right: the pair of centres with its disks turns by fifths about the \
              active centre while the point stays." }
  narrowWidth := some 360

/-- The golden pictures, by file name. -/
def golden : Array (String × MotionPanels) := #[("motion-panels", framesPanels)]

/-! ### Small pictures for the rules -/

/-- A motion of three steps of a point `X` at `ps` (four keys) with the moves `mvs`, inside the
frame's corners scaled by `size`. -/
def pointMotion (ps : Array Point) (steps : Array MotionStep) (size : Float := 1)
    (id : String := "X") : Motion where
  keys := ps.map fun p =>
    { items := #[Plane.point ⟨-3 * size, -3 * size⟩ |>.faint,
        Plane.point ⟨3 * size, 3 * size⟩ |>.faint, Plane.segment ⟨0, 0⟩ ⟨1, 0⟩ |>.faint,
        (Plane.point p |>.accent 0).actor id] }
  steps

/-- A point turned a quarter about the origin, then again, then idle. -/
def turner (size : Float := 1) (id : String := "X") : Motion :=
  pointMotion #[⟨1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]
    #[{ moves := #[(id, .turn ⟨0, 0⟩ (1 / 4))] }, { moves := #[(id, .turn ⟨0, 0⟩ (1 / 4))] },
      MotionStep.idle] size id

/-- A point slid by one, then nothing in a step where the other panel moves, then idle. -/
def slider (size : Float := 1) (id : String := "X") : Motion :=
  pointMotion #[⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]
    #[{ moves := #[(id, .slide ⟨1, 0⟩)] }, {}, MotionStep.idle] size id

/-- Two panels: one turning, one sliding in the same step, then only the first moves, then an
idle step. -/
def turnSlide (sizeR : Float := 1) : MotionPanels where
  panels := #[{ title := "Turn", motion := turner }, { title := "Slide", motion := slider sizeR }]
  captions := #["One.", "Two.", "Three.", "Four."]
  info := testInfo

/-- Whether some problem of the picture is an error whose message contains `s`. -/
def hasError (P : MotionPanels) (s : String) : Bool :=
  P.problems.any fun p => p.severity == .error && has p.message s

/-- Whether the picture has no error. -/
def noErrors (P : MotionPanels) : Bool := P.problems.all (·.severity == .note)

/-- The values of the attribute `key` of every element of a tree, at most `fuel` deep. -/
def attrValues (key : String) : Nat → Node → Array String
  | 0, _ => #[]
  | _, .text _ => #[]
  | fuel + 1, .element _ attrs cs =>
    ((Smil.attr? attrs key).toArray) ++ cs.flatMap (attrValues key fuel)

/-- Whether the strings are all different. -/
def distinct (xs : Array String) : Bool :=
  (xs.toList.zip (List.range xs.size)).all fun (x, i) => !(xs.toList.drop (i + 1)).contains x

/-- The number of actor layers and of upright groups of all panels of a picture. -/
def markerCounts (r : MotionPanelsReport) : Nat × Nat :=
  (r.panels.foldl (fun a pr => a + pr.plan.markerCounts.1) 0,
    r.panels.foldl (fun a pr => a + pr.plan.markerCounts.2) 0)

/-- Whether, at 50 times through the cycle, the written moving picture (`liveNodes`, read with
`Smil.valueAt`) shows what the composed baker draws (`markersDiff`). -/
def agrees (r : MotionPanelsReport) : Bool :=
  let (actors, ups) := markerCounts r
  let live := r.liveNodes
  (sampleTimes r.timeline.cycle).all fun tr =>
    (markersDiff (r.markersAt (Exact.toFloat tr)) actors ups live (Exact.toFloat tr)).isNone

/-- Whether the outputs of a picture are inert, keep the invariant, run on one clock (the whole
root), are deterministic, and agree with the baker. -/
def outputsOk (r : MotionPanelsReport) : Bool :=
  let svg := r.toSvgUnchecked
  Svg.isInert svg && Smil.invariantProblem? 256 r.svgRootUnchecked == none &&
    Smil.clockProblem? r.svgRootUnchecked == none && svg == r.toSvgUnchecked && agrees r &&
    (List.range r.figure.keyCount).all fun k => Svg.isInert (r.keyStillSvg k)

/-- The page position of the actor `id` (prefixed) at the time `t`, from the composed baker. -/
def actorAt (r : MotionPanelsReport) (id : String) (t : Float) : Option Point :=
  ((r.markersAt t).find? (·.1 == s!"actor {id}")).map (·.2.1)

/-- The time at the fraction `x` of the segment of kind `kind`. -/
def timeIn (r : MotionPanelsReport) (kind : SegKind) (x : Rat) : Float :=
  match r.timeline.segments.find? (·.kind == kind) with
  | some s => Exact.toFloat (s.start + s.dur * x)
  | none => -1

/-- The panel's page length of the unit segment from `(0, 0)` to `(1, 0)` of key 0, as its
still draws it on the page. -/
def unitLength (r : MotionPanelsReport) (i : Nat) : Float :=
  match r.panels[i]? with
  | some pr => (pr.env.frame.toScreen ⟨1, 0⟩).dist (pr.env.frame.toScreen ⟨0, 0⟩)
  | none => 0

/-- `MotionChecks.sampledMotion` with figures between its keys only at the quarters of the step. -/
def quarters : Motion :=
  { MotionChecks.sampledMotion with
    morphSamples := 4
    between := fun j q =>
      if (q * 4).den == 1 then MotionChecks.sampledMotion.between j q else none }

/-- Two motions of two keys as panels `A` and `B`. -/
def pair (a b : Motion) : MotionPanels :=
  { turnSlide with
    panels := #[{ title := "A", motion := a }, { title := "B", motion := b }]
    captions := #["Start.", "End."] }

/-- `turnSlide` with the title `t` on its first panel and a share six times as wide for the
second. -/
def titled (t : String) : MotionPanels :=
  { turnSlide with
    panels := turnSlide.panels.modify 0 ({ · with title := t })
    shares := #[1, 6] }

/-- The checks of the shared timeline. -/
def timelineChecks : Array (String × Bool) := Id.run do
  let mut out : Array (String × Bool) := #[]
  let P := turnSlide
  let r := P.report
  out := out.push ("panels: a turn beside a slide, one panel alone, an idle step: no problems",
    decide P.WellFormed && P.problems.isEmpty)
  out := out.push ("panels: a step's duration is the longest of the panels', idle only when \
      every panel is idle",
    let s := P.animSteps
    s.size == 3 && s[0]!.dur == 1 && s[0]!.kind == .move && s[1]!.dur == 1 &&
      s[1]!.kind == .move && s[2]!.kind == .idle && s[2]!.dur == P.pacing.idle)
  out := out.push ("panels: the shared timeline has the picture's keys; every panel's plan uses it",
    r.timeline.keys == 4 && r.panels.all fun pr =>
      pr.plan.timeline.cycle == r.timeline.cycle &&
        pr.plan.timeline.segments.size == r.timeline.segments.size)
  -- the turn and the slide arrive at the same moment
  let mid := timeIn r (.move 0) (1 / 2)
  let t1 := Exact.toFloat (r.timeline.restTime 1)
  let quarter := timeIn r (.move 1) (1 / 2)
  out := out.push ("panels: the turn and the slide run in the same segment, on one clock",
    match actorAt r "p1-X" mid, actorAt r "p2-X" mid, actorAt r "p2-X" t1 with
    | some a, some b, some b1 =>
      let pr0 := r.panels[0]!
      let pr1 := r.panels[1]!
      let c := pr0.env.frame.toScreen ⟨0, 0⟩
      -- half way through the eased step: the turn half done (45°), the slide half done
      (a.dist c - pr0.env.frame.scale).abs < 1e-4 &&
        ((Float.atan2 (c.y - a.y) (a.x - c.x)) * 180 / Plane.pi - 45).abs < 1e-3 &&
        (b.x - (pr1.env.frame.toScreen ⟨0.5, 1⟩).x).abs < 1e-3 &&
        (b1.dist (pr1.env.frame.toScreen ⟨1, 1⟩)) < 1e-3
    | _, _, _ => false)
  out := out.push ("panels: in a step where only one panel moves, the other stays",
    match actorAt r "p2-X" t1, actorAt r "p2-X" quarter, actorAt r "p1-X" quarter,
        actorAt r "p1-X" t1 with
    | some a, some b, some c, some d => a.dist b < 1e-9 && c.dist d > 10
    | _, _, _, _ => false)
  -- a sampled morph in one panel divides the step for the other
  let sampled : MotionPanels :=
    { turnSlide with panels := #[{ title := "Morph", motion := MotionChecks.sampledMotion },
        { title := "Turn", motion := pointMotion #[⟨1, 0⟩, ⟨0, 1⟩] #[{ moves := #[("X",
          .turn ⟨0, 0⟩ (1 / 4))] }] }], captions := #["Start.", "End."] }
  let rs := sampled.report
  out := out.push ("panels: a morph sampled in one panel divides the step for every panel",
    sampled.problems.isEmpty && rs.samples == #[4] &&
      rs.timeline.segments.size == sampled.baseTimeline.segments.size + 3 &&
      rs.panels.all (·.plan.timeline.segments.size == rs.timeline.segments.size) && agrees rs)
  let morph := fun (n : Nat) =>
    { MotionChecks.sampledMotion with morphSamples := n }
  out := out.push ("panels: panels sampling one step in 4 and 6 intervals share 12 when their \
      figures between the keys answer there",
    let both := pair (morph 4) (morph 6)
    both.problems.isEmpty && both.report.samples == #[12] &&
      both.report.timeline.segments.size == both.baseTimeline.segments.size + 11 &&
      agrees both.report)
  let clash := pair quarters (morph 6)
  out := out.push ("panels: sampling that cannot be shared is an error that says what is drawn",
    hasError clash "sample a morph in different numbers of intervals (4, 6)" &&
      hasError clash "the step is drawn unsampled" && clash.report.samples == #[1] &&
      (match clash.svg? with | .error _ => true | .ok _ => false))
  out := out.push ("panels: under warn, unshared sampling is a note saying what is drawn, and the \
      picture is written",
    let w : MotionPanels := { clash with checks := .warn }
    w.problems.any (fun p => p.severity == .note && has p.message "drawn unsampled") &&
      (match w.svg? with | .ok _ => true | .error _ => false) && outputsOk w.report)
  out := out.push ("panels: the same numbers of intervals are one sampling",
    let same := pair (morph 4) (morph 4)
    same.problems.isEmpty && same.report.samples == #[4])
  return out

/-- The checks of the layout. -/
def layoutChecks : Array (String × Bool) := Id.run do
  let mut out : Array (String × Bool) := #[]
  -- common scale: a unit length is as long in both panels, the larger panel wider
  let big := turnSlide 2
  let r := big.report
  out := out.push ("panels: at the common scale a unit segment has the same length in every \
      panel",
    big.problems.isEmpty && (unitLength r 0 - unitLength r 1).abs < 1e-9 &&
      ((r.panels[0]!.keys.figure 0).frame.scale - (r.panels[1]!.keys.figure 0).frame.scale).abs <
        1e-9)
  out := out.push ("panels: the larger content gets the larger share of the width",
    let ps := r.layout.places
    ps.size == 2 && ps[1]!.frame.width > 1.5 * ps[0]!.frame.width &&
      (ps[0]!.frame.width + ps[1]!.frame.width + big.gap - big.width).abs < 1e-6 &&
      (ps[1]!.x - (ps[0]!.frame.width + big.gap)).abs < 1e-9)
  let indep : MotionPanels := { big with scale := .independent }
  let ri := indep.report
  out := out.push ("panels: at independent scales each panel is fitted on its own",
    indep.problems.isEmpty && (unitLength ri 0 / unitLength ri 1 - 1).abs > 0.2)
  -- shares given: a larger right panel
  let shared : MotionPanels := { turnSlide with shares := #[1, 2], scale := .independent }
  let rsh := shared.report
  out := out.push ("panels: shares given set the widths (a right panel twice as wide)",
    shared.problems.isEmpty &&
      let ps := rsh.layout.places
      (ps[1]!.frame.width - (2 : Float) * ps[0]!.frame.width).abs < 1e-9)
  out := out.push ("panels: side by side, the panels are as tall as the tallest, under the titles",
    r.layout.places.all (fun p => p.frame.height == r.layout.places[0]!.frame.height &&
      p.y == r.layout.band) && r.layout.band > 0 &&
      r.layout.height == r.layout.band + r.layout.places[0]!.frame.height)
  -- the narrow rendition: stacked, at the narrow width, at one scale
  let narrow := ({ big with narrowWidth := some 300 } : MotionPanels).narrow
  out := out.push ("panels: the narrow rendition stacks the panels at the narrow width, at one \
      scale",
    match narrow with
    | some n =>
      let rn := n.report
      let ps := rn.layout.places
      n.problems.isEmpty && rn.layout.width == 300 && ps.all (·.x == 0) &&
        ps.all (·.frame.width == 300) && ps[1]!.y > ps[0]!.y + ps[0]!.frame.height &&
        (unitLength rn 0 - unitLength rn 1).abs < 1e-9 && outputsOk rn
    | none => false)
  out := out.push ("panels: a picture without a narrow width has no narrow rendition",
    turnSlide.narrow.isNone)
  return out

/-- The checks of ids and stills. -/
def idChecks : Array (String × Bool) := Id.run do
  let mut out : Array (String × Bool) := #[]
  -- both panels use the actor id `P`
  let twin : MotionPanels :=
    { turnSlide with panels := #[{ title := "One", motion := turner (id := "P") },
        { title := "Two", motion := slider (id := "P") }] }
  let r := twin.report
  let root := r.svgRootUnchecked
  out := out.push ("panels: two panels with the same actor id give distinct ids in the document",
    twin.problems.isEmpty && distinct (attrValues "id" 256 root) &&
      (attrValues "id" 256 root).size ≥ 4 &&
      (attrValues "data-pilean-actor" 256 root).toList.eraseDups == ["p1-P", "p2-P"] &&
      (attrValues "data-pilean-panel" 256 root) == #["p1", "p2"])
  out := out.push ("panels: the stills have distinct ids too",
    (List.range 4).all fun k => (r.stillNodes k).all fun _ =>
      distinct ((r.stillNodes k).flatMap (attrValues "id" 256)))
  -- the stills are the panels' key figures composed in their frames
  let P := framesPanels
  let rp := P.report
  let composed := fun (k : Nat) =>
    let nodes := (Array.range P.panels.size).flatMap fun i =>
      match rp.panelKeyFigure? i k with
      | some fig =>
        let place := rp.layout.places[i]!
        let f := fig.env.frame
        let env : Env :=
          { fig.env with frame := { f with ox := f.ox + place.x, oy := f.oy + place.y } }
        ((Canvas.Shape.group (fig.items.flatMap (drawItem env))).render fig.svgMode).map
          (prefixNodeIds (panelPrefix i) 256)
      | none => #[]
    Svg.document rp.layout.width.round rp.layout.height.round
      (rp.background.render rp.mode ++ rp.titleNodes ++ nodes)
  out := out.push ("panels: each key of the picture is the panels' key figures composed, byte \
      for byte",
    (List.range 5).all fun k => rp.keyStillSvg k == composed k)
  -- each panel's part of the still is its own still moved to its place
  out := out.push ("panels: each panel's part of a key is that panel's still moved to its place",
    (List.range 5).all fun k => (List.range 2).all fun i =>
      match rp.panelKeyFigure? i k, rp.stillShape k with
      | some fig, .group cs .. =>
        let place := rp.layout.places[i]!
        let own := drawnOf 256 (Affine.translate place.x place.y) 1
          (.group (fig.items.flatMap (drawItem fig.env)))
        -- the still is the background, the titles, then the panels
        let part := drawnOf 256 Affine.id 1 (cs.getD (cs.size - 2 + i) (.group #[]))
        own.size == part.size && own.size > 0 &&
          (drawingDiff part own).isNone &&
          (own.zip part).all fun
            | (.text a p _, .text b q _) => a == b && p.dist q < 1e-9
            | (.path a xs, .path b ys) => a == b && linesApart xs ys 1e-9 == 0
            | _ => false
      | _, _ => false)
  out := out.push ("panels: the panel key figures are the keys of each panel as laid out",
    (List.range 5).all fun k =>
      (rp.panelKeyFigure? 0 k).map (·.toSvg) == some (rp.panels[0]!.motion.keyFigure k).toSvg)
  out := out.push ("panels: the poster still has the poster's prefix on every id",
    (attrValues "id" 256 rp.svgRootUnchecked).all fun id =>
      id.startsWith "p1-" || id.startsWith "p2-" || id.startsWith "poster-p1-" ||
        id.startsWith "poster-p2-")
  return out

/-- The checks of the problems of a picture. -/
def problemChecks : Array (String × Bool) := Id.run do
  let mut out : Array (String × Bool) := #[]
  let P := turnSlide
  let withPanel := fun (i : Nat) (f : Motion → Motion) =>
    ({ P with panels := P.panels.modify i fun p => { p with motion := f p.motion } } :
      MotionPanels)
  out := out.push ("panels: unequal numbers of keys are an error",
    let short := withPanel 1 fun m => { m with keys := m.keys.pop, steps := m.steps.pop }
    !decide short.WellFormed && hasError short "has 3 keys where panel Turn has 4" &&
      (match short.svg? with | .error _ => true | .ok _ => false))
  out := out.push ("panels: captions that are not one per key are an error",
    hasError { P with captions := #["one"] } "1 captions for 4 keys")
  out := out.push ("panels: two panels with one title are an error",
    hasError { P with panels := P.panels.modify 1 ({ · with title := "Turn" }) }
      "two panels have the title Turn")
  out := out.push ("panels: a panel's own step timing is an error",
    hasError (withPanel 0 fun m =>
        { m with steps := m.steps.modify 0 ({ · with duration := some 2 }) })
      "panel Turn: step 1 sets its own duration or easing")
  out := out.push ("panels: the picture's timing for a step is used, and must be one per step",
    let timed : MotionPanels := { P with timing := #[{ duration := some 3 }, {}, {}] }
    timed.problems.isEmpty && timed.animSteps[0]!.dur == 3 &&
      hasError { P with timing := #[{}] } "the timing of 1 steps; it has 3")
  out := out.push ("panels: a line in a panel is an error",
    hasError (withPanel 1 fun m => { m with keys := m.keys.map fun f =>
        { f with items := f.items.push (Plane.line ⟨0, 0⟩ ⟨1, 1⟩ |>.faint) } })
      "panel Slide: key 0 has a line or a ray")
  out := out.push ("panels: a panel whose content does not fit its share is an error",
    let wide := withPanel 0 fun m => { m with keys := m.keys.map fun f =>
      { f with items := f.items.push (Plane.label "a label far too wide for its share" ⟨0, 0⟩) } }
    hasError { wide with shares := #[1, 40] } "panel Turn: its content does not fit its share")
  out := out.push ("panels: a panel's own problem is reported with its panel",
    let wrong := withPanel 1 fun m => { m with steps := m.steps.modify 0 fun _ =>
      { moves := #[("X", .slide ⟨2, 0⟩)] } }
    hasError wrong "panel Slide: step 1 (key 0 to key 1): the slide of X does not carry" &&
      (match wrong.svg? with | .error _ => true | .ok _ => false))
  out := out.push ("panels: a panel's layout problem on a key is reported with its panel",
    let crowded := withPanel 0 fun m => { m with keys := m.keys.map fun f =>
      { f with items := f.items ++
        #[Plane.label "Y" ⟨0, 0⟩ .center, Plane.label "Z" ⟨0, 0⟩ .center] } }
    crowded.problems.any fun p => p.severity == .error && has p.message "panel Turn: key 0:")
  out := out.push ("panels: shares that are not one per panel are an error",
    hasError { P with shares := #[1, 2, 3] } "3 shares for 2 panels" &&
      hasError { P with shares := #[1, -2] } "not a positive number")
  out := out.push ("panels: a picture without a title or description is an error under fail, a \
      note under warn",
    hasError { P with info := {} } "the picture has no title" &&
      hasError { P with info := { title := "t" }, captions := #["", "", "", ""] }
        "neither a description nor captions" &&
      noErrors { P with info := {}, checks := .warn })
  out := out.push ("panels: a poster that is not a key is an error",
    hasError { P with poster := 4 } "the poster is key 4")
  out := out.push ("panels: panels on different backgrounds are an error",
    hasError (withPanel 1 fun m => { m with keys := m.keys.map fun f =>
        { f with style := { f.style with background := ⟨0, 0, 0, 255⟩ } } })
      "panel Slide is drawn on another background")
  out := out.push ("panels: a picture without panels is an error",
    hasError { P with panels := #[] } "no panels")
  out := out.push ("panels: fail is the default; the checked SVG is the unchecked one when \
      nothing is wrong",
    P.checks == .fail && (match P.svg? with | .ok s => s == P.toSvgUnchecked | .error _ => false) &&
      (match P.animation? with | .ok a => a.problems () == #[] | .error _ => false))
  return out

/-- The checks of the outputs of the pictures. -/
def outputChecks : Array (String × Bool) := Id.run do
  let mut out : Array (String × Bool) := #[]
  for (name, P) in golden ++ #[("turn and slide", turnSlide), ("sizes", turnSlide 2),
      ("independent", { turnSlide 2 with scale := .independent })] do
    let r := P.report
    out := out.push (s!"panels {name}: no problems", P.problems.isEmpty)
    out := out.push (s!"panels {name}: the SVG is inert, keeps the invariant, runs on one clock \
        and shows what the composed baker draws", outputsOk r)
    out := out.push (s!"panels {name}: at every rest the composed baker draws the composed still",
      r.restProblems.isEmpty && r.writerProblems.isEmpty)
    out := out.push (s!"panels {name}: every animation element of the document has one timing",
      let anims := (elements "animateTransform" 256 r.svgRootUnchecked) ++
        (elements "animate" 256 r.svgRootUnchecked)
      anims.size > 0 && anims.all fun a =>
        attrOf a "dur" == Smil.durText r.timeline.cycle &&
          attrOf a "keyTimes" == attrOf (anims[0]!) "keyTimes")
    let a := r.toAnimationUnchecked
    out := out.push (s!"panels {name}: the baked animation is one cycle of the picture's size",
      (a.duration - Exact.toFloat r.timeline.cycle).abs < 1e-12 && (a.width, a.height) ==
        r.pixelSize && a.posterTime == some (Exact.toFloat (r.timeline.restTime 0)))
    match P.narrow with
    | some n =>
      out := out.push (s!"panels {name}: the narrow rendition passes its checks too",
        n.problems.isEmpty && outputsOk n.report)
    | none => pure ()
  out := out.push ("panels: the golden picture's right panel has one chain for its rigid body",
    let pr := framesPanels.report.panels[1]!
    pr.plan.runs.flatten.any fun sub => sub.size == 5)
  out := out.push ("panels: the golden picture's left and right actors are in phase at every \
      rest",
    let r := framesPanels.report
    (List.range 5).all fun k =>
      let t := Exact.toFloat (r.timeline.restTime k)
      let pl := r.panels[0]!
      let pr := r.panels[1]!
      (actorAt r "p1-P" t).any (·.dist (pl.env.frame.toScreen leftPositions[k]!) < 1e-3) &&
        (actorAt r "p2-A" t).any (·.dist (pr.env.frame.toScreen rightCentres[k]!.1) < 1e-3) &&
        (actorAt r "p2-B" t).any (·.dist (pr.env.frame.toScreen rightCentres[k]!.2) < 1e-3))
  return out


/-! ### What a turn sweeps, the layout's inputs, ids -/

/-- A point turned half a turn about the far centre `(0, 2)`, from `(0, 0)` to `(0, 4)`: half way
it is at `(2, 2)`, outside the box of its keys; with `view`, its keys show only that box. -/
def farTurn (view : Option Box := none) : Motion where
  keys := #[⟨0, 0⟩, ⟨0, 4⟩, ⟨0, 4⟩].map fun p =>
    { items := #[Plane.point ⟨-1, 0⟩ |>.faint, Plane.point ⟨1, 4⟩ |>.faint,
        (Plane.point p |>.accent 0).actor "X"], view }
  captions := #["a", "b", "c"]
  steps := #[{ moves := #[("X", .turn ⟨0, 2⟩ (1 / 2))] }, MotionStep.idle]
  info := testInfo

/-- A neighbour for `farTurn`: a point slid by one. -/
def neighbour : Motion where
  keys := #[⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩].map fun p =>
    { items := #[Plane.point ⟨-1, -1⟩ |>.faint, Plane.point ⟨2, 5⟩ |>.faint,
      (Plane.point p |>.accent 1).actor "Y"] }
  steps := #[{ moves := #[("Y", .slide ⟨1, 0⟩)] }, MotionStep.idle]

/-- `farTurn` beside `neighbour`. -/
def farPanels (view : Option Box := none) : MotionPanels where
  panels := #[{ title := "Far turn", motion := farTurn view },
    { title := "Neighbour", motion := neighbour }]
  captions := #["a", "b", "c"]
  info := testInfo

/-- `turnSlide` under `warn` with a slide in its second panel that misses its key. -/
def missedSlide : MotionPanels :=
  { turnSlide with
    checks := .warn
    panels := turnSlide.panels.modify 1 fun p =>
      { p with motion := { p.motion with steps := p.motion.steps.modify 0 fun _ =>
        { moves := #[("X", .slide ⟨2, 0⟩)] } } } }

/-- The checks of what turns sweep, of the layout's inputs and of the ids. -/
def sweepChecks : Array (String × Bool) := Id.run do
  let mut out : Array (String × Bool) := #[]
  let box : Box := ⟨-1, 0, 1, 4⟩
  out := out.push ("motion: the view includes what a turn sweeps; nothing leaves the picture",
    let f := (farTurn).keysOf.env.frame
    (farTurn).problems.isEmpty && (f.toScreen ⟨2, 2⟩).x < f.width - 3)
  out := out.push ("motion: a turn that leaves a view the keys set is an error",
    (farTurn (some box)).problems.any fun p =>
      p.severity == .error && has p.message "X leaves the picture during step 1")
  out := out.push ("panels: a panel's extent includes what its turns sweep",
    let r := (farPanels).report
    let pr := r.panels[0]!
    (farPanels).problems.isEmpty && (pr.env.frame.toScreen ⟨2, 2⟩).x <
      r.layout.places[0]!.x + r.layout.places[0]!.frame.width - 3)
  out := out.push ("panels: a turn that leaves a panel with a view of its own is an error",
    hasError (farPanels (some box)) "panel Far turn: X leaves its panel during step 1")
  out := out.push ("panels: a gap below zero is an error",
    hasError { turnSlide with gap := -10 } "the gap between the panels (-10 px)")
  -- titles on a narrow share: made smaller to fit, or refused
  out := out.push ("panels: a title wider than its panel is made smaller to fit it",
    let P := titled "Turning the point"
    let r := P.report
    let pl := r.layout.places[0]!
    let st := r.style
    let w := st.text.measure "Turning the point" pl.titleSize
    P.problems.isEmpty && pl.titleSize < st.panelTitleSize && pl.titleFits &&
      pl.titleAt.x - w / 2 ≥ pl.x && pl.titleAt.x + w / 2 ≤ pl.x + pl.frame.width)
  out := out.push ("panels: a title too wide even at the smallest size is an error",
    hasError (titled "A rather long title for the first of the two panels")
      "panel A rather long title for the first of the two panels: its title is wider")
  -- every id of the document is distinct, checked at run time
  out := out.push ("panels: an id twice in the document is an error",
    let r := turnSlide.report
    let bad : MotionPanelsReport :=
      { r with panels := r.panels.modify 1 ({ · with idPrefix := "p1-" }) }
    r.idProblems.isEmpty && bad.idProblems.any fun p => has p.message "has the id p1-X twice")
  -- a picture written under warn despite errors says it was not checked as a whole
  out := out.push ("panels: under warn, a picture with errors says it was not composed-checked",
    let wrong := missedSlide
    wrong.problems.any (fun p => p.severity == .note && has p.message "was not checked") &&
      (match wrong.svg? with | .ok _ => true | .error _ => false) &&
      !turnSlide.problems.any fun p => has p.message "was not checked")
  -- several pictures in one page: a prefix of their own
  out := out.push ("motion: two motions with the same actor ids and prefixes of their own have \
      distinct ids",
    let a : Motion := { MotionChecks.turnMotion with idPrefix := "a-" }
    let b : Motion := { MotionChecks.turnMotion with idPrefix := "b-" }
    let ids := attrValues "id" 256 a.svgRootUnchecked ++ attrValues "id" 256 b.svgRootUnchecked
    a.problems.isEmpty && ids.size ≥ 4 && distinct ids &&
      (attrValues "data-pilean-actor" 256 a.svgRootUnchecked).all (·.startsWith "a-") &&
      Svg.isInert a.toSvgUnchecked)
  out := out.push ("panels: two pictures with the same actor ids and prefixes of their own have \
      distinct ids, stills included",
    let a : MotionPanels := { turnSlide with idPrefix := "a-" }
    let b : MotionPanels := { turnSlide with idPrefix := "b-" }
    let idsOf := fun (P : MotionPanels) =>
      attrValues "id" 256 P.report.svgRootUnchecked ++
        (P.report.stillNodes 0).flatMap (attrValues "id" 256)
    a.problems.isEmpty && distinct (attrValues "id" 256 a.report.svgRootUnchecked) &&
      (idsOf a).all (fun x => !(idsOf b).contains x) && (idsOf a).size ≥ 4 &&
      (attrValues "data-pilean-actor" 256 a.report.svgRootUnchecked).toList.eraseDups ==
        ["a-p1-X", "a-p2-X"] && outputsOk a.report)
  out := out.push ("panels: the table of steps lists each step's kind, duration and every move",
    let rows := framesPanels.report.stepRows
    rows.size == 4 && rows[2]!.kind == .idle && rows[0]!.moves.size == 6 &&
      rows[0]!.duration == 1 && (rows[0]!.moves.filter (·.1 == 1)).size == 5)
  return out

/-- All checks. -/
def checks : Array (String × Bool) :=
  timelineChecks ++ layoutChecks ++ idChecks ++ problemChecks ++ outputChecks ++ sweepChecks

/-! ### Files for the browser check -/

open PILeanTest.MotionChecks (num pt)

/-- What `tools/motion-browser-check.py` expects of a picture of panels, as JSON, in the shape of
`MotionChecks.expectations` (ids with their panel's prefix, points on the picture's page): the
cycle; at the middle of each key's rest every actor's anchor in the composed still and every
upright group's anchor where the plan draws it; every turn with its centre, start, angle and
three samples; and also each panel's box on the page, and the marked points of every actor of
every panel at every rest and at a quarter, a half and three quarters of every move (`phase`), to
show that the panels are in phase. -/
def expectations (name : String) (r : MotionPanelsReport) : String :=
  let st := r.style
  let anchorOf := fun (pr : PanelReport) (fig : Figure) (id : String) =>
    (fig.actor? id).bind fun it => (it.leaves[0]?).bind fun lf =>
      (anchors pr.env.frame st lf.geom)[0]?
  let rests := (List.range r.figure.keyCount).map fun k =>
    let actors := r.panels.toList.flatMap fun pr =>
      let fig := pr.keys.figure k
      let still := pr.plan.layers.filter (·.geoms.isNone)
      let ids := (still.filterMap (·.version.actor)).toList.eraseDups.filter fig.hasActor
      ids.filterMap fun id => (anchorOf pr fig id).map fun a =>
        s!"\{\"id\": \"{pr.idPrefix}{Canvas.safeToken id}\", \"at\": {pt a}}"
    let t := Exact.toFloat (r.timeline.restTime k)
    let ups := ((r.markersAt t).filter (·.1 == "upright")).toList.map fun (_, q, _) => pt q
    s!"\{\"key\": {k}, \"t\": {num t}, \"actors\": [{", ".intercalate actors}], \
      \"uprights\": [{", ".intercalate ups}]}"
  let segs := r.timeline.segments
  let turns := r.panels.toList.flatMap fun pr =>
    let still := pr.plan.layers.filter (·.geoms.isNone)
    still.toList.flatMap fun L => match L.version.actor with
      | none => []
      | some id => L.links.toList.filterMap fun
        | .turn j c deg => do
          let i ← (List.range segs.size).find? fun i => (segs[i]?.map (·.kind)) == some (.move j)
          let s ← segs[i]?
          let start ← anchorOf pr (pr.keys.figure j) id
          let samples := [0.25, 0.5, 0.75].map fun (x : Float) =>
            let t := Exact.toFloat s.start + x * Exact.toFloat s.dur
            s!"\{\"t\": {num t}, \"f\": {num ((pr.plan.clock.splines.getD i .linear).eval x)}}"
          return s!"\{\"id\": \"{pr.idPrefix}{Canvas.safeToken id}\", \"step\": {j}, \
            \"centre\": {pt c}, \"start\": {pt start}, \"sweep\": {num deg}, \
            \"samples\": [{", ".intercalate samples}]}"
        | .slide .. => none
  let ups := (markerCounts r).2
  let panels := (r.panels.zip r.layout.places).toList.map fun (pr, place) =>
    s!"\{\"id\": \"{pr.idPrefix.dropEnd 1}\", \"box\": [{num place.x}, {num place.y}, \
      {num place.frame.width}, {num place.frame.height}]}"
  let restTimes := (List.range r.figure.keyCount).map fun k =>
    Exact.toFloat (r.timeline.restTime k)
  let times := restTimes ++
    (segs.toList.filter fun s => match s.kind with | .move _ => true | _ => false).flatMap
      fun s => [0.25, 0.5, 0.75].map fun (x : Float) =>
        Exact.toFloat s.start + x * Exact.toFloat s.dur
  let phase := times.map fun t =>
    let actors := ((r.markersAt t).filter (·.1.startsWith "actor ")).toList.map fun (n, q, _) =>
      s!"[\"{(n.drop 6).toString}\", {pt q}]"
    s!"\{\"t\": {num t}, \"actors\": [{", ".intercalate actors}]}"
  let marks := r.figure.panels.any fun p => MotionChecks.turningMarks p.motion
  s!"\{\"name\": \"{name}\", \"svg\": \"{name}.svg\", \"poster_png\": \"{name}-poster.png\", \
    \"cycle\": {num (Exact.toFloat r.timeline.cycle)}, \"uprights\": {ups}, \
    \"turning_marks\": {marks}, \"band\": {num r.layout.band}, \
    \"rests\": [{", ".intercalate rests}], \"turns\": [{", ".intercalate turns}], \
    \"panels\": [{", ".intercalate panels}], \"phase\": [{", ".intercalate phase}]}\n"

/-- Writes the golden pictures and their narrow renditions, and `farPanels`, into `dir` for
`tools/motion-browser-check.py`: each picture's SVG, the SVG of each key of the picture, the
poster key's PNG and the expectations (`expectations`). -/
def writeBrowserFiles (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  -- the golden pictures, and a picture whose turn sweeps far outside its keys (no labels)
  for (name, P) in golden.push ("motion-panels-far", farPanels) do
    let all := #[(name, P)] ++ (P.narrow.map fun n => #[(name ++ "-narrow", n)]).getD #[]
    for (file, Q) in all do
      let r := Q.report
      IO.FS.writeFile (dir / s!"{file}.svg") r.toSvgUnchecked
      for k in [0:Q.keyCount] do
        IO.FS.writeFile (dir / s!"{file}-key{k}.svg") (r.keyStillSvg k)
      IO.FS.writeBinFile (dir / s!"{file}-poster.png") ((r.keyStillPng Q.poster).getD .empty)
      IO.FS.writeFile (dir / s!"{file}.json") (expectations file r)
      IO.println s!"{dir / file}: .svg, -key*.svg, -poster.png, .json"

end PILeanTest.MotionPanelsChecks
