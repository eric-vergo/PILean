/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plane.MotionPlan

/-!
# Motions of plane figures: outputs and the check against the stills

The outputs of a `Motion` laid out as a `MotionPlan` (`PILean.Plane.MotionPlan`), and its checks.
The checked route is `Motion.report` (the keys, the plan and the problems, computed once) and its
`svg?` and `animation?`, which give the messages of the errors instead of a motion whose problems
stop it (`CheckLevel.fail`, the default). The routes that write whatever the problems say end in
`Unchecked` (`Motion.svgRootUnchecked`, `toSvgUnchecked`, `figureAtUnchecked`,
`toAnimationUnchecked`), for tests and tools.

**The stills pin the animation.** `Motion.restProblems` compares, at the middle of every key's rest
(of its last part, after its fades), the whole baked drawing (every path and every text, in order:
`Drawn`, `drawnOf`) with the key's still, within `restTolerance` (0.05 px, plus `5.5e-4 r` for a
path of half-width `r`, for the cubic approximations of turned circles, `drawingDiff`). **The writer
against the baker.** `Motion.writerProblems` reads the written moving picture with `Smil.valueAt` at
the middle of every segment of the timeline and requires what the baker draws (`writerDiff`).
**Nothing leaves the picture.** `boundsProblems` draws every layer at eight times through every move
and requires every point of it in the page (0.5 px). `Motion.problems` is the problems of the keys
and steps (`Motion.keyProblems`) with these. A motion's own prefix (`Motion.idPrefix`) goes on every
id of its SVG, for several pictures in one page.

## Main definitions

* `MotionReport`, `Motion.report`, `Motion.svg?`, `Motion.animation?`, `Motion.problems`,
  `Motion.checkMessages`, `Motion.problemsFail`.
* `Motion.svgRootUnchecked`, `Motion.toSvgUnchecked`, `Motion.figureAtUnchecked`,
  `Motion.toAnimationUnchecked`.
* `Drawn`, `drawnOf`, `drawingDiff`, `restTolerance`, `Motion.restProblems`, `inexactProblems`.
* `writtenMarkers`, `markersDiff`, `writerDiff`, `Motion.writerProblems`.
* `shapePoints`, `boundsTolerance`, `boundsProblems`.

## Main results

* `MotionReport.wellFormed_of_svg`, `Motion.report_unsound`, `Motion.timeline_eq_of_svg`: a
  motion that gives an SVG is well formed, has no segment divided unsoundly, and is written on its
  base timeline divided into exactly its writer's parts.
-/

namespace PILean.Plane

open Canvas Anim Svg

/-! ### The motion's outputs, unchecked -/

namespace Motion

variable (m : Motion)

/-- The captions of the stills (`Motion.stillKeys`), in order. -/
def stillCaptions : Array String := m.stillKeys.map (m.captions.getD · "")

/-- The text alternative of the motion: its description and the captions of its stills. -/
def description : String :=
  " ".intercalate ((if m.info.description.isEmpty then [] else [m.info.description]) ++
    m.stillCaptions.toList)

/-- The root element of the motion's animated SVG from its keys as drawn `K` and its plan `p`,
whatever its problems: the background; the moving picture (`MotionPlan.toNodesUnchecked`) in a
group of class `pilean-motion-live`; and the poster key's still in a group of class
`pilean-motion-poster`, which a style rule shows instead under reduced motion
(`Animation.reducedMotionStyle`). The root has `role="img"`, the motion's title and a
description with the captions. -/
def svgRootIn (K : MotionKeys) (p : MotionPlan) : Node :=
  let f := p.env.frame
  let w := f.width.round
  let h := f.height.round
  let outer := fun (ns : Array Node) =>
    if m.idPrefix.isEmpty then ns else ns.map (prefixNodeIds m.idPrefix 256)
  let poster := outer ((K.figure m.poster).svgNodes.map (prefixIds "poster-" 256))
  let head := (if m.info.title.isEmpty then #[] else #[el "title" #[] #[.text m.info.title]]) ++
    (if m.description.isEmpty then #[] else #[el "desc" #[] #[.text m.description]])
  el "svg" #[("xmlns", "http://www.w3.org/2000/svg"), ("width", fmtNum w),
    ("height", fmtNum h), ("viewBox", s!"0 0 {fmtNum w} {fmtNum h}"), ("role", "img")]
    (head ++ #[Animation.reducedMotionStyle] ++ p.background.render p.mode ++
      #[el "g" #[("class", Animation.liveClass)] (outer p.toNodesUnchecked),
        el "g" #[("class", Animation.posterClass)] poster])

/-- The root element of the motion's animated SVG (`svgRootIn`), whatever its problems: for tests
and tools. `Motion.svg?` is the checked route. -/
def svgRootUnchecked : Node := let K := m.keysOf; m.svgRootIn K (m.planIn K K.env)

/-- The motion as an animated SVG document, whatever its problems: for tests and tools.
`Motion.svg?` is the checked route. -/
def toSvgUnchecked : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++ Svg.render 0 m.svgRootUnchecked ++ "\n"

/-- The motion at the time `t` (seconds) as a drawing (`MotionPlan.figureAtUnchecked`), whatever
its problems. `Motion.animation?` is the checked route to the baked drawings. -/
def figureAtUnchecked (t : Float) : Shape := m.plan.figureAtUnchecked t

end Motion

/-! ### The baker against the stills -/

/-- A drawn element as the rest check compares it: a path's paint (fill, stroke, the stroke's
width under its transform, its opacity) with its page polylines, or a text with its page anchor
point and the angle its transform turns it by. -/
inductive Drawn where
  /-- A path: its paint as text and its polylines on the page. -/
  | path (paint : String) (lines : Array Polyline)
  /-- A text: its string, size, colour, anchor, weight and opacity as text, its page point and the
  angle (radians) of its transform. -/
  | text (key : String) (at_ : Point) (turn : Float)
  deriving Inhabited

/-- The paint of a path as text, at the scale `k` and opacity `o`. -/
def paintText (fill : Option Fill) (line : Option Line) (k o : Float) : String :=
  let f := match fill with
    | some (.solid c) => s!"{c.rgbHex}/{c.a}"
    | some (.paint _) => "gradient"
    | none => "none"
  let l := match line with
    | some l =>
      s!"{l.ink.rgbHex}/{l.ink.a} {fmtNum (l.width * k) 3} {l.cap} {l.join} \
        {l.dash.map fun d => fmtNum (d * k) 3}"
    | none => "none"
  s!"{f} | {l} | {fmtNum o 4}"

/-- The elements a drawing shows, in order, under the transform `M` and the opacity `o`, at most
`fuel` deep; what is drawn at an opacity of zero is left out. Curves are flattened to `0.01` px. -/
def drawnOf : Nat → Affine → Float → Shape → Array Drawn
  | 0, _, _, _ => #[]
  | _, M, o, .path q fill line op =>
    if o * op < 1e-6 then #[]
    else #[.path (paintText fill line M.maxScale (o * op)) ((q.transform M).flatten 0.01)]
  | _, M, o, .text str at_ size ink anchor w rot =>
    if o < 1e-6 then #[]
    else #[.text s!"{str} {fmtNum (size * M.maxScale) 3} {ink.rgbHex}/{ink.a} {reprStr anchor} \
      {fmtNum w 3} {fmtNum o 4}" (M.apply at_) (rot + Float.atan2 M.b M.a)]
  | fuel + 1, M, o, .group cs t op _ => cs.flatMap (drawnOf fuel (M.comp t) (o * op))
  | fuel + 1, M, o, .tagged _ c => drawnOf fuel M o c

/-- The farthest a point of the polylines `a` is from the polylines `b` (their segments, closing
segments included). -/
def farthest (a b : Array Polyline) : Float :=
  let segs := b.flatMap fun pl => polylineSegments pl
  let pts := b.flatMap (·.points)
  a.foldl (init := 0) fun acc pl => pl.points.foldl (init := acc) fun acc q =>
    let d := if segs.isEmpty then pts.foldl (init := 1e300) (fun m r => min m (q.dist r))
      else distToSegments q segs
    max acc d

/-- How far two lists of polylines are apart: `0` when they have the same points within `tol`,
else the larger of the two one-sided distances (Hausdorff's), or infinity when their numbers or
kinds of polylines differ. -/
def linesApart (a b : Array Polyline) (tol : Float) : Float :=
  if a.size != b.size || (a.zip b).any (fun (x, y) => x.closed != y.closed) then 1e300
  else if (a.zip b).all fun (x, y) => x.points.size == y.points.size &&
      (x.points.zip y.points).all fun (u, v) => u.dist v ≤ tol then 0
  else max (farthest a b) (farthest b a)

/-- How far the baked drawing at a rest may be from the still: `restTolerance` (0.05 px) for every
path and text, plus for each path `5.5e-4 r`, `r` half the larger side of its box (a circle's
radius): the most two cubic approximations of one circle can differ (each is within `2.73e-4 r`
of the circle, `Path.arc`), since a circle or arc turned by a move is not drawn by the same cubics
as the next key draws it. The comparison is between outlines: it does not see the phase of a
dash pattern (a dashed circle turned about its own centre passes while its dashes move). -/
def restTolerance : Float := 0.05

/-- The first way the drawing `baked` differs from the drawing `still` beyond the rest tolerance
(see `restTolerance`): another number of elements, an element of another kind or paint, a path
farther away, a text elsewhere or turned. -/
def drawingDiff (baked still : Array Drawn) : Option String := Id.run do
  if baked.size != still.size then
    return some s!"draws {baked.size} elements where the still draws {still.size}"
  for (i, b, k) in (baked.zip still).mapIdx fun i (b, k) => (i, b, k) do
    match b, k with
    | .path pb lb, .path pk lk =>
      if pb != pk then return some s!"paints element {i} otherwise ({pb}, the still {pk})"
      let pts := lk.flatMap (·.points)
      let half := match pts[0]? with
        | none => 0
        | some q0 =>
          let (lo, hi) := pts.foldl (init := (q0, q0)) fun (lo, hi) q =>
            ((⟨min lo.x q.x, min lo.y q.y⟩ : Point), (⟨max hi.x q.x, max hi.y q.y⟩ : Point))
          max (hi.x - lo.x) (hi.y - lo.y) / 2
      let tol := restTolerance + 5.5e-4 * half
      let d := linesApart lb lk tol
      if !(d ≤ tol) then
        return some s!"draws element {i} {fmtNum d 3} px from the still (tolerance {fmtNum tol 3})"
    | .text kb ab tb, .text kk ak tk =>
      if kb != kk then return some s!"writes text element {i} otherwise ({kb}, the still {kk})"
      if !(ab.dist ak ≤ restTolerance) then
        return some s!"places text element {i} {fmtNum (ab.dist ak) 3} px from the still"
      if !((tb - tk).abs ≤ 1e-4) then
        return some s!"turns text element {i} by {fmtNum ((tb - tk) * 180 / pi) 4}°"
    | _, _ => return some s!"draws element {i} as another kind of element than the still"
  return none

/-! ### The writer against the baker -/

/-- The transform of a value of an `animateTransform` of type `type` (`rotate` or `translate`). -/
def transformOfValue (type : String) (v : Array Float) : Affine :=
  if type == "rotate" then rotAbout ⟨v.getD 1 0, v.getD 2 0⟩ (v.getD 0 0)
  else Affine.translate (v.getD 0 0) (v.getD 1 0)

/-- A point written as `x y`. -/
def pointOfText (s : String) : Point :=
  match (s.splitOn " ").map Raster.parseNumber? with
  | [some x, some y] => ⟨x, y⟩
  | _ => ⟨0, 0⟩

/-- What a written tree shows at the time `t`, read with `Smil.valueAt` alone: every element with
`data-pilean-actor` or `data-pilean-upright`, in document order, with what it stands for, the
page point its anchor is drawn at, its opacity and the whole transform its content is under;
`none` where an animation does not evaluate; at most `fuel` deep. -/
def writtenMarkers (t : Float) : Nat → Affine → Float → Node →
    Option (Array (String × Point × Float × Affine))
  | 0, _, _, _ => some #[]
  | _, _, _, .text _ => some #[]
  | fuel + 1, M, o, .element _ attrs cs => do
    let mut M := M
    let mut o := o
    for c in cs do
      if let .element n as _ := c then
        if n == "animateTransform" then
          M := M.comp (transformOfValue ((Smil.attr? as "type").getD "") (← Smil.valueAt c t))
        else if n == "animate" && Smil.attr? as "attributeName" == some "opacity" then
          o := o * (← Smil.valueAt c t).getD 0 1
    let upright := Smil.attr? attrs "data-pilean-upright"
    let own := match Smil.attr? attrs "data-pilean-actor", upright with
      | some id, _ =>
        #[(s!"actor {id}", M.apply (pointOfText ((Smil.attr? attrs "data-pilean-anchor").getD "")),
          o, M)]
      | none, some a => #[("upright", M.apply (pointOfText a), o, M)]
      | none, none => #[]
    let rest ← cs.mapM (writtenMarkers t fuel M o)
    return own ++ rest.flatten

/-- Whether two transforms agree within `tol` in every coefficient. -/
def affineNear (a b : Affine) (tol : Float) : Bool :=
  [(a.a, b.a), (a.b, b.b), (a.c, b.c), (a.d, b.d), (a.e, b.e), (a.f, b.f)].all fun (x, y) =>
    (x - y).abs < tol

/-- The first way the written moving picture `nodes` disagrees, at the time `t`, with the marked
points `baked` of a baker (`MotionPlan.markersAt`, in document order): another number of actors
than `actors` or of upright groups than `ups`, an anchor farther than `1e-6` px, an opacity or a
coefficient of a transform off by more than `1e-6`. -/
def markersDiff (baked : Array (String × Point × Float × Affine)) (actors ups : Nat)
    (nodes : Array Node) (t : Float) : Option String :=
  match nodes.mapM (writtenMarkers t 256 Affine.id 1) with
  | none => some "has an animation that does not evaluate"
  | some ws =>
    let written := ws.flatten
    if (written.filter (·.1 != "upright")).size != actors then
      some s!"shows {(written.filter (·.1 != "upright")).size} actors where the plan has {actors}"
    else if (written.filter (·.1 == "upright")).size != ups then
      some s!"shows {(written.filter (·.1 == "upright")).size} upright groups where the plan has \
        {ups}"
    else if written.size != baked.size then some "shows another number of marked elements"
    else
      (written.zip baked).findSome? fun ((n, q, o, M), (n', q', o', M')) =>
        if n != n' then some s!"shows {n} where the baked drawing has {n'}"
        else if !(q.dist q' < 1e-6) then
          some s!"draws the anchor of {n} {fmtNum (q.dist q') 7} px from the baked drawing"
        else if !((o - o').abs < 1e-6) then some s!"shows {n} at another opacity"
        else if !affineNear M M' 1e-6 then some s!"puts {n} under another transform"
        else none

/-- The first way the written moving picture `nodes` disagrees, at the time `t`, with the baker
of the plan `p`: another number of actors or of upright groups than the plan declares, an anchor
farther than `1e-6` px, an opacity or a coefficient of a transform off by more than `1e-6`. -/
def writerDiff (p : MotionPlan) (nodes : Array Node) (t : Float) : Option String :=
  markersDiff (p.markersAt t) p.markerCounts.1 p.markerCounts.2 nodes t

namespace Motion

variable (m : Motion)

/-- The steps whose easing cannot be divided exactly at the ends of the windows of their fades
(`divideSegments`), as errors: their parts are drawn without easing. -/
def _root_.PILean.Plane.inexactProblems (steps : Array Nat) : Array MotionProblem :=
  steps.map fun j =>
    { severity := .error, message := s!"step {j + 1}: its easing cannot be divided exactly at the \
        ends of the windows of its fades (a part of its curve is not a timing curve), so its parts \
        would be drawn without easing; move the windows, or give the step another easing" }

/-- The baker against the stills: at the middle of each key's rest (of its last part, after its
fades, `Timeline.restTime`), the whole baked drawing
(`MotionPlan.figureAtUnchecked`: every path and every text, in order) must be the still of that
key (the drawing of `keyFigure k`) within the rest tolerance (`drawingDiff`). This pins the
animation to the exact keys for every motion: a turn carried through many steps (each landing
within `arrivalTolerance`), a wrong upright position, or another stacking order shows here. -/
def restProblems (K : MotionKeys) (p : MotionPlan) : Array MotionProblem :=
  (Array.range m.keys.size).filterMap fun k =>
    let t := Exact.toFloat (p.timeline.restTime k)
    let baked := drawnOf 256 Affine.id 1 (p.figureAtUnchecked t)
    let still := drawnOf 256 Affine.id 1 (K.figure k).draw
    (drawingDiff baked still).map fun why =>
      { severity := .error, message := s!"at the rest on key {k} the animation {why}" }

/-- The writer against the baker: at the middle of every segment of the timeline (every rest and
every move), the written moving picture read with `Smil.valueAt` (`writtenMarkers`) must show what
the baker draws (`writerDiff`): this checks what the baker never reads, such as the angles of the
counter-rotations of upright leaves. -/
def writerProblems (p : MotionPlan) : Array MotionProblem :=
  let nodes := p.toNodesUnchecked
  match p.timeline.segments.findSome? fun s =>
      let t := Exact.toFloat (s.start + s.dur / 2)
      (writerDiff p nodes t).map fun why => s!"at {fmtNum t 3} s the written animation {why}" with
  | some msg => #[{ severity := .error, message := msg }]
  | none => #[]

end Motion

/-- The page points of a drawing under the transform `M`, at most `fuel` deep: the points of
every path flattened to `0.5` px and the anchor point of every text. -/
def shapePoints : Nat → Affine → Shape → Array Point
  | 0, _, _ => #[]
  | _, M, .path q .. => ((q.transform M).flatten 0.5).flatMap (·.points)
  | _, M, .text _ at_ .. => #[M.apply at_]
  | fuel + 1, M, .group cs t _ _ => cs.flatMap (shapePoints fuel (M.comp t))
  | fuel + 1, M, .tagged _ c => shapePoints fuel M c

/-- How far outside its box a drawn point may lie (pixels). -/
def boundsTolerance : Float := 0.5

/-- What leaves the box `box` (page coordinates) while the plan `p` moves: at a ninth, two ninths,
…, eight ninths of every segment of every move, every point of every layer shown then
(`shapePoints`: its paths and its texts' anchors, turned and slid as its chain has them) must lie
in the box within `boundsTolerance`; each layer that leaves it is reported once per step, as
`… leaves {place} during step …`. -/
def boundsProblems (p : MotionPlan) (box : Box) (place : String) : Array MotionProblem :=
  let inside := fun (q : Point) =>
    box.x0 - boundsTolerance ≤ q.x && q.x ≤ box.x1 + boundsTolerance &&
      box.y0 - boundsTolerance ≤ q.y && q.y ≤ box.y1 + boundsTolerance
  let found := p.timeline.segments.toList.flatMap fun s => match s.kind with
    | .move j => (List.range 8).flatMap fun i =>
      let t := Exact.toFloat (s.start + s.dur * ((i + 1 : Nat) : Rat) / 9)
      (p.layers.toList.zipIdx.filter fun (L, _) =>
          p.opacityAt L t > 1e-3 &&
            !((p.layerShape L t).flatMap (shapePoints 256 Affine.id)).all inside).map
        fun (_, li) => (li, j)
    | _ => []
  (found.eraseDups.toArray.map fun (li, j) =>
    let what := match (p.layers.getD li default).version.actor with
      | some id => id
      | none => "an item without an id"
    { severity := .error, message := s!"{what} leaves {place} during step {j + 1}" })

/-- A motion with its keys as drawn, its plan and its problems, computed once: the checked
outputs (`svg?`, `animation?`) and the build's messages read it, so a consumer computes the
problems of a motion once (`Motion.report`). -/
structure MotionReport where
  /-- The motion. -/
  motion : Motion
  /-- Its keys as drawn. -/
  keys : MotionKeys
  /-- Its plan. -/
  plan : MotionPlan
  /-- The segments its timeline's division divides unsoundly (`Motion.unsoundOf`; none for a
  motion that is not well formed): they stop it at every level, and its plan is then laid out on
  its base timeline undivided (`MotionDivision.soundOn`). -/
  unsound : Array SegKind := #[]
  /-- Its problems (`Motion.problems`). -/
  problems : Array MotionProblem

namespace Motion

variable (m : Motion)

/-- The motion checked: the problems of its keys and steps (`keyProblems`) and, for a well-formed
motion, the segments its writer divides unsoundly (`unsoundProblems`); when there are none, a
step whose easing its windows cannot divide exactly (`inexactProblems`), and the problems of its
plan against the stills (`restProblems`), of its writer against its baker (`writerProblems`) and
of what leaves the picture while it moves (`boundsProblems`); otherwise a note that these were not
checked. -/
def report : MotionReport :=
  let K := m.keysOf
  let p := m.planIn K K.env
  let base := m.keyProblems
  let f := p.env.frame
  let unsound := if decide m.WellFormed then m.unsoundOf K else #[]
  let problems := if !decide m.WellFormed then base
    else if !unsound.isEmpty then
      base ++ unsoundProblems unsound |>.push { severity := .note, message := "the motion was \
        not checked against its stills, its writer against its baker or its bounds, because its \
        timeline is divided unsoundly" }
    else base ++ inexactProblems (m.inexactSteps K) ++
      m.restProblems K p ++ writerProblems p ++
      boundsProblems p ⟨0, 0, f.width, f.height⟩ "the picture"
  { motion := m, keys := K, plan := p, unsound, problems }

/-- The problems of the motion (`report`). -/
def problems : Array MotionProblem := m.report.problems

end Motion

namespace MotionReport

variable (r : MotionReport)

/-- The messages of the problems a build reports (unless the level is `ignore`), each with its
severity. -/
def checkMessages : Array String :=
  if r.motion.checks == .ignore then #[]
  else r.problems.map fun p => match p.severity with
    | .error => p.message
    | .note => s!"note: {p.message}"

/-- Whether the problems stop the motion from being rendered: an error under `CheckLevel.fail`
(the default), and at every level a motion that is not well formed (`Motion.WellFormed`) or a
segment divided unsoundly (`unsound`, a fault of the writer). -/
def problemsFail : Bool :=
  (r.motion.checks == .fail && r.problems.any (·.severity == .error)) ||
    !decide r.motion.WellFormed || !r.unsound.isEmpty

/-- The messages of the errors. -/
def errors : Array String := (r.problems.filter (·.severity == .error)).map (·.message)

/-- The messages of the errors that stop the motion (`problemsFail`): every error under
`CheckLevel.fail` or of a motion that is not well formed, those of the segments divided unsoundly
at the other levels. -/
def stopErrors : Array String :=
  if r.motion.checks == .fail || !decide r.motion.WellFormed then r.errors
  else (unsoundProblems r.unsound).map (·.message)

/-- The motion's animated SVG, or, when its problems stop it (`problemsFail`), the messages of its
errors: a motion that contradicts its keys is not written. -/
def svg? : Except (Array String) String :=
  if r.problemsFail then .error r.stopErrors
  else .ok ("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
    Svg.render 0 (r.motion.svgRootIn r.keys r.plan) ++ "\n")

/-- The motion as an `Animation` of its baked drawings, whatever its problems (they travel with
it, `Animation.problems`): one cycle at `fps` frames a second, the poster at the middle of the
poster key's rest. -/
def toAnimationUnchecked (fps : Nat := 30) : Animation :=
  let p := r.plan
  let fig := r.keys.figure 0
  let f := p.env.frame
  { width := f.width.round.toUInt64.toNat, height := f.height.round.toUInt64.toNat, fps,
    duration := Exact.toFloat p.timeline.cycle, frame := p.figureAtUnchecked,
    posterTime := some (Exact.toFloat (p.timeline.restTime r.motion.poster)),
    background := fig.style.background, fontFamily := fig.style.fontFamily,
    text := fig.style.text, srgb := true, textAsShapes := fig.textAsShapes,
    problems := fun _ => r.checkMessages, problemsFail := r.problemsFail }

/-- The motion as an `Animation` of its baked drawings (`toAnimationUnchecked`), or, when its
problems stop it, the messages of its errors. -/
def animation? (fps : Nat := 30) : Except (Array String) Animation :=
  if r.problemsFail then .error r.stopErrors else .ok (r.toAnimationUnchecked fps)

end MotionReport

namespace Motion

variable (m : Motion)

/-- The messages of the motion's problems (`MotionReport.checkMessages`). To use several of the
checked outputs, compute `report` once and read them from it. -/
def checkMessages : Array String := m.report.checkMessages

/-- Whether the motion's problems stop it (`MotionReport.problemsFail`). -/
def problemsFail : Bool := m.report.problemsFail

/-- The motion's animated SVG, or the messages of the errors that stop it (`MotionReport.svg?`). -/
def svg? : Except (Array String) String := m.report.svg?

/-- The motion as an `Animation`, or the messages of the errors that stop it
(`MotionReport.animation?`). -/
def animation? (fps : Nat := 30) : Except (Array String) Animation := m.report.animation? fps

/-- The motion as an `Animation`, whatever its problems (`MotionReport.toAnimationUnchecked`). -/
def toAnimationUnchecked (fps : Nat := 30) : Animation := m.report.toAnimationUnchecked fps

end Motion

/-- A report that gives an SVG is of a well-formed motion with no segment divided unsoundly
(`MotionReport.problemsFail`). -/
theorem MotionReport.wellFormed_of_svg {r : MotionReport} {s : String} (h : r.svg? = .ok s) :
    r.motion.WellFormed ∧ r.unsound.isEmpty = true := by
  unfold MotionReport.svg? at h
  split at h
  · cases h
  · rename_i hp
    simp only [MotionReport.problemsFail, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, not_or] at hp
    obtain ⟨⟨_, hw⟩, hu⟩ := hp
    simp only [Bool.not_eq_false] at hw hu
    exact ⟨of_decide_eq_true (by simpa using hw), by simpa using hu⟩

namespace Motion

variable (m : Motion)

/-- The report of a motion is of that motion. -/
theorem report_motion : m.report.motion = m := rfl

/-- The segments the report of a well-formed motion holds as divided unsoundly are those of its
timeline's division (`Motion.unsoundOf`). -/
theorem report_unsound (h : m.WellFormed) : m.report.unsound = m.unsoundOf m.keysOf := by
  change (if decide m.WellFormed then m.unsoundOf m.keysOf else #[]) = _
  simp [h]

/-- The timeline of a motion that gives an SVG (`Motion.svg?`) is its base timeline divided into
exactly the division's parts. -/
theorem timeline_eq_of_svg {s : String} (h : m.svg? = .ok s) :
    m.timeline = m.baseTimeline.divide
      ((m.divisionOn m.keysOf m.baseTimeline).parts (m.baseTimeline.keys - 1)) := by
  obtain ⟨hw, hu⟩ := MotionReport.wellFormed_of_svg (r := m.report) h
  rw [report_motion] at hw
  rw [report_unsound m hw] at hu
  exact timeline_eq_of_sound m hu

end Motion

end PILean.Plane
