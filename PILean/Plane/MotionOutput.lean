/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plane.MotionPlan

/-!
# Motions of plane figures: outputs and the check against the stills

The outputs of a `Motion` laid out as a `MotionPlan` (`PILean.Plane.MotionPlan`): the animated SVG
(`Motion.svgRoot`, `Motion.toSvg`, and `Motion.svg?`, which writes nothing for a motion whose
problems stop it), the baked drawing at a time (`Motion.figureAt`) and the `Animation` of the baked
drawings (`Motion.toAnimation`).

**The stills pin the animation.** `Motion.restProblems` compares, at the middle of every key's
rest, the whole baked drawing (every path and every text, in order: `Drawn`, `drawnOf`) with the
key's still, within `restTolerance` (0.05 px, plus `5.5e-4` of a path's half-diagonal for the
cubic approximations of turned circles, `drawingDiff`). `Motion.problems` is the problems of the
keys and steps (`Motion.keyProblems`) with these.

## Main definitions

* `Motion.svgRoot`, `Motion.toSvg`, `Motion.svg?`, `Motion.figureAt`, `Motion.toAnimation`.
* `Drawn`, `drawnOf`, `drawingDiff`, `restTolerance`, `Motion.restProblems`.
* `Motion.problems`, `Motion.checkMessages`, `Motion.problemsFail`.
-/

namespace PILean.Plane

open Canvas Anim Svg

/-! ### The motion's outputs -/

namespace Motion

variable (m : Motion)

/-- The text alternative of the motion: its description and the captions of its keys. -/
def description : String :=
  " ".intercalate ((if m.info.description.isEmpty then [] else [m.info.description]) ++
    m.captions.toList)

/-- The root element of the motion's animated SVG: the background; the moving picture
(`MotionPlan.toNodes`) in a group of class `pilean-motion-live`; and the poster key's still in a
group of class `pilean-motion-poster`, which a style rule shows instead under reduced motion
(`Animation.reducedMotionStyle`). The root has `role="img"`, the motion's title and a
description with the captions. -/
def svgRoot : Node :=
  let K := m.keysOf
  let p := m.planIn K K.env
  let f := p.env.frame
  let w := f.width.round
  let h := f.height.round
  let poster := (K.figure m.poster).svgNodes.map (prefixIds "poster-" 256)
  let head := (if m.info.title.isEmpty then #[] else #[el "title" #[] #[.text m.info.title]]) ++
    (if m.description.isEmpty then #[] else #[el "desc" #[] #[.text m.description]])
  el "svg" #[("xmlns", "http://www.w3.org/2000/svg"), ("width", fmtNum w),
    ("height", fmtNum h), ("viewBox", s!"0 0 {fmtNum w} {fmtNum h}"), ("role", "img")]
    (head ++ #[Animation.reducedMotionStyle] ++ p.background.render p.mode ++
      #[el "g" #[("class", Animation.liveClass)] p.toNodes,
        el "g" #[("class", Animation.posterClass)] poster])

/-- The motion as an animated SVG document (`svgRoot`), whatever its problems; `svg?` refuses a
motion whose problems stop it. -/
def toSvg : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++ Svg.render 0 m.svgRoot ++ "\n"

/-- The motion at the time `t` (seconds) as a drawing (`MotionPlan.figureAt`). -/
def figureAt (t : Float) : Shape := m.plan.figureAt t

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

/-- How far the baked drawing at a rest may be from the still: `restTolerance` (0.05 px), plus
for each path `5.5e-4` times half the diagonal of its box, the most two cubic approximations of
one circle can differ (each is within `2.73e-4 r` of the circle, `Path.arc`), since a circle or
arc turned by a move is not drawn by the same cubics as the next key draws it. -/
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
          lo.dist hi / 2
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

namespace Motion

variable (m : Motion)

/-- The baker against the stills: at the middle of each key's rest, the whole baked drawing
(`MotionPlan.figureAt`: every path and every text, in order) must be the still of that key (the
drawing of `keyFigure k`) within the rest tolerance (`drawingDiff`). This pins the animation to
the exact keys for every motion: a turn carried through many steps (each landing within
`arrivalTolerance`), a wrong upright counter-rotation, or another stacking order shows here. -/
def restProblems (K : MotionKeys) (p : MotionPlan) : Array MotionProblem :=
  (Array.range m.keys.size).filterMap fun k =>
    let t := Exact.toFloat (p.timeline.restTime k)
    let baked := drawnOf 256 Affine.id 1 (p.figureAt t)
    let still := drawnOf 256 Affine.id 1 (K.figure k).draw
    (drawingDiff baked still).map fun why =>
      { severity := .error, message := s!"at the rest on key {k} the animation {why}" }

/-- The problems of the motion: those of its keys and steps (`keyProblems`), and, for a
well-formed motion, those of its layout against the stills (`restProblems`). -/
def problems : Array MotionProblem :=
  let base := m.keyProblems
  if !decide m.WellFormed then base
  else
    let K := m.keysOf
    base ++ m.restProblems K (m.planIn K K.env)

/-- The messages of the problems a build reports (unless the level is `ignore`), each with its
severity. -/
def checkMessages : Array String :=
  if m.checks == .ignore then #[]
  else m.problems.map fun p => match p.severity with
    | .error => p.message
    | .note => s!"note: {p.message}"

/-- Whether the problems stop the motion from being rendered: an error under `CheckLevel.fail`
(the default). -/
def problemsFail : Bool := m.checks == .fail && m.problems.any (·.severity == .error)

/-- The motion's animated SVG (`toSvg`), or, when its problems stop it (`problemsFail`), the
messages of its errors: a motion that contradicts its keys is not written. -/
def svg? : Except (Array String) String :=
  let ps := m.problems
  if m.checks == .fail && ps.any (·.severity == .error) then
    .error ((ps.filter (·.severity == .error)).map (·.message))
  else .ok m.toSvg

end Motion

namespace Motion

variable (m : Motion)

/-- The motion as an `Animation` of its baked drawings, for animated PNG and GIF: one cycle at
`fps` frames a second, the poster at the middle of the poster key's rest. -/
def toAnimation (fps : Nat := 30) : Animation :=
  let K := m.keysOf
  let p := m.planIn K K.env
  let fig := K.figure 0
  let f := p.env.frame
  { width := f.width.round.toUInt64.toNat, height := f.height.round.toUInt64.toNat, fps,
    duration := Exact.toFloat p.timeline.cycle, frame := p.figureAt,
    posterTime := some (Exact.toFloat (p.timeline.restTime m.poster)),
    background := fig.style.background, fontFamily := fig.style.fontFamily,
    text := fig.style.text, srgb := true, textAsShapes := fig.textAsShapes,
    problems := fun _ => m.checkMessages, problemsFail := m.problemsFail }

end Motion

end PILean.Plane
