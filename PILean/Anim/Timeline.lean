/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Exact

/-!
# Timelines of key-frame motions

The timing of a looping motion through key frames, with no drawing: when each key frame is held,
when each step between two key frames runs, how its progress is eased, and how the loop closes.

A timeline of `n + 1` key frames, from `n` steps, is the sequence of segments

* a rest on key `0` (`Pacing.firstHold`);
* for each step `i < n`, a move from key `i` to key `i + 1` (the step's duration), then a rest on
  key `i + 1` (`Pacing.hold`, or `Pacing.lastHold` after the last step);

closed by the seam (`Seam`): under `Seam.cut` nothing is added and the picture jumps from the last
key back to key `0` when the cycle repeats; under `Seam.crossfade d` the cycle starts with a fade
in (`SegKind.seamIn`, `d / 2`) and ends with a fade out (`SegKind.seamOut`, `d / 2`), so that the
jump from the last key back to key `0` happens where the cycle repeats, while nothing is visible.

Durations are exact rational numbers of seconds (`Rat`), so the start of every segment, the length
of the cycle and the segment boundaries as fractions of the cycle (`Timeline.keyTimes`) are exact,
and the statements about them (`PILean/Anim/TimelineProofs.lean`) are theorems about rationals.
A negative duration counts as zero. Floating point begins with the eased progress through a
segment (`Easing.eval`, `Timeline.locate`).

## Main definitions

* `Easing`, `Easing.eval`: the cubic Bézier timing functions of SMIL's `keySplines` and CSS.
* `Pacing`, `Step`, `Seam`: the durations of a motion and how its loop closes.
* `Segment`, `Timeline`, `Timeline.build`: the segments of a cycle, their kinds
  (`Timeline.kinds`) and their durations and easings (`Timeline.spec`).
* `Timeline.segmentAt`, `Timeline.locate`: the segment at a time and the eased progress through it.
* `Timeline.restTime`, `Timeline.keyTimes`.

## References

* Synchronized Multimedia Integration Language (SMIL 3.0), W3C Recommendation 1 December 2008,
  section 5.4 ("Animation function calculation", `calcMode="spline"`, `keySplines`).
* CSS Easing Functions Level 1, section 3.3 ("Cubic Bézier easing functions").
-/

namespace PILean.Anim

/-! ### Easing -/

/-- How progress through a segment is eased: the identity, or a cubic Bézier curve from `(0, 0)` to
`(1, 1)` with the control points `(x₁, y₁)` and `(x₂, y₂)`, as in SMIL's `keySplines` and CSS's
`cubic-bezier`. Control values outside `[0, 1]` are clamped into it, as SMIL requires, so the eased
progress never overshoots. -/
inductive Easing where
  /-- The identity: progress is not eased. -/
  | linear
  /-- The cubic Bézier curve with control points `(x₁, y₁)` and `(x₂, y₂)`. -/
  | spline (x₁ y₁ x₂ y₂ : Float)
  deriving Inhabited, Repr, BEq

namespace Easing

/-- The ease in and out of CSS's `ease-in-out`, `cubic-bezier(0.42, 0, 0.58, 1)`. -/
def standard : Easing := .spline 0.42 0 0.58 1

/-- `x` clamped into `[0, 1]` (`0` for a value that is not a number). -/
def clamp01 (x : Float) : Float := if x.isNaN || x ≤ 0 then 0 else if x ≥ 1 then 1 else x

/-- The control values `x₁ y₁ x₂ y₂`, clamped into `[0, 1]`; the identity is the curve
`0 0 1 1`. -/
def controls : Easing → Float × Float × Float × Float
  | .linear => (0, 0, 1, 1)
  | .spline x₁ y₁ x₂ y₂ => (clamp01 x₁, clamp01 y₁, clamp01 x₂, clamp01 y₂)

/-- One coordinate of the cubic Bézier curve from `0` to `1` with the control values `a` and `b`,
at the parameter `s`: `3 (1 - s)² s a + 3 (1 - s) s² b + s³`. -/
def bezier (a b s : Float) : Float :=
  let r := 1 - s
  3 * r * r * s * a + 3 * r * s * s * b + s * s * s

/-- The parameter `s ∈ [0, 1]` at which the curve's first coordinate is `x`, found by 64 halvings
of `[0, 1]` (the first coordinate does not decrease with `s`, because both of its control values
are in `[0, 1]`). -/
def solve (e : Easing) (x : Float) : Float := Id.run do
  let (x₁, _, x₂, _) := e.controls
  let mut lo : Float := 0
  let mut hi : Float := 1
  for _ in [0:64] do
    let mid := (lo + hi) / 2
    if bezier x₁ x₂ mid < x then lo := mid else hi := mid
  return (lo + hi) / 2

/-- The eased progress at the progress `x`: `0` up to `x = 0`, `1` from `x = 1`, and in between
the second coordinate of the curve where its first coordinate is `x`. The parameter is found to
within `2⁻⁶⁴`, so the first coordinate there is within `1e-15` of `x`; where the curve is steep the
second coordinate can only be as precise as that. -/
def eval (e : Easing) (x : Float) : Float :=
  if x.isNaN || x ≤ 0 then 0
  else if x ≥ 1 then 1
  else match e with
    | .linear => x
    | .spline .. =>
      let (_, y₁, _, y₂) := e.controls
      bezier y₁ y₂ (e.solve x)

end Easing

/-! ### Pacing and steps -/

/-- How the loop of a motion closes. -/
inductive Seam where
  /-- The picture fades out at the end of the cycle and in at its start, `d` seconds in all (half
  each); the jump back to the first key happens while nothing is visible. -/
  | crossfade (d : Rat)
  /-- The picture jumps from the last key back to the first when the cycle repeats. -/
  | cut
  deriving Inhabited, Repr, DecidableEq

/-- What a step between two key frames does (for the caller; the timing depends only on the
step's duration and easing). -/
inductive StepKind where
  /-- Something moves. -/
  | move
  /-- Nothing moves (an operation that leaves the picture as it is): the step takes its time. -/
  | idle
  deriving Inhabited, Repr, DecidableEq

/-- The durations of a motion, in seconds, its easing and its seam. -/
structure Pacing where
  /-- A turn about a centre. -/
  turn : Rat := 1.0
  /-- A slide along a vector. -/
  slide : Rat := 0.8
  /-- An appearance or a disappearance. -/
  fade : Rat := 0.35
  /-- The rest on a key frame between two steps. -/
  hold : Rat := 0.6
  /-- A step in which nothing moves. -/
  idle : Rat := 0.9
  /-- The rest on the first key frame. -/
  firstHold : Rat := 1.2
  /-- The rest on the last key frame. -/
  lastHold : Rat := 1.8
  /-- The easing the steps made from this pacing (`turnStep`, `slideStep`, `fadeStep`) get. -/
  easing : Easing := .standard
  /-- How the loop closes. -/
  seam : Seam := .crossfade 0.4
  deriving Inhabited, Repr

/-- A step between two consecutive key frames: what it does, how long it takes, in seconds, and how
its progress is eased. -/
structure Step where
  /-- What the step does. -/
  kind : StepKind := .move
  /-- How long it takes, in seconds. -/
  dur : Rat
  /-- How its progress is eased. -/
  easing : Easing := .standard
  deriving Inhabited, Repr

namespace Pacing

variable (p : Pacing)

/-- A turn, `turn` seconds long, eased with `easing`. -/
def turnStep : Step := { dur := p.turn, easing := p.easing }

/-- A slide, `slide` seconds long, eased with `easing`. -/
def slideStep : Step := { dur := p.slide, easing := p.easing }

/-- An appearance or a disappearance, `fade` seconds long, eased with `easing`. -/
def fadeStep : Step := { dur := p.fade, easing := p.easing }

/-- A step in which nothing moves, `idle` seconds long, not eased. -/
def idleStep : Step := { kind := .idle, dur := p.idle, easing := .linear }

/-- Half the length of the seam: the length of the fade in and of the fade out (`0` for a cut). -/
def seamHalf : Rat :=
  match p.seam with
  | .crossfade d => d / 2
  | .cut => 0

end Pacing

/-! ### Segments and timelines -/

/-- What happens during a segment of a timeline. -/
inductive SegKind where
  /-- Key frame `key` is shown, still. -/
  | rest (key : Nat)
  /-- Step `step` runs, from key `step` to key `step + 1`. -/
  | move (step : Nat)
  /-- The fade out at the end of the cycle (under `Seam.crossfade`), on the last key. -/
  | seamOut
  /-- The fade in at the start of the cycle (under `Seam.crossfade`), on key `0`. -/
  | seamIn
  deriving Inhabited, Repr, DecidableEq

/-- A segment of a timeline: what happens, when it starts and how long it lasts (in seconds,
exactly), and how its progress is eased. -/
structure Segment where
  /-- What happens. -/
  kind : SegKind
  /-- The start, in seconds from the start of the cycle. -/
  start : Rat
  /-- The duration, in seconds. -/
  dur : Rat
  /-- The easing of the progress through the segment. -/
  easing : Easing
  deriving Inhabited, Repr

/-- The end of a segment, in seconds from the start of the cycle. -/
def Segment.stop (s : Segment) : Rat := s.start + s.dur

/-- The timing of a looping motion through key frames: its segments in order and the length of its
cycle, in seconds. -/
structure Timeline where
  /-- The number of key frames. -/
  keys : Nat
  /-- The segments, in order. -/
  segments : Array Segment
  /-- The length of the cycle, in seconds. -/
  cycle : Rat
  deriving Inhabited, Repr

namespace Timeline

/-- A segment before its start is known: what happens, its duration and its easing. -/
abbrev Piece := SegKind × Rat × Easing

/-- The kinds of the segments of the timeline of `steps`, in order: the rest on key `0`, then for
each step `j` its move and the rest on key `j + 1`; under a crossfade, the fade in first and the
fade out last. -/
def kinds (steps : Array Step) (p : Pacing) : List SegKind :=
  let body := .rest 0 :: (List.range steps.size).flatMap fun j => [.move j, .rest (j + 1)]
  match p.seam with
  | .cut => body
  | .crossfade _ => .seamIn :: body ++ [.seamOut]

/-- The duration (a negative one counting as zero once laid out) and the easing of the segment of
kind `k`: the rest on key `0` lasts `firstHold`, the rest on the last key `lastHold`, any other rest
`hold`; the move of step `j` lasts as long as the step, with its easing; a fade lasts half the
seam. Rests and fades are not eased. -/
def spec (steps : Array Step) (p : Pacing) : SegKind → Rat × Easing
  | .rest k =>
    (if k = 0 then p.firstHold else if k = steps.size then p.lastHold else p.hold, .linear)
  | .move j =>
    match steps[j]? with
    | some s => (s.dur, s.easing)
    | none => (0, .linear)
  | .seamIn | .seamOut => (p.seamHalf, .linear)

/-- The pieces of the timeline of `steps`: each kind with its duration and easing. -/
def pieces (steps : Array Step) (p : Pacing) : List Piece :=
  (kinds steps p).map fun k => (k, spec steps p k)

/-- The segments of the pieces laid end to end from `start`, each lasting its duration (a negative
one counts as zero). -/
def layout : Rat → List Piece → List Segment
  | _, [] => []
  | start, (k, d, e) :: rest => ⟨k, start, max d 0, e⟩ :: layout (start + max d 0) rest

/-- The total duration of the pieces (a negative one counting as zero). -/
def total : List Piece → Rat
  | [] => 0
  | (_, d, _) :: rest => max d 0 + total rest

/-- The timeline of a motion through `steps.size + 1` key frames: a rest on key `0`, then each
step and the rest on the key it reaches, closed by the seam (see the module docstring). -/
def build (steps : Array Step) (p : Pacing) : Timeline where
  keys := steps.size + 1
  segments := (layout 0 (pieces steps p)).toArray
  cycle := total (pieces steps p)

variable (tl : Timeline)

/-- The segment boundaries in seconds: the start of every segment, then the end of the cycle. -/
def boundaries : Array Rat := (tl.segments.map (·.start)).push tl.cycle

/-- The segment boundaries as fractions of the cycle: `0`, then the start of every other segment,
then `1` (when the cycle is longer than zero; when it is zero, every fraction is `0`). -/
def keyTimes : Array Rat := tl.boundaries.map (· / tl.cycle)

/-- The time `t` (in seconds, any rational) brought into the cycle: `t` minus a whole number of
cycles, in `[0, cycle)`. A cycle of length zero brings every time to `0`. -/
def wrap (t : Rat) : Rat := if tl.cycle ≤ 0 then 0 else t - tl.cycle * (t / tl.cycle).floor

/-- The index of the first segment of the list that ends after `u`, or the list's length if
there is none. -/
def findSeg (u : Rat) : List Segment → Nat
  | [] => 0
  | s :: rest => if u < s.stop then 0 else findSeg u rest + 1

/-- The index of the segment running at the time `t` (brought into the cycle with `wrap`): the
first that ends after it, which is the one that contains it (`segmentAt_mem`). -/
def segmentAt (t : Rat) : Nat := findSeg (tl.wrap t) tl.segments.toList

/-- The exact progress through the segment running at the time `t`: the fraction of its duration
that has passed, in `[0, 1)` (`0` for a segment of length zero). -/
def progress (t : Rat) : Rat :=
  match tl.segments[tl.segmentAt t]? with
  | some s => if s.dur = 0 then 0 else (tl.wrap t - s.start) / s.dur
  | none => 0

/-- The segment running at the time `t` (in seconds, exact) and the eased progress through it: the
segment's easing applied to `progress t` converted to `Float` (where floating point begins). -/
def locate (t : Rat) : SegKind × Float :=
  match tl.segments[tl.segmentAt t]? with
  | some s => (s.kind, s.easing.eval (Exact.toFloat (tl.progress t)))
  | none => (.rest 0, 0)

/-- The middle of the rest on key `k`, in seconds from the start of the cycle (the time of a still
of that key); `0` if the timeline has no rest on key `k`. -/
def restTime (k : Nat) : Rat :=
  match tl.segments.find? (·.kind = .rest k) with
  | some s => s.start + s.dur / 2
  | none => 0

end Timeline

end PILean.Anim
