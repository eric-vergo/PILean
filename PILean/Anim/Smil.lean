/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Anim.Animation
import PILean.Anim.Timeline

/-!
# SMIL animations on a timeline

Builders of SMIL animation elements (`Svg.Node`s) that follow a `Timeline`: a value for each key
frame, held during the rests, eased during the moves, and carried round the loop by the seam.
Every element they build has the same timing attributes (`smilTiming`): one duration, the same
key times and `begin="0s"`, repeated indefinitely, so all the animations of a document run on one
clock. Under a crossfade the motion layer fades in at the start of the cycle and out at its end
(`seamOpacity`), so the jump from the last key back to the first, where SMIL starts the next
repetition, happens while nothing is visible; under a cut the picture jumps there.

The values are written at the segment boundaries: the value of the key that a rest shows, at both
of its ends; the values before and after a step, at the ends of its move. Each interval between two
boundaries is interpolated with its own spline (`calcMode="spline"`, `keySplines`): the pacing's
easing for a move, the identity `0 0 1 1` otherwise, so a rest repeats a value and nothing moves.

**The invariant.** These builders write no static `transform` attribute. A transform appears only
as the animated value of an `animateTransform`, which `group` puts as the only animation inside a
`g` with no attributes. Only `transform`, `opacity` and (for a morph between paths, inside the
`path`) `d` are animated: never a colour, `fill-opacity` or any other attribute that a page's
theme rules may restyle. `invariantProblem?` checks a tree against this.

**Boundaries that coincide.** A segment of length zero gives two equal key times in a row. Whether
every browser engine accepts that is the one choice kept in `Options.gap`: when it is above zero
(the default), boundaries closer than `gap` (a fraction of the cycle) are pushed apart to exactly
`gap`, so the key times strictly increase; when it is zero, equal key times are written as they are.

`valueAt` evaluates an animation element at a time exactly as SMIL defines it from its `values`,
`keyTimes`, `keySplines` and `calcMode`, for tests that compare what a document shows with what
was meant, without a browser.

## Main definitions

* `Smil.Options`, `Smil.times`, `Smil.smilTiming`.
* `Smil.animateRotate`, `Smil.animateTranslate`, `Smil.animateOpacity`, `Smil.animateD`,
  `Smil.seamOpacity`, `Smil.group`.
* `Smil.invariantProblem?`, `Smil.valueAt`.

## References

* SMIL 3.0, section 5.4 ("Animation function calculation"); SVG 1.1 (Second Edition), section 19
  ("Animation").
-/

namespace PILean.Anim

namespace Smil

open Svg Timeline

/-- How the timing of the animations is written. -/
structure Options where
  /-- The least distance between two consecutive key times, as a fraction of the cycle; `0` writes
  equal key times for a segment of length zero. -/
  gap : Rat := 1 / 10000
  deriving Inhabited, Repr

/-- The times `ts` (non-decreasing, from `0` to `1`) with consecutive ones at least `gap` apart: a
time too close to the one before it is moved later, and then one too close to the one after it
earlier, so the first stays `0` and the last `1`. A `gap` of zero leaves the times as they are; one
above `1 / (2 m)`, for `m` intervals, counts as `1 / (2 m)`. -/
def spread (gap : Rat) (ts : Array Rat) : Array Rat := Id.run do
  if gap ≤ 0 || ts.size < 2 then return ts
  let g := min gap (1 / (2 * (ts.size - 1 : Nat) : Rat))
  let mut fwd : Array Rat := #[]
  for t in ts do
    fwd := fwd.push (match fwd.back? with | some u => max t (u + g) | none => t)
  let mut out := fwd
  for j in [0:ts.size - 1] do
    let i := ts.size - 2 - j
    out := out.set! i (min out[i]! (out[i + 1]! - g))
  return out

/-- The key times the animations of a timeline write, as fractions of the cycle. -/
def times (tl : Timeline) (o : Options := {}) : Array Rat := spread o.gap tl.keyTimes

/-- A fraction of the cycle as text, to eight decimals. -/
def timeText (r : Rat) : String := fmtNum (Exact.toFloat r) 8

/-- An easing as the text of one `keySplines` entry, `x₁ y₁ x₂ y₂`. -/
def splineText (e : Easing) : String :=
  let (x₁, y₁, x₂, y₂) := e.controls
  s!"{fmtNum x₁ 4} {fmtNum y₁ 4} {fmtNum x₂ 4} {fmtNum y₂ 4}"

/-- The easing of the interval of a segment: its own for a move, the identity otherwise. -/
def segmentEasing (s : Segment) : Easing :=
  match s.kind with
  | .move _ => s.easing
  | _ => .linear

/-- The timing attributes every animation on the timeline carries: the cycle as `dur`, the key
times, one spline per segment, `calcMode="spline"`, indefinite repetition and `begin="0s"`. -/
def smilTiming (tl : Timeline) (o : Options := {}) : Array (String × String) :=
  #[("dur", fmtNum (Exact.toFloat tl.cycle) 4 ++ "s"),
    ("keyTimes", ";".intercalate ((times tl o).map timeText).toList),
    ("keySplines", ";".intercalate (tl.segments.map (splineText ∘ segmentEasing)).toList),
    ("calcMode", "spline"), ("repeatCount", "indefinite"), ("begin", "0s")]

/-- The keys shown at the start and at the end of a segment of a timeline whose last key is
`last`. -/
def endKeys (last : Nat) : SegKind → Nat × Nat
  | .rest k => (k, k)
  | .move s => (s, s + 1)
  | .seamIn => (0, 0)
  | .seamOut => (last, last)

/-- The key shown at each boundary of the timeline: at the start of the first segment, then at the
end of each segment (one more than the segments). -/
def boundaryKeys (tl : Timeline) : Array Nat :=
  match tl.segments[0]? with
  | none => #[]
  | some s₀ =>
    let last := tl.keys - 1
    #[(endKeys last s₀.kind).1] ++ tl.segments.map fun s => (endKeys last s.kind).2

/-- An animation element `tag` with its own attributes `head`, the values `valueOf k` at the keys
of the boundaries, and the timeline's timing. -/
def animation (tag : String) (head : Array (String × String)) (tl : Timeline)
    (valueOf : Nat → String) (o : Options) : Node :=
  el tag (head ++ #[("values", ";".intercalate ((boundaryKeys tl).map valueOf).toList)] ++
    smilTiming tl o)

/-- A turn: the rotation by `angleAt k` degrees about `(cx, cy)` in key `k`, written as the values
`θ cx cy` of an `animateTransform` of type `rotate`. -/
def animateRotate (tl : Timeline) (angleAt : Nat → Float) (cx cy : Float) (o : Options := {}) :
    Node :=
  animation "animateTransform" #[("attributeName", "transform"), ("type", "rotate")] tl
    (fun k => s!"{fmtNum (angleAt k) 4} {fmtNum cx 3} {fmtNum cy 3}") o

/-- A slide: the translation by `offsetAt k` in key `k`, written as the values `dx dy` of an
`animateTransform` of type `translate`. -/
def animateTranslate (tl : Timeline) (offsetAt : Nat → Float × Float) (o : Options := {}) : Node :=
  animation "animateTransform" #[("attributeName", "transform"), ("type", "translate")] tl
    (fun k => s!"{fmtNum (offsetAt k).1 3} {fmtNum (offsetAt k).2 3}") o

/-- An appearance or a disappearance: the opacity `opacityAt k` in key `k`. -/
def animateOpacity (tl : Timeline) (opacityAt : Nat → Float) (o : Options := {}) : Node :=
  animation "animate" #[("attributeName", "opacity")] tl (fun k => fmtNum (opacityAt k) 4) o

/-- A morph: the path data `pathAt k` in key `k`, or `none` when the paths cannot be interpolated
(they differ in their commands or in the number of their coordinates, `interpolable`). -/
def animateD (tl : Timeline) (pathAt : Nat → String) (o : Options := {}) : Option Node :=
  if interpolable ((boundaryKeys tl).map pathAt) then
    some (animation "animate" #[("attributeName", "d")] tl pathAt o)
  else none

/-- The opacity of the motion layer under a crossfade: `0` at the start of the fade in and at the
end of the fade out, `1` at every other boundary; `none` when the timeline has no seam segments
(a cut). -/
def seamOpacity (tl : Timeline) (o : Options := {}) : Option Node := do
  let s₀ ← tl.segments[0]?
  if !tl.segments.any (fun s => s.kind = .seamIn || s.kind = .seamOut) then none
  let first : Float := if s₀.kind = .seamIn then 0 else 1
  let ends := tl.segments.map fun s => if s.kind = .seamOut then (0 : Float) else 1
  return el "animate" (#[("attributeName", "opacity"),
    ("values", ";".intercalate ((#[first] ++ ends).map (fmtNum · 4)).toList)] ++ smilTiming tl o)

/-- The animation `anim` inside a `g` with no attributes, before the children it moves. -/
def group (anim : Node) (children : Array Node) : Node := el "g" #[] (#[anim] ++ children)

/-! ### The invariant -/

/-- The attributes these builders animate. -/
def animatedAttributes : List String := ["transform", "opacity", "d"]

/-- The value of the attribute `key` among `attrs`. -/
def attr? (attrs : Array (String × String)) (key : String) : Option String :=
  (attrs.find? (·.1 == key)).map (·.2)

/-- The first way the tree breaks the invariant (see the module docstring), at most `fuel` deep:
a static `transform` attribute; an animation element other than `animate` and `animateTransform`;
an animated attribute other than `transform`, `opacity` and `d`; an `animateTransform` of anything
but `transform`, or not the only one inside a `g` with no attributes; an `animate` of `transform`,
or of `d` outside a `path`. -/
def invariantProblem? : Nat → Node → Option String
  | 0, _ => some "the tree is too deep"
  | _, .text _ => none
  | fuel + 1, .element name attrs children => Id.run do
    if (attr? attrs "transform").isSome then return some s!"a static transform on <{name}>"
    let animations := children.filter fun
      | .element n _ _ => n == "animateTransform" || n == "animate" || n == "set" ||
        n == "animateMotion" || n == "animateColor"
      | .text _ => false
    for c in animations do
      let .element n as _ := c | continue
      let some target := attr? as "attributeName"
        | return some s!"an <{n}> without attributeName"
      if !animatedAttributes.contains target then
        return some s!"an animation of {target}"
      if n == "animateTransform" then
        if target != "transform" then return some s!"an animateTransform of {target}"
        if name != "g" || !attrs.isEmpty then
          return some s!"an animateTransform inside <{name}> with attributes"
        if (animations.filter fun | .element m _ _ => m == "animateTransform" | _ => false).size > 1
        then return some "two animateTransform elements inside one g"
      else if n == "animate" then
        if target == "transform" then return some "an animate of transform"
        if target == "d" && name != "path" then return some s!"an animate of d inside <{name}>"
      else return some s!"the animation element <{n}>"
    for c in children do
      if let some p := invariantProblem? fuel c then return some p
    return none

/-! ### Evaluating an animation -/

/-- The numbers of a value, in order (path data, a list of coordinates, a single number). -/
def numbers (v : String) : Array Float :=
  (valuePieces v).filterMap fun (isNum, s) => if isNum then Raster.parseNumber? s else none

/-- A SMIL clock value in seconds (`2.5s`, `300ms`, `1.5min`, `1h`, or a number of seconds). -/
def clock? (s : String) : Option Float :=
  let s := s.trimAscii.toString
  let unit := [("ms", 0.001), ("min", 60), ("h", 3600), ("s", 1)].find? (s.endsWith ·.1)
  match unit with
  | some (u, f) => (Raster.parseNumber? (s.dropEnd u.length).toString).map (· * f)
  | none => Raster.parseNumber? s

/-- The entries of a list separated by `;`, trimmed, without empty ones. -/
def entries (s : String) : Array String :=
  ((s.splitOn ";").map (·.trimAscii.toString) |>.filter (!·.isEmpty)).toArray

/-- The value of the animation element `n` at the time `t` (in seconds from its begin, `0 ≤ t`) as
its numbers, as SMIL computes it with the element repeated indefinitely: the time within the
repetition as a fraction of `dur`; for `calcMode` `discrete` the value of the last key time at or
before it; for `linear` and `spline` the interval of key times that contains it, the fraction of
that interval passed (through the interval's `keySplines` entry for `spline`) and the values at
its ends interpolated number by number. Without `keyTimes` the values are evenly spaced. `none`
for anything malformed (counts that do not agree, values with different numbers of numbers, no
positive duration, a negative time, a `calcMode` other than these three). -/
def valueAt (n : Node) (t : Float) : Option (Array Float) := do
  let .element _ attrs _ := n | none
  let values := (entries ((attr? attrs "values").getD "")).map numbers
  let m := values.size
  if m == 0 || t < 0 then none
  let dur ← clock? ((attr? attrs "dur").getD "")
  if !(dur > 0) then none
  let mode := (attr? attrs "calcMode").getD "linear"
  let kts ← match attr? attrs "keyTimes" with
    | some s => (entries s).mapM Raster.parseNumber?
    | none =>
      if mode == "discrete" then some ((Array.range m).map fun i => i.toFloat / m.toFloat)
      else some ((Array.range m).map fun i => i.toFloat / (max 1 (m - 1)).toFloat)
  if kts.size != m then none
  let u := t / dur - (t / dur).floor
  let last := ((Array.range m).filter fun i => kts[i]! ≤ u).back?.getD 0
  if mode == "discrete" then return values[last]!
  if mode != "linear" && mode != "spline" then none
  if m == 1 then return values[0]!
  let i := min last (m - 2)
  let span := kts[i + 1]! - kts[i]!
  let x := if span > 0 then (u - kts[i]!) / span else 1
  let sp := (entries ((attr? attrs "keySplines").getD "")).map numbers
  let f ← if mode == "linear" then some x
    else match sp[i]? with
      | some #[x₁, y₁, x₂, y₂] =>
        if sp.size + 1 == m then some ((Easing.spline x₁ y₁ x₂ y₂).eval x) else none
      | _ => none
  let a := values[i]!
  let b := values[i + 1]!
  if a.size != b.size then none
  return (a.zip b).map fun (p, q) => p + (q - p) * f

end Smil

end PILean.Anim
