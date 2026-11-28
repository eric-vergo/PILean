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
clock (`clockProblem?` checks a document for that). Under a crossfade the motion layer fades in
at the start of the cycle and out at its end (`seamOpacity`), so the jump from the last key back
to the first, where SMIL starts the next repetition, happens while nothing is visible; under a cut
the picture jumps there.

An element is first a `Track`: its values at the segment boundaries, its key times (`times`) and
one easing per segment (the segment's own: the step's easing for a move, the identity `0 0 1 1`
for a rest or a fade, so a rest repeats a value and nothing moves). `Track.toNode` writes it;
`PILean/Anim/SmilProofs.lean` proves what the arrays hold. A builder gives `none` for a timeline
whose cycle is not longer than zero, which SMIL cannot express.

**The invariant.** These builders write no static `transform` attribute. A transform appears only
as the animated value of an `animateTransform`, which `group` puts as the only animation inside a
`g` with no attributes. Only `transform`, `opacity` and (for a morph between paths, inside the
`path`) `d` are animated: never a colour, `fill-opacity` or any other attribute that a page's
theme rules may restyle. `invariantProblem?` checks a tree against this.

**Turns that follow each other.** An actor turned in several steps sits in one group per turn,
the earliest turn innermost: each centre is then a point of the page, and the later turns carry
the result of the earlier ones (`nest`). A label that stays upright turns back about its anchor by
the whole angle so far (`uprightAngles`), inside the innermost group.

**Boundaries that coincide.** A segment of length zero gives two equal key times in a row.
`Options.gap` keeps consecutive key times apart: when it is above zero (the default), a time too
close to the one before it is moved later and then one too close to the one after it earlier, so
that the key times increase strictly from `0` to `1`; when it is zero, the key times are written
as they are.

`valueAt` evaluates an animation element at a time as SMIL defines it, and refuses what a browser
would refuse, for tests that compare what a document shows with what was meant, without a
browser.

## Main definitions

* `Smil.Options`, `Smil.times`, `Smil.smilTiming`, `Smil.Track`.
* `Smil.animateRotate`, `Smil.animateTranslate`, `Smil.animateOpacity`, `Smil.animateD`,
  `Smil.seamOpacity`, `Smil.group`, `Smil.nest`, `Smil.turnAngles`, `Smil.uprightAngles`.
* `Smil.invariantProblem?`, `Smil.clockProblem?`, `Smil.valueAt`.

## References

* SMIL 3.0, section 5.4 ("Animation function calculation"); SVG 1.1 (Second Edition), section 19
  ("Animation").
-/

namespace PILean.Anim

namespace Smil

open Svg Timeline

/-! ### Key times -/

/-- How the timing of the animations is written. -/
structure Options where
  /-- The least distance between two consecutive key times, as a fraction of the cycle (raised to
  `minGap` when it is above zero, and lowered to `1 / (2 m)` for `m` intervals); `0` writes equal
  key times for a segment of length zero. -/
  gap : Rat := 1 / 10000
  deriving Inhabited, Repr

/-- The least gap above zero: `10⁻⁷` of the cycle, ten units of the eighth decimal that key times
are written to, so that two consecutive key times never print alike. -/
def minGap : Rat := 1 / 10000000

/-- The gap used for `m` intervals: `0` for a gap of at most zero, otherwise the gap raised to
`minGap` and lowered to `1 / (2 m)`, so that `m` gaps take at most half of the cycle. -/
def effectiveGap (gap : Rat) (m : Nat) : Rat :=
  if gap ≤ 0 then 0 else min (max gap minGap) (1 / (2 * m))

/-- The times after `prev`, each at least `g` after the one before it, except the last, which is
kept. -/
def pushUp (g : Rat) : Rat → List Rat → List Rat
  | _, [] => []
  | _, [x] => [x]
  | prev, x :: y :: r => max x (prev + g) :: pushUp g (max x (prev + g)) (y :: r)

/-- The times, each at most the one after it minus `g`; the last is kept. -/
def pullDown (g : Rat) : List Rat → List Rat
  | [] => []
  | x :: rest =>
    match pullDown g rest with
    | [] => [x]
    | y :: r => min x (y - g) :: y :: r

/-- The times with consecutive ones at least `g` apart: those too close to the one before them
moved later (all but the first and the last), then those too close to the one after them moved
earlier (all but the last). From non-decreasing times from `0` to `1`, with `m g ≤ 1` for `m`
intervals, this gives times from `0` to `1` each at least `g` after the one before it
(`PILean/Anim/SmilProofs.lean`); a time moves only when a neighbour is closer than `g`. -/
def spreadList (g : Rat) : List Rat → List Rat
  | [] => []
  | t :: ts => pullDown g (t :: pushUp g t ts)

/-- The key times the animations of a timeline write, as fractions of the cycle: the timeline's
key times, spread with the effective gap. -/
def times (tl : Timeline) (o : Options := {}) : Array Rat :=
  (spreadList (effectiveGap o.gap (tl.keyTimes.size - 1)) tl.keyTimes.toList).toArray

/-- A fraction of the cycle as text, to eight decimals. -/
def timeText (r : Rat) : String := fmtNum (Exact.toFloat r) 8

/-- A cycle as a clock value, in seconds to six decimals (`fmtNum`): a function of the exact cycle,
so every element of one timeline, and of any timeline with the same cycle, writes the same text. A
cycle that is not a whole number of microseconds is written within half a microsecond, which
changes the speed of the whole picture by that fraction and nothing else, because every element
uses the same text. -/
def durText (cycle : Rat) : String := fmtNum (Exact.toFloat cycle) 6 ++ "s"

/-- An easing as the text of one `keySplines` entry, `x₁ y₁ x₂ y₂`, each to six decimals (the part
of an easing in a divided step, `Easing.part`, needs them: measured over thirteen curves on every
part between two hundredths of a step, at six a turn stays within `2.85e-6` of its change from its
eased angle, at four it would be off by up to about `7.5e-5`; `docs/DESIGN.md`, "Timelines and
SMIL motions"). -/
def splineText (e : Easing) : String :=
  let (x₁, y₁, x₂, y₂) := e.controls
  s!"{fmtNum x₁ 6} {fmtNum y₁ 6} {fmtNum x₂ 6} {fmtNum y₂ 6}"

/-- The timing attributes of an element: the cycle as `dur`, the key times, one spline per
interval, `calcMode="spline"`, indefinite repetition and `begin="0s"`. -/
def timing (times : Array Rat) (splines : Array Easing) (cycle : Rat) : Array (String × String) :=
  #[("dur", durText cycle), ("keyTimes", ";".intercalate (times.map timeText).toList),
    ("keySplines", ";".intercalate (splines.map splineText).toList),
    ("calcMode", "spline"), ("repeatCount", "indefinite"), ("begin", "0s")]

/-- The timing attributes every animation on the timeline carries. -/
def smilTiming (tl : Timeline) (o : Options := {}) : Array (String × String) :=
  timing (times tl o) (tl.segments.map (·.easing)) tl.cycle

/-! ### Tracks -/

/-- An animation element before it is written: its name, its own attributes, its values at the
boundaries, its key times and the easing of each interval, and the cycle. -/
structure Track where
  /-- The element's name. -/
  tag : String
  /-- Its own attributes (`attributeName`, `type`). -/
  head : Array (String × String)
  /-- The values at the boundaries. -/
  values : Array String
  /-- The key times. -/
  times : Array Rat
  /-- The easing of each interval. -/
  splines : Array Easing
  /-- The cycle, in seconds. -/
  cycle : Rat
  deriving Inhabited, Repr

/-- The track as an element. -/
def Track.toNode (t : Track) : Node :=
  el t.tag (t.head ++ #[("values", ";".intercalate t.values.toList)] ++
    timing t.times t.splines t.cycle)

/-- The track of the element `tag` with its attributes `head` and the values `values` on the
timeline. -/
def track (tag : String) (head : Array (String × String)) (tl : Timeline) (values : Array String)
    (o : Options) : Track :=
  { tag, head, values, times := times tl o, splines := tl.segments.map (·.easing),
    cycle := tl.cycle }

/-- The track as an element, or `none` when the cycle is not longer than zero, when there are no
values, or when a value contains `;` (which would split it in two). -/
def emit (t : Track) : Option Node :=
  if t.cycle ≤ 0 || t.values.isEmpty || t.values.any (·.contains ';') then none
  else some t.toNode

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

/-- The values `valueOf k` at the keys of the boundaries. -/
def keyValues (tl : Timeline) (valueOf : Nat → String) : Array String :=
  (boundaryKeys tl).map valueOf

/-- The opacity of the motion layer at each boundary: `0` at the start of a fade in and at the end
of a fade out, `1` elsewhere. -/
def seamLevels (tl : Timeline) : Array Float :=
  match tl.segments[0]? with
  | none => #[]
  | some s₀ =>
    #[if s₀.kind = .seamIn then 0 else 1] ++
      tl.segments.map fun s => if s.kind = .seamOut then (0 : Float) else 1

/-! ### Builders -/

/-- The track of a turn: the rotation by `angleAt k` degrees about `(cx, cy)` in key `k`. -/
def rotateTrack (tl : Timeline) (angleAt : Nat → Float) (cx cy : Float) (o : Options := {}) :
    Track :=
  track "animateTransform" #[("attributeName", "transform"), ("type", "rotate")] tl
    (keyValues tl fun k => s!"{fmtNum (angleAt k) 4} {fmtNum cx 3} {fmtNum cy 3}") o

/-- A turn: the rotation by `angleAt k` degrees about `(cx, cy)` in key `k`, written as the values
`θ cx cy` of an `animateTransform` of type `rotate`. Put it in its own group (`group`); for turns
about several centres, see `nest`. -/
def animateRotate (tl : Timeline) (angleAt : Nat → Float) (cx cy : Float) (o : Options := {}) :
    Option Node :=
  emit (rotateTrack tl angleAt cx cy o)

/-- The track of a slide: the translation by `offsetAt k` in key `k`. -/
def translateTrack (tl : Timeline) (offsetAt : Nat → Float × Float) (o : Options := {}) : Track :=
  track "animateTransform" #[("attributeName", "transform"), ("type", "translate")] tl
    (keyValues tl fun k => s!"{fmtNum (offsetAt k).1 3} {fmtNum (offsetAt k).2 3}") o

/-- A slide: the translation by `offsetAt k` in key `k`, written as the values `dx dy` of an
`animateTransform` of type `translate`. -/
def animateTranslate (tl : Timeline) (offsetAt : Nat → Float × Float) (o : Options := {}) :
    Option Node :=
  emit (translateTrack tl offsetAt o)

/-- The track of an opacity: `opacityAt k` in key `k`. -/
def opacityTrack (tl : Timeline) (opacityAt : Nat → Float) (o : Options := {}) : Track :=
  track "animate" #[("attributeName", "opacity")] tl (keyValues tl fun k => fmtNum (opacityAt k) 4)
    o

/-- An appearance or a disappearance: the opacity `opacityAt k` in key `k`. -/
def animateOpacity (tl : Timeline) (opacityAt : Nat → Float) (o : Options := {}) : Option Node :=
  emit (opacityTrack tl opacityAt o)

/-- The track of a morph: the path data `pathAt k` in key `k`. -/
def morphTrack (tl : Timeline) (pathAt : Nat → String) (o : Options := {}) : Track :=
  track "animate" #[("attributeName", "d")] tl (keyValues tl pathAt) o

/-- A morph: the path data `pathAt k` in key `k`, or `none` when the paths cannot be interpolated
(they differ in their commands or in the number of their coordinates, `interpolable`). -/
def animateD (tl : Timeline) (pathAt : Nat → String) (o : Options := {}) : Option Node :=
  if interpolable (keyValues tl pathAt) then emit (morphTrack tl pathAt o) else none

/-- The track of the motion layer's opacity (`seamLevels`). -/
def seamTrack (tl : Timeline) (o : Options := {}) : Track :=
  track "animate" #[("attributeName", "opacity")] tl ((seamLevels tl).map (fmtNum · 4)) o

/-- The opacity of the motion layer under a crossfade: `0` at the start of the fade in and at the
end of the fade out, `1` at every other boundary; `none` when the timeline has no fades (a cut). -/
def seamOpacity (tl : Timeline) (o : Options := {}) : Option Node :=
  if tl.segments.any (fun s => s.kind = .seamIn || s.kind = .seamOut) then emit (seamTrack tl o)
  else none

/-- The animation `anim` inside a `g` with no attributes, before the children it moves. An
`animateTransform` turns its own group's content; for an actor turned in several steps, the
earliest turn is the innermost group (`nest`). -/
def group (anim : Node) (children : Array Node) : Node := el "g" #[] (#[anim] ++ children)

/-- The angle in degrees after each key of an actor that turns by `turns[j]` of a full turn in
step `j` (`0` in the steps where it does not turn; missing steps count as `0`): the exact sum of
the turns before key `k`, times 360, converted to `Float`. -/
def turnAngles (turns : Array Rat) (k : Nat) : Float :=
  Exact.toFloat (360 * (turns.toList.take k).foldr (· + ·) 0)

/-- The angle of a counter-rotation that keeps a label upright: minus `turnAngles turns k`, the
whole angle the label's groups have turned by key `k`. Turn the label about its anchor by it,
inside the innermost group. -/
def uprightAngles (turns : Array Rat) (k : Nat) : Float :=
  Exact.toFloat (-(360 * (turns.toList.take k).foldr (· + ·) 0))

/-- The angles of a single turn by `q` of a full turn in step `j`: `0` up to key `j`, `360 q`
after it. -/
def stepAngles (j : Nat) (q : Rat) (k : Nat) : Float :=
  if k ≤ j then 0 else Exact.toFloat (360 * q)

/-- The children turned by `turns` in order of time, each a centre and its angles at the keys: one
group per turn, the earliest innermost, so that each centre is a point of the page and each turn
moves the result of the turns before it. `none` when a turn cannot be written (`animateRotate`). -/
def nest (tl : Timeline) (turns : List (Float × Float × (Nat → Float))) (children : Array Node)
    (o : Options := {}) : Option Node :=
  turns.foldlM (init := el "g" #[] children) fun inner (cx, cy, angleAt) =>
    (animateRotate tl angleAt cx cy o).map fun a => group a #[inner]

/-! ### The invariant and the clock -/

/-- The attributes these builders animate. -/
def animatedAttributes : List String := ["transform", "opacity", "d"]

/-- The value of the attribute `key` among `attrs`. -/
def attr? (attrs : Array (String × String)) (key : String) : Option String :=
  (attrs.find? (·.1 == key)).map (·.2)

/-- Whether an element is an animation element. -/
def isAnimation (name : String) : Bool :=
  name == "animateTransform" || name == "animate" || name == "set" || name == "animateMotion" ||
    name == "animateColor"

/-- The first way the tree breaks the invariant (see the module docstring), at most `fuel` deep:
a static `transform`, `gradientTransform` or `patternTransform` attribute, or a `style` attribute
that mentions `transform`; an `additive` or `accumulate` attribute; an animation element other than
`animate` and `animateTransform`; an animated attribute other than `transform`, `opacity` and `d`;
an `animateTransform` of anything but `transform`, or not the only one inside a `g` with no
attributes; an `animate` of `transform`, or of `d` outside a `path`. -/
def invariantProblem? : Nat → Node → Option String
  | 0, _ => some "the tree is too deep"
  | _, .text _ => none
  | fuel + 1, .element name attrs children => Id.run do
    for (k, v) in attrs do
      if k == "transform" || k == "gradientTransform" || k == "patternTransform" then
        return some s!"a static {k} on <{name}>"
      if k == "style" && (v.toLower.splitOn "transform").length > 1 then
        return some s!"a style with a transform on <{name}>"
      if k == "additive" || k == "accumulate" then return some s!"{k} on <{name}>"
    let animations := children.filter fun
      | .element n _ _ => isAnimation n
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

/-- The attributes that put an animation on its clock. -/
def clockAttributes : List String := ["dur", "begin", "keyTimes", "calcMode", "repeatCount"]

/-- The clock attributes of every animation element of the tree, in document order, at most `fuel`
deep. -/
def clocks : Nat → Node → Array (List (Option String))
  | 0, _ => #[]
  | _, .text _ => #[]
  | fuel + 1, .element name attrs children =>
    let own := if isAnimation name then #[clockAttributes.map (attr? attrs ·)] else #[]
    children.foldl (fun acc c => acc ++ clocks fuel c) own

/-- The first reason the animations of the tree (at most 256 deep) do not all run on one clock:
an animation element without `dur`, `begin`, `keyTimes`, `calcMode` or `repeatCount`, or two that
differ in one of them. -/
def clockProblem? (root : Node) : Option String :=
  let cs := clocks 256 root
  if cs.any (·.any (·.isNone)) then
    some "an animation without dur, begin, keyTimes, calcMode or repeatCount"
  else match cs.toList with
    | [] => none
    | c :: rest =>
      if rest.all (· == c) then none
      else some "two animations on different clocks (dur, begin, keyTimes, calcMode or repeatCount)"

/-! ### Evaluating an animation -/

/-- The numbers of a value, in order (path data, a list of coordinates, a single number). -/
def numbers (v : String) : Array Float :=
  (valuePieces v).filterMap fun (isNum, s) => if isNum then Raster.parseNumber? s else none

/-- A plain decimal number (digits with at most one `.`, at least one digit), or `none`. -/
def decimal? (s : String) : Option Float :=
  let cs := s.toList
  if cs.any (fun c => !(c.isDigit || c == '.')) || cs.count '.' > 1 || !cs.any Char.isDigit then
    none
  else Raster.parseNumber? s

/-- A SMIL clock value in seconds: a plain decimal number followed by `h`, `min`, `s`, `ms` or
nothing (seconds), or `none`. -/
def clock? (s : String) : Option Float :=
  let s := s.trimAscii.toString
  match [("ms", 0.001), ("min", 60), ("h", 3600), ("s", 1)].find? (s.endsWith ·.1) with
  | some (u, f) => (decimal? (s.dropEnd u.length).toString).map (· * f)
  | none => decimal? s

/-- The entries of a list separated by `;`, trimmed, without empty ones. -/
def entries (s : String) : Array String :=
  ((s.splitOn ";").map (·.trimAscii.toString) |>.filter (!·.isEmpty)).toArray

/-- Whether the numbers do not decrease. -/
def sorted (xs : Array Float) : Bool := (xs.toList.zip xs.toList.tail).all fun (a, b) => a ≤ b

/-- The value of the animation element `n` at the time `t` (in seconds from its begin, `0 ≤ t`) as
its numbers, as SMIL computes it with the element repeated indefinitely: the time within the
repetition as a fraction of `dur`; for `calcMode` `discrete` the value of the last key time at or
before it; for `linear` and `spline` the interval of key times that contains it, the fraction of
that interval passed (through the interval's `keySplines` entry for `spline`) and the values at
its ends interpolated number by number. Without `keyTimes` the values are evenly spaced.

It gives `none` for what SMIL makes an error, so that a value here means a browser animates the
element: `dur` not a clock value longer than zero; key times that do not start at `0`, decrease,
or (for `linear` and `spline`) do not end at `1`, or whose count is not that of the values; for
`spline`, a count of `keySplines` other than one less than the values, or an entry that is not four
numbers in `[0, 1]`; values with different numbers of numbers; a negative time; a `calcMode` other
than these three. -/
def valueAt (n : Node) (t : Float) : Option (Array Float) := do
  let .element _ attrs _ := n | none
  let values := (entries ((attr? attrs "values").getD "")).map numbers
  let m := values.size
  let first ← values[0]?
  if t < 0 || values.any (·.size != first.size) then none
  let dur ← clock? ((attr? attrs "dur").getD "")
  if !(dur > 0) then none
  let mode := (attr? attrs "calcMode").getD "linear"
  if mode != "discrete" && mode != "linear" && mode != "spline" then none
  let kts ← match attr? attrs "keyTimes" with
    | some s => (entries s).mapM decimal?
    | none =>
      if mode == "discrete" then some ((Array.range m).map fun i => i.toFloat / m.toFloat)
      else some ((Array.range m).map fun i => i.toFloat / (max 1 (m - 1)).toFloat)
  if kts.size != m || kts[0]? != some 0 || !sorted kts then none
  if mode != "discrete" && kts.back? != some 1 then none
  let splines := (entries ((attr? attrs "keySplines").getD "")).map numbers
  if mode == "spline" && (splines.size + 1 != m ||
      splines.any fun c => c.size != 4 || c.any fun v => v < 0 || v > 1) then none
  let u := t / dur - (t / dur).floor
  let last := ((List.range m).filter fun i => kts.getD i 2 ≤ u).getLast?.getD 0
  if mode == "discrete" then return values.getD last first
  if m == 1 then return first
  let i := min last (m - 2)
  let lo := kts.getD i 0
  let span := kts.getD (i + 1) 1 - lo
  let x := if span > 0 then (u - lo) / span else 1
  let f ← if mode == "linear" then some x
    else match splines[i]? with
      | some #[x₁, y₁, x₂, y₂] => some ((Easing.spline x₁ y₁ x₂ y₂).eval x)
      | _ => none
  let a := values.getD i first
  let b := values.getD (i + 1) first
  return (a.zip b).map fun (p, q) => p + (q - p) * f

end Smil

end PILean.Anim
