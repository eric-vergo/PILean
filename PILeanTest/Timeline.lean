/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean

/-!
# Timeline and SMIL tests

`Easing.eval` against cubic Bézier values computed independently (bisection in 60-digit decimal
arithmetic), its inverse consistency and monotonicity; timelines of 1, 2 and 13 key frames under
both seams and with steps in which nothing moves; the SMIL attributes the builders write (counts of
values, key times and splines, the spreading of equal key times); `Smil.valueAt` on the builders'
output against the eased values the timeline gives; the invariant of the builders (no static
transform, only `transform`, `opacity` and `d` animated) with planted breaks; and the inertness of
everything the builders write.
-/

namespace PILeanTest.TimelineChecks

open PILean PILean.Anim PILean.Svg

/-- Whether `a` and `b` differ by less than `tol`. -/
def near (a b : Float) (tol : Float) : Bool := (a - b).abs < tol

/-! ### Easing -/

/-- The curves of the easing checks, with their values at `0.1, 0.25, 0.5, 0.75, 0.9` computed by
bisection in 60-digit decimal arithmetic. -/
def curves : Array (String × Easing × Array Float) :=
  #[("standard", .standard, #[0.01972245354831120, 0.12916193104731981, 0.5,
      0.87083806895268019, 0.98027754645168880]),
    ("CSS ease", .spline 0.25 0.1 0.25 1, #[0.09479630571604325, 0.40851059135539587,
      0.80240338758485699, 0.96045897834897408, 0.99431647748455637]),
    ("0 1 0 1", .spline 0 1 0 1, #[0.84614624307426855, 0.94933078586616014,
      0.99122000310998946, 0.99923545257723948, 0.99995889845841629]),
    ("1 0 1 0", .spline 1 0 1 0, #[0.00004110154158371, 0.00076454742276052,
      0.00877999689001054, 0.05066921413383986, 0.15385375692573145]),
    ("1 0 0 1", .spline 1 0 0 1, #[0.00376167495808317, 0.02972460551192520, 0.5,
      0.97027539448807480, 0.99623832504191683])]

/-- The progresses at which `curves` gives the values. -/
def probes : Array Float := #[0.1, 0.25, 0.5, 0.75, 0.9]

/-- The easing checks. -/
def easingChecks : Array (String × Bool) := Id.run do
  let mut r : Array (String × Bool) := #[]
  for (name, e, expected) in curves do
    -- `1 0 0 1` is flat in its first coordinate at `0.5`: there the value is only as precise as
    -- the cube root of the rounding of `x`, so it is checked more loosely
    let ok := (probes.zip expected).all fun (x, y) =>
      near (e.eval x) y (if name == "1 0 0 1" && x == 0.5 then 1e-4 else 1e-7)
    r := r.push (s!"easing: {name} matches the reference values within 1e-7", ok)
    let (x₁, _, x₂, _) := e.controls
    let grid := (List.range 1001).map fun i => i.toFloat / 1000
    r := r.push (s!"easing: {name} is solved for its parameter within 1e-12",
      grid.all fun s =>
        let x := Easing.bezier x₁ x₂ s
        near (Easing.bezier x₁ x₂ (e.solve x)) x 1e-12)
    r := r.push (s!"easing: {name} does not decrease and stays in [0, 1]",
      (grid.zip grid.tail).all fun (a, b) =>
        e.eval a ≤ e.eval b && 0 ≤ e.eval a && e.eval b ≤ 1)
    r := r.push (s!"easing: {name} gives 0 at 0 and 1 at 1, and 0 and 1 beyond",
      e.eval 0 == 0 && e.eval 1 == 1 && e.eval (-3) == 0 && e.eval 7 == 1 &&
        e.eval (0 / 0) == 0)
  for (name, e) in [("standard", Easing.standard), ("CSS ease", .spline 0.25 0.1 0.25 1)] do
    let (x₁, y₁, x₂, y₂) := e.controls
    r := r.push (s!"easing: {name} at the first coordinate of a point of the curve gives its \
        second coordinate within 1e-7",
      (List.range 101).all fun i =>
        let s := i.toFloat / 100
        near (e.eval (Easing.bezier x₁ x₂ s)) (Easing.bezier y₁ y₂ s) 1e-7)
  r := r.push ("easing: linear is the identity",
    probes.all fun x => Easing.linear.eval x == x)
  r := r.push ("easing: control values outside [0, 1] are clamped",
    (Easing.spline (-1) 2 1.5 (-0.5)).controls == (0, 1, 1, 0) &&
      (Easing.spline (0 / 0) 0.5 0.5 0.5).controls == (0, 0.5, 0.5, 0.5))
  return r

/-! ### Timelines -/

/-- `n` turns. -/
def turns (n : Nat) : Array Step := Array.replicate n ({} : Pacing).turnStep

/-- Twelve steps of which four do not move. -/
def mixed : Array Step :=
  #["m", "i", "m", "m", "i", "m", "m", "i", "i", "m", "m", "m"].map fun c =>
    if c == "m" then ({} : Pacing).turnStep else ({} : Pacing).idleStep

/-- A pacing with a cut. -/
def cutPacing : Pacing := { seam := .cut }

/-- The kinds of the segments. -/
def kinds (tl : Timeline) : List SegKind := tl.segments.toList.map (·.kind)

/-- The kinds of the step segments of `n` steps. -/
def stepKinds (n : Nat) : List SegKind := (List.range n).flatMap fun j => [.move j, .rest (j + 1)]

/-- Whether the segments tile the cycle and the key times are well formed. -/
def wellFormed (tl : Timeline) : Bool :=
  let segs := tl.segments
  let kt := tl.keyTimes
  segs.size > 0 && (segs[0]?.map (·.start)) == some 0 &&
    (List.range (segs.size - 1)).all (fun i => segs[i + 1]!.start == segs[i]!.stop) &&
    (segs.back?.map (·.stop)) == some tl.cycle && segs.all (0 ≤ ·.dur) &&
    kt.size == segs.size + 1 && kt[0]? == some 0 && kt.back? == some 1 &&
    (List.range (kt.size - 1)).all fun i => kt[i]! ≤ kt[i + 1]!

/-- The timeline checks. -/
def timelineChecks : Array (String × Bool) := Id.run do
  let p : Pacing := {}
  let mut r : Array (String × Bool) := #[]
  for (steps, name) in [(turns 0, "1 key"), (turns 1, "2 keys"), (turns 12, "13 keys"),
      (mixed, "13 keys with steps that do not move")] do
    let n := steps.size
    let cf := Timeline.build steps p
    let cut := Timeline.build steps cutPacing
    r := r.push (s!"timeline: {name}, crossfade: 2n + 1 segments in order, tiling the cycle",
      cf.keys == n + 1 && cf.segments.size == 2 * (n + 1) + 1 && wellFormed cf &&
        kinds cf == .seamIn :: .rest 0 :: stepKinds n ++ [.seamOut])
    r := r.push (s!"timeline: {name}, cut: 2n - 1 segments in order, tiling the cycle",
      cut.keys == n + 1 && cut.segments.size == 2 * (n + 1) - 1 && wellFormed cut &&
        kinds cut == .rest 0 :: stepKinds n)
    r := r.push (s!"timeline: {name}: the crossfade adds its length to the cycle",
      cf.cycle == cut.cycle + 0.4)
    r := r.push (s!"timeline: {name}: every key's still is in the middle of its rest",
      (List.range (n + 1)).all fun k =>
        let t := cf.restTime k
        cf.locate t == (.rest k, 0.5) && cut.locate (cut.restTime k) == (.rest k, 0.5))
    r := r.push (s!"timeline: {name}: each move has its step's duration and easing",
      (List.range n).all fun j => match cf.segments.find? (·.kind == .move j), steps[j]? with
        | some s, some st => s.easing == st.easing && s.dur == st.dur &&
          st.easing == (if st.kind == .move then p.easing else .linear)
        | _, _ => false)
  -- exact lengths
  r := r.push ("timeline: 1 key: the cycle is the first rest (and the crossfade)",
    (Timeline.build #[] cutPacing).cycle == 1.2 && (Timeline.build #[] p).cycle == 1.6)
  r := r.push ("timeline: 2 keys under a cut: 1.2 + 1 + 1.8",
    (Timeline.build (turns 1) cutPacing).cycle == 4)
  r := r.push ("timeline: 13 keys of turns: 1.2 + 12 turns + 11 holds + 1.8 + 0.4",
    (Timeline.build (turns 12) p).cycle == 1.2 + 12 + 11 * 0.6 + 1.8 + 0.4)
  r := r.push ("timeline: mixed steps: 8 turns and 4 idle steps",
    (Timeline.build mixed p).cycle == 1.2 + 8 + 4 * 0.9 + 11 * 0.6 + 1.8 + 0.4)
  -- times outside the cycle, the middle of a move
  let tl := Timeline.build (turns 2) cutPacing
  r := r.push ("timeline: times are brought into the cycle",
    tl.cycle == 5.6 && tl.wrap 6 == 0.4 && tl.wrap (-1) == 4.6 && tl.wrap 5.6 == 0 &&
      tl.segmentAt (-1) == tl.segmentAt 4.6 && tl.locate 12.6 == tl.locate 1.4)
  r := r.push ("timeline: the middle of a turn is half way under the symmetric easing",
    tl.locate 1.7 == (.move 0, 0.5) && tl.progress 1.7 == 1 / 2)
  r := r.push ("timeline: a boundary belongs to the segment it starts",
    tl.locate 1.2 == (.move 0, 0) && tl.segmentAt 0 == 0 && tl.segmentAt 2.2 == 2)
  -- negative and zero durations
  let negPacing : Pacing := { seam := .cut, hold := -2, lastHold := 1 }
  let neg := Timeline.build #[{ dur := -1 }] negPacing
  r := r.push ("timeline: a negative duration counts as zero",
    neg.segments.all (0 ≤ ·.dur) && neg.cycle == 2.2 && wellFormed neg)
  let still : Pacing := { firstHold := 0, lastHold := 0, hold := 0, turn := 0, seam := .cut }
  let zero := Timeline.build (Array.replicate 2 still.turnStep) still
  r := r.push ("timeline: a cycle of length zero has every key time 0",
    zero.cycle == 0 && zero.keyTimes.all (· == 0) && zero.wrap 3 == 0 &&
      zero.locate 1 == (.rest 0, 0))
  r := r.push ("timeline: a rest that is missing has the time 0",
    tl.restTime 9 == 0)
  -- every duration and easing, with steps of their own durations and easings
  let custom : Array Step := #[{ dur := 0.7, easing := .spline 0.1 0.2 0.3 0.4 },
    { kind := .idle, dur := 1.3, easing := .linear }, { dur := 0.25, easing := .linear }]
  let cp : Pacing := { hold := 0.5, firstHold := 2, lastHold := 3, seam := .crossfade 0.6 }
  let ct := Timeline.build custom cp
  r := r.push ("timeline: every segment has the duration and easing of its kind",
    (ct.segments.map fun s => (s.kind, s.dur)).toList ==
        [(.seamIn, 0.3), (.rest 0, 2), (.move 0, 0.7), (.rest 1, 0.5), (.move 1, 1.3),
          (.rest 2, 0.5), (.move 2, 0.25), (.rest 3, 3), (.seamOut, 0.3)] &&
      (ct.segments.map (·.easing)).toList ==
        [.linear, .linear, .spline 0.1 0.2 0.3 0.4, .linear, .linear, .linear, .linear, .linear,
          .linear])
  let ep : Pacing := { easing := .spline 0.3 0 0.7 1 }
  r := r.push ("timeline: rests are not eased whatever the pacing's easing",
    (Timeline.build (Array.replicate 3 ep.turnStep) ep).segments.all fun s =>
      match s.kind with
      | .move _ => s.easing == .spline 0.3 0 0.7 1
      | _ => s.easing == .linear)
  return r

/-! ### SMIL attributes -/

/-- The value of an attribute of an element. -/
def attrOf (n : Node) (key : String) : String :=
  match n with
  | .element _ attrs _ => (Smil.attr? attrs key).getD ""
  | .text _ => ""

/-- The element, or an empty text when there is none. -/
def get (n : Option Node) : Node := n.getD (.text "")

/-- The number of entries of a list separated by `;`. -/
def count (s : String) : Nat := (Smil.entries s).size

/-- Whether an animation element has `n` values and key times and `n - 1` splines, each of four
numbers, and the shared timing. -/
def countsAgree (n : Nat) (a : Node) : Bool :=
  count (attrOf a "values") == n && count (attrOf a "keyTimes") == n &&
    count (attrOf a "keySplines") + 1 == n &&
    (Smil.entries (attrOf a "keySplines")).all (fun s => (Smil.numbers s).size == 4) &&
    attrOf a "calcMode" == "spline" && attrOf a "repeatCount" == "indefinite" &&
    attrOf a "begin" == "0s"

/-- A timeline whose key times are exact in a few decimals: a cycle of 10 seconds. -/
def decimalTimeline : Timeline :=
  Timeline.build (turns 3) { firstHold := 1.5, hold := 1, lastHold := 2.5, seam := .crossfade 1 }

/-- The angle of key `k` in the checks: a fifth of a turn per key. -/
def angleAt (k : Nat) : Float := 72 * k.toFloat

/-- A square path at `(10 k, 0)`. -/
def pathAt (k : Nat) : String := pathData (rect' (10 * k.toFloat) 0 20 20)
where
  /-- A rectangle as a path. -/
  rect' (x y w h : Float) : Path :=
    { cmds := #[.move ⟨x, y⟩, .line ⟨x + w, y⟩, .line ⟨x + w, y + h⟩, .line ⟨x, y + h⟩, .close] }

/-- The value the timeline gives at the time `t` for a quantity with the value `valueAt k` in key
`k`: held during rests and seams, eased between two keys during a move. -/
def expected (tl : Timeline) (valueAt : Nat → Float) (t : Rat) : Float :=
  match tl.locate t with
  | (.rest k, _) => valueAt k
  | (.move s, e) => valueAt s + (valueAt (s + 1) - valueAt s) * e
  | (.seamIn, _) => valueAt 0
  | (.seamOut, _) => valueAt (tl.keys - 1)

/-- Whether exact times start at `0`, end at `1` and are each at least `g` after the one before. -/
def spreadWell (g : Rat) (ts : List Rat) : Bool :=
  ts.head? == some 0 && ts.getLast? == some 1 && (ts.zip ts.tail).all fun (a, b) => a + g ≤ b

/-- Whether written key times start at `0`, end at `1` and increase strictly. -/
def writtenWell (s : String) : Bool :=
  let ts := (Smil.entries s).filterMap Smil.decimal?
  ts.size == count s && ts[0]? == some 0 && ts.back? == some 1 &&
    (ts.toList.zip ts.toList.tail).all fun (a, b) => a < b

/-- The SMIL checks. -/
def smilChecks : Array (String × Bool) := Id.run do
  let mut r : Array (String × Bool) := #[]
  for (steps, name) in [(turns 0, "1 key"), (turns 1, "2 keys"), (turns 12, "13 keys"),
      (mixed, "mixed steps")] do
    for (p, seam) in [(({} : Pacing), "crossfade"), (cutPacing, "cut")] do
      let tl := Timeline.build steps p
      let n := tl.segments.size + 1
      let anims := #[Smil.animateRotate tl angleAt 50 60, Smil.animateTranslate tl (fun k =>
        (k.toFloat, 2 * k.toFloat)), Smil.animateOpacity tl (fun k => if k == 1 then 0 else 1),
        Smil.animateD tl pathAt, Smil.seamOpacity tl].filterMap id
      r := r.push (s!"smil: {name}, {seam}: n values, n key times, n - 1 splines, one clock",
        anims.size == (if seam == "cut" then 4 else 5) && anims.all (countsAgree n) &&
          Smil.clockProblem? (Svg.el "g" #[] anims) == none)
  let tl := decimalTimeline
  let rot := get (Smil.animateRotate tl angleAt 50 60)
  r := r.push ("smil: the decimal timeline is 10 seconds and its key times are written exactly",
    tl.cycle == 10 && attrOf rot "dur" == "10s" &&
      attrOf rot "keyTimes" == "0;0.05;0.2;0.3;0.4;0.5;0.6;0.7;0.95;1")
  r := r.push ("smil: rests repeat a value with the identity spline, moves carry the easing",
    attrOf rot "values" == "0 50 60;0 50 60;0 50 60;72 50 60;72 50 60;144 50 60;144 50 60;\
      216 50 60;216 50 60;216 50 60" &&
      attrOf rot "keySplines" == "0 0 1 1;0 0 1 1;0.42 0 0.58 1;0 0 1 1;0.42 0 0.58 1;\
        0 0 1 1;0.42 0 0.58 1;0 0 1 1;0 0 1 1")
  let custom : Array Step := #[{ dur := 0.7, easing := .spline 0.1 0.2 0.3 0.4 },
    { kind := .idle, dur := 1.3, easing := .linear }, { dur := 0.25, easing := .linear }]
  r := r.push ("smil: each interval is written with its segment's easing",
    attrOf (get (Smil.animateOpacity (Timeline.build custom {}) fun _ => 1)) "keySplines" ==
      "0 0 1 1;0 0 1 1;0.1 0.2 0.3 0.4;0 0 1 1;0 0 1 1;0 0 1 1;0 0 1 1;0 0 1 1;0 0 1 1")
  r := r.push ("smil: the motion layer fades in at the start of the cycle and out at its end",
    (Smil.seamOpacity tl).map (attrOf · "values") == some "0;1;1;1;1;1;1;1;1;0" &&
      (Smil.seamOpacity (Timeline.build (turns 3) cutPacing)).isNone)
  r := r.push ("smil: paths that cannot be interpolated give no morph",
    (Smil.animateD tl fun k => if k == 2 then "M0 0 L1 1" else pathAt k).isNone)
  r := r.push ("smil: a value with a ; is refused",
    (Smil.animateD tl fun k => if k == 2 then "M0 0;L1 1" else pathAt k).isNone)
  -- a cycle of length zero
  let still : Pacing := { firstHold := 0, lastHold := 0, hold := 0, seam := .cut }
  let zero := Timeline.build #[{ dur := 0 }] still
  r := r.push ("smil: a cycle of length zero gives no element",
    zero.cycle == 0 && (Smil.animateRotate zero angleAt 0 0).isNone &&
      (Smil.animateOpacity zero fun _ => 1).isNone && (Smil.animateD zero pathAt).isNone &&
      (Smil.animateTranslate zero fun _ => (0, 0)).isNone &&
      (Smil.seamOpacity
        (Timeline.build #[{ dur := 0 }] { still with seam := .crossfade 0 })).isNone &&
      (Smil.nest zero [(0, 0, angleAt)] #[]).isNone)
  -- coinciding boundaries
  let cases : Array (String × Timeline) :=
    #[("a rest of length zero", Timeline.build (turns 2) { hold := 0, seam := .cut }),
      ("a crossfade of length zero", Timeline.build (turns 1) { seam := .crossfade 0 }),
      ("a last rest of length zero", Timeline.build (turns 1) { seam := .cut, lastHold := 0 }),
      ("a first rest of length zero", Timeline.build (turns 1) { seam := .cut, firstHold := 0 }),
      ("five steps of length zero in a row", Timeline.build (Array.replicate 5 { dur := 0 })
        { seam := .crossfade 0, hold := 0 })]
  for (name, z) in cases do
    let raw := z.keyTimes
    let spread := Smil.times z
    let written := attrOf (get (Smil.animateOpacity z fun _ => 1)) "keyTimes"
    r := r.push (s!"smil: {name}: equal key times, kept as they are with a gap of 0",
      (raw.toList.zip raw.toList.tail).any (fun (a, b) => a == b) &&
        Smil.times z { gap := 0 } == raw)
    r := r.push (s!"smil: {name}: the key times go from 0 to 1, at least the gap apart, \
        each moved by at most the gap for each boundary",
      spread.size == raw.size && spreadWell (1 / 10000) spread.toList &&
        (raw.zip spread).all fun (a, b) => (a - b) * (a - b) ≤ ((raw.size : Rat) / 10000) ^ 2)
    r := r.push (s!"smil: {name}: the written key times go from 0 to 1 and increase",
      writtenWell written)
    r := r.push (s!"smil: {name}: a browser model animates every element",
      (Smil.valueAt (get (Smil.animateRotate z angleAt 0 0)) 0.1).isSome)
  r := r.push ("smil: a gap larger than its neighbours spreads them",
    Smil.spreadList (1 / 10) [0, 1 / 100, 2 / 100, 1] == [0, 1 / 10, 2 / 10, 1] &&
      Smil.spreadList (1 / 4) [0, 0, 1, 1] == [0, 1 / 4, 3 / 4, 1] &&
      Smil.spreadList (1 / 10) [0, 1 / 2, 1, 1] == [0, 1 / 2, 9 / 10, 1] &&
      Smil.spreadList (1 / 10) [0, 0, 0, 1, 1, 1] == [0, 1 / 10, 2 / 10, 8 / 10, 9 / 10, 1])
  r := r.push ("smil: the effective gap is at most half the cycle in all",
    Smil.effectiveGap 1 4 == 1 / 8 && Smil.effectiveGap 0 4 == 0 && Smil.effectiveGap (-1) 4 == 0)
  r := r.push ("smil: a gap below the printed precision is raised, so key times print apart",
    let z := Timeline.build (turns 2) { hold := 0, seam := .cut }
    Smil.effectiveGap (1 / 10 ^ 12) 5 == Smil.minGap &&
      writtenWell (attrOf (get (Smil.animateOpacity z (fun _ => 1) { gap := 1 / 10 ^ 12 }))
        "keyTimes"))
  -- the duration
  r := r.push ("smil: the same cycle is written alike, and a third of a second to the microsecond",
    Smil.durText (Timeline.build (turns 2) cutPacing).cycle ==
        Smil.durText (Timeline.build #[{ dur := 2.6 }] cutPacing).cycle &&
      Smil.durText (1 / 3) == "0.333333s" && Smil.durText 22.6 == "22.6s")
  return r

/-! ### The evaluator -/

/-- An `animate` element with the attributes. -/
def anim (attrs : Array (String × String)) : Node := Svg.el "animate" attrs

/-- The evaluator checks. -/
def evaluatorChecks : Array (String × Bool) := Id.run do
  let mut r : Array (String × Bool) := #[]
  let tl := decimalTimeline
  let rot := get (Smil.animateRotate tl angleAt 50 60)
  -- 50 times spread over the cycle, none on a boundary, and the same times a cycle later
  let samples : List Rat := (List.range 50).map fun (j : Nat) => (j : Rat) / 5 + 7 / 100
  r := r.push ("evaluator: animateRotate gives the eased angle at 50 times within 1e-9",
    samples.all fun t => match Smil.valueAt rot (Exact.toFloat t) with
      | some #[θ, cx, cy] => near θ (expected tl angleAt t) 1e-9 && cx == 50 && cy == 60
      | _ => false)
  r := r.push ("evaluator: and the same a cycle later",
    samples.all fun t => match Smil.valueAt rot (Exact.toFloat (t + 10)) with
      | some #[θ, _, _] => near θ (expected tl angleAt t) 1e-9
      | _ => false)
  r := r.push ("evaluator: at the middle of each rest the angle is the key's",
    (List.range 4).all fun k => match Smil.valueAt rot (Exact.toFloat (tl.restTime k)) with
      | some #[θ, _, _] => near θ (angleAt k) 1e-9
      | _ => false)
  r := r.push ("evaluator: the motion layer's opacity is 1 between the seams, 0 at the wrap",
    match Smil.seamOpacity tl with
    | some a => Smil.valueAt a 0 == some #[0] && Smil.valueAt a 5 == some #[1] &&
      (Smil.valueAt a 9.75).any (fun v => near (v.getD 0 9) 0.5 1e-12) &&
      (Smil.valueAt a 0.25).any (fun v => near (v.getD 0 9) 0.5 1e-12)
    | none => false)
  let morph := get (Smil.animateD tl pathAt)
  r := r.push ("evaluator: the morph moves the path's coordinates with the easing",
    samples.all fun t => match Smil.valueAt morph (Exact.toFloat t) with
      | some v => v.size == 8 &&
        near (v.getD 0 0) (expected tl (fun k => 10 * k.toFloat) t) 1e-9 &&
        near (v.getD 2 0) (expected tl (fun k => 10 * k.toFloat + 20) t) 1e-9
      | none => false)
  -- the default pacing, 13 keys: key times rounded to eight decimals of a 22.6-second cycle
  let big := Timeline.build mixed {}
  let rotBig := get (Smil.animateRotate big angleAt 0 0)
  r := r.push ("evaluator: 13 keys with the default pacing within 1e-3 degrees",
    (List.range 200).all fun j =>
      let t : Rat := (j : Rat) * big.cycle / 200 + 1 / 1000
      match Smil.valueAt rotBig (Exact.toFloat t) with
      | some #[θ, _, _] => near θ (expected big angleAt t) 1e-3
      | _ => false)
  r := r.push ("evaluator: discrete and linear modes, clock values",
    Smil.valueAt (anim #[("values", "0;10;20"), ("dur", "3s"), ("calcMode", "discrete")]) 1.5 ==
        some #[10] &&
      Smil.valueAt (anim #[("values", "0;10"), ("dur", "2000ms")]) 0.5 == some #[2.5] &&
      Smil.valueAt (anim #[("values", "0;10"), ("dur", "0.05min")]) 1.5 == some #[5] &&
      Smil.valueAt (anim #[("values", "0;10"), ("dur", "4")]) 1 == some #[2.5])
  let spline := fun (kt ks : String) => anim #[("values", "0;10;20"), ("dur", "1s"),
    ("calcMode", "spline"), ("keyTimes", kt), ("keySplines", ks)]
  r := r.push ("evaluator: a well-formed spline animation has a value",
    (Smil.valueAt (spline "0;0.5;1" "0 0 1 1;0.42 0 0.58 1") 0.25).isSome)
  r := r.push ("evaluator: what a browser refuses has no value",
    let bad : List Node :=
      [spline "0.1;0.5;1" "0 0 1 1;0 0 1 1", spline "0;0.5;0.9" "0 0 1 1;0 0 1 1",
        spline "0;0.6;0.5" "0 0 1 1;0 0 1 1", spline "0;1" "0 0 1 1",
        spline "0;0.5;1" "0 0 1 1", spline "0;0.5;1" "0 0 1 1;0 0 1 1.2",
        spline "0;0.5;1" "0 0 1 1;-0.1 0 1 1", spline "0;0.5;1" "0 0 1 1;0 0 1",
        anim #[("values", "0;10"), ("dur", "0s")], anim #[("values", "0;10"), ("dur", "-1s")],
        anim #[("values", "0;10"), ("dur", "indefinite")],
        anim #[("values", "0;10"), ("dur", "1e3s")],
        anim #[("values", "0;10")], anim #[("values", "0 1;10"), ("dur", "1s")],
        anim #[("values", "0;10"), ("dur", "1s"), ("calcMode", "paced")],
        anim #[("values", "0;10"), ("dur", "2s"), ("keyTimes", "0;0.5;1")],
        anim #[("values", "0;1;2"), ("dur", "1s"), ("calcMode", "discrete"),
          ("keyTimes", "0.2;0.5;0.7")]]
    bad.all fun n => (Smil.valueAt n 0.3).isNone)
  r := r.push ("evaluator: the key times of a last rest of length zero, unspread, are refused",
    (Smil.valueAt (spline "0;0.0001;1.0001" "0 0 1 1;0 0 1 1") 0.5).isNone &&
      (Smil.valueAt (anim #[("values", "0;0;90;90;90;90"), ("dur", "4s"), ("calcMode", "spline"),
        ("keyTimes", "0;0.0001;0.3;0.55;1;1.0001"),
        ("keySplines", "0 0 1 1;0 0 1 1;0 0 1 1;0 0 1 1;0 0 1 1")]) 0.5).isNone)
  return r

/-! ### Turns -/

/-- The rotation of a point by `θ` degrees about `(cx, cy)`, as SVG's `rotate(θ cx cy)`. -/
def rotate (θ cx cy : Float) (q : Float × Float) : Float × Float :=
  let a := θ * 3.141592653589793 / 180
  let (x, y) := (q.1 - cx, q.2 - cy)
  (cx + x * a.cos - y * a.sin, cy + x * a.sin + y * a.cos)

/-- The `animateTransform` elements of a chain of groups, outermost first. -/
partial def chain : Node → List Node
  | .element "g" _ children =>
    let own := children.toList.filter fun
      | .element n _ _ => n == "animateTransform" | _ => false
    own ++ (children.toList.flatMap fun c => match c with
      | .element "g" _ _ => chain c | _ => [])
  | _ => []

/-- Where the point `q` is drawn at the time `t` inside a chain of turning groups: the innermost
group's turn first. -/
def drawnAt (tree : Node) (t : Float) (q : Float × Float) : Option (Float × Float) :=
  (chain tree).reverse.foldlM (init := q) fun q a => do
    let v ← Smil.valueAt a t
    match v with
    | #[θ, cx, cy] => some (rotate θ cx cy q)
    | _ => none

/-- The turn checks. -/
def turnChecks : Array (String × Bool) := Id.run do
  let mut r : Array (String × Bool) := #[]
  r := r.push ("turns: the angles after each key are the exact sums of the turns",
    (List.range 5).map (Smil.turnAngles #[1 / 4, 0, 1 / 2]) == [0, 90, 90, 270, 270] &&
      (List.range 4).map (Smil.uprightAngles #[1 / 4, 0, 1 / 2]) == [0, -90, -90, -270] &&
      (List.range 4).map (Smil.stepAngles 1 (1 / 3)) == [0, 0, 120, 120] &&
      Smil.turnAngles #[1 / 3, 1 / 3, 1 / 3] 3 == 360)
  -- a point at (2, 0) turned a quarter about (0, 0) in step 0, then a quarter about (1, 0)
  let tl := Timeline.build (turns 2) { firstHold := 1, hold := 1, lastHold := 1, seam := .cut }
  let turnsAt := [((0 : Float), (0 : Float), Smil.stepAngles 0 (1 / 4)),
    ((1 : Float), (0 : Float), Smil.stepAngles 1 (1 / 4))]
  let tree := get (Smil.nest tl turnsAt #[Svg.el "circle" #[("cx", "2"), ("cy", "0"), ("r", "1")]])
  let posAt := fun (t : Rat) => drawnAt tree (Exact.toFloat t) (2, 0)
  let closeTo := fun (a : Option (Float × Float)) (b : Float × Float) =>
    a.any fun (x, y) => near x b.1 1e-9 && near y b.2 1e-9
  r := r.push ("turns: nest puts the earliest turn innermost (exact positions at the rests)",
    closeTo (posAt (tl.restTime 0)) (2, 0) && closeTo (posAt (tl.restTime 1)) (0, 2) &&
      closeTo (posAt (tl.restTime 2)) (-1, -1) &&
      Smil.invariantProblem? 64 tree == none && Smil.clockProblem? tree == none)
  r := r.push ("turns: the drawn point is the composed exact turns at 40 times",
    (List.range 40).all fun j =>
      let t : Rat := (j : Rat) * tl.cycle / 40 + 1 / 1000
      let θ₀ := expected tl (Smil.stepAngles 0 (1 / 4)) t
      let θ₁ := expected tl (Smil.stepAngles 1 (1 / 4)) t
      let q := rotate θ₁ 1 0 (rotate θ₀ 0 0 (2, 0))
      closeTo (posAt t) q && (q.1 - 1) ^ 2 + q.2 ^ 2 > 0)
  r := r.push ("turns: during a turn the point stays on its circle (a true arc)",
    (List.range 20).all fun j =>
      let t : Rat := 1 + (j : Rat) / 20
      (posAt t).any fun (x, y) => near (x * x + y * y) 4 1e-9)
  -- the other order puts the point elsewhere
  let wrong := get (Smil.nest tl turnsAt.reverse #[])
  r := r.push ("turns: the other order of the groups would draw another point",
    !closeTo (drawnAt wrong (Exact.toFloat (tl.restTime 2)) (2, 0)) (-1, -1))
  -- an upright label: the counter-rotation about its anchor undoes the whole angle
  let upright := Smil.group (get (Smil.animateRotate tl (Smil.uprightAngles #[1 / 4, 1 / 4]) 2 0))
    #[Svg.text 2 0 "P" 12 ⟨0, 0, 0, 255⟩ .start]
  let label := get (Smil.nest tl turnsAt #[upright])
  r := r.push ("turns: an upright label's net angle is zero at all times",
    (chain label).length == 3 && Smil.invariantProblem? 64 label == none &&
      (List.range 40).all fun j =>
        let t := Exact.toFloat ((j : Rat) * tl.cycle / 40 + 1 / 1000)
        let angles := (chain label).filterMap fun a => (Smil.valueAt a t).bind (·[0]?)
        angles.length == 3 && near (angles.foldl (· + ·) 0) 0 1e-9)
  return r

/-! ### The invariant, the clock and inertness -/

/-- A tree of everything the builders write: a turning group around a sliding group around a
morphing path and a fading label, inside the faded motion layer. -/
def sample (tl : Timeline) : Node :=
  let path := Svg.el "path" #[("d", pathAt 0), ("fill", "#336699")]
    ((Smil.animateD tl pathAt).toArray)
  let label := Smil.group (get (Smil.animateOpacity tl fun k => if k == 1 then 0 else 1))
    #[Svg.text 10 10 "a" 12 ⟨0, 0, 0, 255⟩ .start]
  let slide := Smil.group (get (Smil.animateTranslate tl fun k => (k.toFloat, 0))) #[path, label]
  let turn := Smil.group (get (Smil.animateRotate tl angleAt 50 60)) #[slide]
  match Smil.seamOpacity tl with
  | some s => Smil.group s #[turn]
  | none => turn

/-- The invariant and inertness checks. -/
def invariantChecks : Array (String × Bool) := Id.run do
  let mut r : Array (String × Bool) := #[]
  for (tl, name) in [(decimalTimeline, "crossfade"), (Timeline.build mixed cutPacing, "cut")] do
    let tree := sample tl
    let doc := Svg.document 100 100 #[tree]
    r := r.push (s!"invariant: the builders' tree keeps the invariant ({name})",
      Smil.invariantProblem? 64 tree == none)
    r := r.push (s!"invariant: no static transform is written ({name})",
      !(doc.splitOn " transform=").length > 1 &&
        (doc.splitOn "attributeName=\"transform\"").length == 3)
    r := r.push (s!"clock: every animation of the tree is on one clock ({name})",
      Smil.clockProblem? tree == none)
    r := r.push (s!"inert: everything the builders write is inert ({name})", isInert doc)
  let tl := decimalTimeline
  let rot := get (Smil.animateRotate tl angleAt 0 0)
  let planted : Array (String × Node) :=
    #[("a static transform", Svg.el "g" #[("transform", "rotate(3)")] #[]),
      ("a gradientTransform", Svg.el "linearGradient" #[("gradientTransform", "rotate(3)")] #[]),
      ("a patternTransform", Svg.el "g" #[("patternTransform", "rotate(3)")] #[]),
      ("a style with a transform", Svg.el "g" #[("style", "Transform: rotate(3deg)")] #[]),
      ("an additive animation", Svg.el "path" #[] #[Svg.el "animate"
        #[("attributeName", "d"), ("additive", "sum")]]),
      ("an accumulating animation", Svg.el "g" #[] #[Svg.el "animate"
        #[("attributeName", "opacity"), ("accumulate", "sum")]]),
      ("an animated colour", Svg.el "g" #[] #[Svg.el "animate" #[("attributeName", "fill")]]),
      ("an animated fill-opacity",
        Svg.el "g" #[] #[Svg.el "animate" #[("attributeName", "fill-opacity")]]),
      ("an animated style", Svg.el "g" #[] #[Svg.el "animate" #[("attributeName", "style")]]),
      ("an animateTransform in a g with a class", Svg.el "g" #[("class", "a")] #[rot]),
      ("an animateTransform in a path", Svg.el "path" #[] #[rot]),
      ("two animateTransforms in one g", Svg.el "g" #[] #[rot, rot]),
      ("an animated d outside a path",
        Svg.el "g" #[] #[Svg.el "animate" #[("attributeName", "d")]]),
      ("a set element", Svg.el "g" #[] #[Svg.el "set" #[("attributeName", "opacity")]]),
      ("an animateMotion",
        Svg.el "g" #[] #[Svg.el "animateMotion" #[("attributeName", "transform")]]),
      ("a break deep inside", Smil.group rot #[Svg.el "g" #[] #[Svg.el "g" #[]
        #[Svg.el "rect" #[("transform", "scale(2)")]]]])]
  for (name, n) in planted do
    r := r.push (s!"invariant: {name} is reported", (Smil.invariantProblem? 64 n).isSome)
  let other := get (Smil.animateRotate (Timeline.build (turns 3) {}) angleAt 0 0)
  let noBegin := Svg.el "animate" #[("attributeName", "opacity"), ("values", "0;1"),
    ("dur", "10s"), ("keyTimes", "0;1"), ("calcMode", "linear"), ("repeatCount", "indefinite")]
  r := r.push ("clock: two timelines in one tree are reported",
    (Smil.clockProblem? (Svg.el "g" #[] #[Smil.group rot #[], Smil.group other #[]])).isSome)
  r := r.push ("clock: an animation without begin is reported",
    (Smil.clockProblem? (Svg.el "g" #[] #[noBegin])).isSome)
  r := r.push ("clock: a tree without animations is on no clock and fine",
    Smil.clockProblem? (Svg.el "g" #[] #[Svg.el "rect" #[]]) == none)
  return r

/-- The checks of rests of their own, of divided segments and of the parts of an easing. -/
def divisionChecks : Array (String × Bool) := Id.run do
  let mut r : Array (String × Bool) := #[]
  let steps := turns 3
  let own : Pacing := { holds := #[some 2, none, some (1 / 10), some (1 / 2)] }
  let tl := Timeline.build steps own
  let restOf := fun (k : Nat) => ((tl.segments.find? (·.kind == .rest k)).map (·.dur)).getD 0
  r := r.push ("timeline: a key's own rest wins over the first, the last and the other holds",
    restOf 0 == 2 && restOf 1 == own.hold && restOf 2 == 1 / 10 && restOf 3 == 1 / 2 &&
      wellFormed tl &&
      tl.cycle == (Timeline.build steps {}).cycle + (2 - 1.2) + (1 / 10 - 0.6) + (1 / 2 - 1.8))
  -- a timeline divided: every rest in three parts, every move in two
  let parts := fun (s : Segment) => match s.kind with
    | .rest _ => [((1 : Rat) / 4, Easing.linear), (1 / 2, .standard), (1, .linear)]
    | .move _ => [((7 : Rat) / 10, Easing.linear), (1, .linear)]
    | _ => []
  let d := tl.divide parts
  r := r.push ("timeline: divided, its parts tile the cycle, the key times start at 0 and end at 1",
    wellFormed d && d.segments.size == tl.segments.size + 2 * 4 + 3 && d.cycle == tl.cycle &&
      d.keys == tl.keys)
  r := r.push ("timeline: divided, a key's still is in the middle of the last part of its rest",
    (List.range 4).all fun k =>
      d.restTime k == ((d.segments.findRev? (·.kind == .rest k)).map fun s =>
        s.start + s.dur / 2).getD 0 &&
      (d.stillPart? k).map (·.dur) == some (restOf k / 2))
  -- the parts of an easing are the easing between its values at the part's ends
  let partWithin := fun (tol : Float) (e : Easing) (a b : Float) =>
    match e.part a b with
    | none => false
    | some q =>
      let ya := e.eval a
      let yb := e.eval b
      (List.range 21).all fun i =>
        let x := i.toFloat / 20
        let want := (e.eval (a + x * (b - a)) - ya) / (yb - ya)
        (q.eval x - want).abs < tol
  let partOk := partWithin 1e-6
  r := r.push ("easing: a part of the standard easing is a timing curve that follows it",
    [(0, 0.3), (0.7, 1), (0.2, 0.4), (0.45, 0.55), (0, 0.05), (0.9, 1)].all fun (a, b) =>
      partOk .standard a b)
  r := r.push ("easing: parts of other curves follow them; the identity's parts are the identity",
    partOk (.spline 0.25 0.1 0.25 1) 0.1 0.6 && partOk (.spline 0 0 1 1) 0.3 0.8 &&
      Easing.linear.part 0.2 0.7 == some .linear)
  r := r.push ("easing: a part of no length is refused; extreme curves have parts that follow them \
      (within 1e-4 where the curve is steep)",
    Easing.standard.part 0.5 0.5 == none &&
      [Easing.spline 1 0 0 1, .spline 0 1 1 0, .spline 1 1 0 0, .spline 0 1 0 1].all fun e =>
        [(0, 0.3), (0.3, 0.7), (0.7, 1), (0.45, 0.55)].all fun (a, b) => partWithin 1e-4 e a b)
  -- steep named curves refuse some parts; halved, every piece is a timing curve, and the pieces
  -- as written (six decimals) keep the step's eased progress within 1.6e-6 of its change
  let named : List Easing := [.spline 0.83 0 0.17 1, .spline 0.87 0 0.13 1, .spline 0.85 0 0.15 1,
    .spline 0.76 0 0.24 1, .standard, .spline 0.25 0.1 0.25 1]
  let worst := fun (e : Easing) => Id.run do
    let mut w : Float := 0
    let mut exact := true
    for i in [0:20] do
      for j in [i + 1:21] do
        let a : Rat := (i : Rat) / 20
        let mut lo := a
        for (c, q?) in PILean.Plane.easedParts e PILean.Plane.maxEasedDepth a ((j : Rat) / 20) do
          match q? with
          | none => exact := false
          | some q =>
            let (x₁, y₁, x₂, y₂) := q.controls
            let w6 := fun (x : Float) => PILean.Plane.quant 6 x
            let pq := Easing.spline (w6 x₁) (w6 y₁) (w6 x₂) (w6 y₂)
            let fa := Exact.toFloat lo
            let fb := Exact.toFloat c
            for k in [0:21] do
              let x := k.toFloat / 20
              let got := e.eval fa + (e.eval fb - e.eval fa) * pq.eval x
              w := max w (got - e.eval (fa + x * (fb - fa))).abs
          lo := c
    return (exact, w)
  r := r.push ("easing: parts refused by steep curves are halved into timing curves, within \
      1.6e-6 of the step's change as written",
    (Easing.spline 0.83 0 0.17 1).part 0 0.6 == none &&
      named.all fun e => let (ok, w) := worst e; ok && w < 1.6e-6)
  r := r.push ("easing: a part that does not end after it starts is one part without easing, not \
      halved into 2 ^ 16 parts",
    named.all fun e =>
      let back := PILean.Plane.easedParts e PILean.Plane.maxEasedDepth (3 / 4) (1 / 4)
      let flat := PILean.Plane.easedParts e PILean.Plane.maxEasedDepth (1 / 2) (1 / 2)
      back.length == 1 && flat.length == 1)
  return r

/-- All checks. -/
def checks : Array (String × Bool) :=
  easingChecks ++ timelineChecks ++ smilChecks ++ evaluatorChecks ++ turnChecks ++
    invariantChecks ++ divisionChecks

end PILeanTest.TimelineChecks
