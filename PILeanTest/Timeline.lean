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
    r := r.push (s!"timeline: {name}: moves are eased, steps that do not move are not",
      (List.range n).all fun j => match cf.segments.find? (·.kind == .move j) with
        | some s => s.easing == (if steps[j]!.kind == .move then p.easing else .linear) &&
          s.dur == steps[j]!.dur
        | none => false)
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
  return r

/-! ### SMIL attributes -/

/-- The value of an attribute of an element. -/
def attrOf (n : Node) (key : String) : String :=
  match n with
  | .element _ attrs _ => (Smil.attr? attrs key).getD ""
  | .text _ => ""

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

/-- The SMIL checks. -/
def smilChecks : Array (String × Bool) := Id.run do
  let mut r : Array (String × Bool) := #[]
  for (steps, name) in [(turns 0, "1 key"), (turns 1, "2 keys"), (turns 12, "13 keys"),
      (mixed, "mixed steps")] do
    for (p, seam) in [(({} : Pacing), "crossfade"), (cutPacing, "cut")] do
      let tl := Timeline.build steps p
      let n := tl.segments.size + 1
      let anims := #[Smil.animateRotate tl angleAt 50 60, Smil.animateTranslate tl (fun k =>
        (k.toFloat, 2 * k.toFloat)), Smil.animateOpacity tl (fun k => if k == 1 then 0 else 1)] ++
        (Smil.animateD tl pathAt).toArray ++ (Smil.seamOpacity tl).toArray
      r := r.push (s!"smil: {name}, {seam}: n values, n key times, n - 1 splines, one clock",
        anims.size == (if seam == "cut" then 4 else 5) && anims.all (countsAgree n) &&
          anims.all fun a => attrOf a "dur" == attrOf anims[0]! "dur" &&
            attrOf a "keyTimes" == attrOf anims[0]! "keyTimes")
  let tl := decimalTimeline
  let rot := Smil.animateRotate tl angleAt 50 60
  r := r.push ("smil: the decimal timeline is 10 seconds and its key times are written exactly",
    tl.cycle == 10 && attrOf rot "dur" == "10s" &&
      attrOf rot "keyTimes" == "0;0.05;0.2;0.3;0.4;0.5;0.6;0.7;0.95;1")
  r := r.push ("smil: rests repeat a value with the identity spline, moves carry the easing",
    attrOf rot "values" == "0 50 60;0 50 60;0 50 60;72 50 60;72 50 60;144 50 60;144 50 60;\
      216 50 60;216 50 60;216 50 60" &&
      attrOf rot "keySplines" == "0 0 1 1;0 0 1 1;0.42 0 0.58 1;0 0 1 1;0.42 0 0.58 1;\
        0 0 1 1;0.42 0 0.58 1;0 0 1 1;0 0 1 1")
  r := r.push ("smil: the motion layer fades in at the start of the cycle and out at its end",
    (Smil.seamOpacity tl).map (attrOf · "values") == some "0;1;1;1;1;1;1;1;1;0" &&
      (Smil.seamOpacity (Timeline.build (turns 3) cutPacing)).isNone)
  r := r.push ("smil: paths that cannot be interpolated give no morph",
    (Smil.animateD tl fun k => if k == 2 then "M0 0 L1 1" else pathAt k).isNone)
  -- equal key times: a rest of length zero
  let z := Timeline.build (turns 2) { hold := 0, seam := .cut }
  let raw := z.keyTimes
  let spread := Smil.times z
  r := r.push ("smil: a segment of length zero gives equal key times, kept with a gap of 0",
    (List.range (raw.size - 1)).any (fun i => raw[i]! == raw[i + 1]!) &&
      Smil.times z { gap := 0 } == raw)
  r := r.push ("smil: with the default gap the key times increase strictly from 0 to 1",
    spread.size == raw.size && spread[0]? == some 0 && spread.back? == some 1 &&
      (List.range (spread.size - 1)).all (fun i => spread[i]! + 1 / 10000 ≤ spread[i + 1]!) &&
      (raw.zip spread).all fun (a, b) => (a - b) * (a - b) ≤ 1 / 10000 ^ 2 * 4)
  r := r.push ("smil: the written key times increase strictly too",
    let ts := (Smil.entries (attrOf (Smil.animateOpacity z fun _ => 1) "keyTimes")).filterMap
      Raster.parseNumber?
    (List.range (ts.size - 1)).all fun i => ts[i]! < ts[i + 1]!)
  r := r.push ("smil: crowded times are spread by at most half of each interval",
    let s := Smil.spread (1 / 2) #[0, 0, 0, 0, 1]
    s == #[0, 1 / 8, 2 / 8, 3 / 8, 1])
  return r

/-! ### The evaluator -/

/-- The evaluator checks. -/
def evaluatorChecks : Array (String × Bool) := Id.run do
  let mut r : Array (String × Bool) := #[]
  let tl := decimalTimeline
  let rot := Smil.animateRotate tl angleAt 50 60
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
      (Smil.valueAt a 9.75).any (fun v => near v[0]! 0.5 1e-12) &&
      (Smil.valueAt a 0.25).any (fun v => near v[0]! 0.5 1e-12)
    | none => false)
  let morph := (Smil.animateD tl pathAt).getD (.text "")
  r := r.push ("evaluator: the morph moves the path's coordinates with the easing",
    samples.all fun t => match Smil.valueAt morph (Exact.toFloat t) with
      | some v => v.size == 8 && near v[0]! (expected tl (fun k => 10 * k.toFloat) t) 1e-9 &&
        near v[2]! (expected tl (fun k => 10 * k.toFloat + 20) t) 1e-9
      | none => false)
  -- the default pacing, 13 keys: key times rounded to eight decimals of a 22.6-second cycle
  let big := Timeline.build mixed {}
  let rotBig := Smil.animateRotate big angleAt 0 0
  r := r.push ("evaluator: 13 keys with the default pacing within 1e-3 degrees",
    (List.range 200).all fun j =>
      let t : Rat := (j : Rat) * big.cycle / 200 + 1 / 1000
      match Smil.valueAt rotBig (Exact.toFloat t) with
      | some #[θ, _, _] => near θ (expected big angleAt t) 1e-3
      | _ => false)
  r := r.push ("evaluator: discrete and linear modes, and malformed input",
    let el := fun (attrs : Array (String × String)) => Svg.el "animate" attrs
    Smil.valueAt (el #[("values", "0;10;20"), ("dur", "3s"), ("calcMode", "discrete")]) 1.5 ==
        some #[10] &&
      Smil.valueAt (el #[("values", "0;10"), ("dur", "2000ms")]) 0.5 == some #[2.5] &&
      Smil.valueAt (el #[("values", "0;10"), ("dur", "2s"), ("keyTimes", "0;0.5;1")]) 1 == none &&
      Smil.valueAt (el #[("values", "0;10"), ("dur", "0s")]) 1 == none &&
      Smil.valueAt (el #[("values", "0 1;10"), ("dur", "1s")]) 0.5 == none &&
      Smil.valueAt (el #[("values", "0;10"), ("dur", "1s"), ("calcMode", "paced")]) 0.5 == none)
  return r

/-! ### The invariant and inertness -/

/-- A tree of everything the builders write: a turning group around a sliding group around a
morphing path and a fading label, inside the faded motion layer. -/
def sample (tl : Timeline) : Node :=
  let path := Svg.el "path" #[("d", pathAt 0), ("fill", "#336699")]
    ((Smil.animateD tl pathAt).toArray)
  let label := Smil.group (Smil.animateOpacity tl fun k => if k == 1 then 0 else 1)
    #[Svg.text 10 10 "a" 12 ⟨0, 0, 0, 255⟩ .start]
  let slide := Smil.group (Smil.animateTranslate tl fun k => (k.toFloat, 0)) #[path, label]
  let turn := Smil.group (Smil.animateRotate tl angleAt 50 60) #[slide]
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
    r := r.push (s!"inert: everything the builders write is inert ({name})", isInert doc)
  let tl := decimalTimeline
  let rot := Smil.animateRotate tl angleAt 0 0
  let planted : Array (String × Node) :=
    #[("a static transform", Svg.el "g" #[("transform", "rotate(3)")] #[]),
      ("an animated colour", Svg.el "g" #[] #[Svg.el "animate" #[("attributeName", "fill")]]),
      ("an animated fill-opacity",
        Svg.el "g" #[] #[Svg.el "animate" #[("attributeName", "fill-opacity")]]),
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
  return r

/-- All checks. -/
def checks : Array (String × Bool) :=
  easingChecks ++ timelineChecks ++ smilChecks ++ evaluatorChecks ++ invariantChecks

end PILeanTest.TimelineChecks
