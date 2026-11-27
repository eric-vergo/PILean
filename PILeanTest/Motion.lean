/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean

/-!
# Motion tests

Motions of plane figures (`PILean.Plane.Motion`, `PILean.Plane.MotionPlan`):

* the model's rules: well-formedness, honest arrival (a wrong angle, a wrong centre, a turn of an
  item that did not move, a move of an actor missing from a key), crossfades reported as notes,
  lines and rays refused in a turning actor, the checks level;
* the layout: shared chains for a rigid body, one opacity animation for points that appear in the
  same step, kept automatic label placements, morphs (interpolated, or crossfaded);
* the writer against the baker: `Smil.valueAt` over the written tree gives every actor's anchor
  and every upright leaf's anchor where `MotionPlan.markersAt` has it, within `1e-6` px, at 50
  times; upright leaves have a net angle of zero;
* the stills are the key figures, byte for byte; every output is inert, keeps the invariant of the
  SMIL builders and runs on one clock;
* the two golden motions (`examples/motion-turn.svg`, `examples/motion-two-centres.svg`) and the
  expectations `tools/motion-browser-check.py` reads (`writeBrowserFiles`).
-/

namespace PILeanTest.MotionChecks

open PILean PILean.Plane PILean.Anim PILean.Svg

/-! ### The golden motions -/

/-- A rational point. -/
abbrev Q := Rat × Rat

/-- The point `P` with its upright label, at `p`. -/
def pointP (p : Q) : Item :=
  (group #[Plane.Exact.point p |>.accent 0 |>.incident .on "the unit circle",
    Plane.Exact.label "P" p .aboveRight |>.accent 0]).actor "P"

/-- The frame of reference drawn in every key: the origin and the unit circle. -/
def turnBackdrop : Array Item :=
  #[Plane.Exact.circle ((0, 0) : Q) (1 : Rat) |>.faint |>.named "the unit circle",
    Plane.Exact.point ((0, 0) : Q) |>.faint,
    Plane.Exact.label "O" ((0, 0) : Q) .belowLeft |>.faint]

/-- One point turned a quarter about the origin, then an idle step. -/
def turnMotion : Motion where
  keys := #[{ items := turnBackdrop.push (pointP (1, 0)), width := 320 },
    { items := turnBackdrop.push (pointP (0, 1)), width := 320 },
    { items := turnBackdrop.push (pointP (0, 1)), width := 320 }]
  captions := #["Key 1 of 3: P at (1, 0).", "Key 2 of 3: P turned a quarter about O.",
    "Key 3 of 3: nothing moves."]
  steps := #[{ moves := #[("P", Plane.Exact.turnAbout ((0, 0) : Q) (1 / 4))] }, MotionStep.idle]
  info := { title := "A quarter turn", description := "The point P turns about the origin O." }

/-- The point `A` with its label. -/
def pointA (p : Q) : Item :=
  (group #[Plane.Exact.point p |>.accent 1, Plane.Exact.label "A" p .right |>.accent 1]).actor "A"

/-- The rigid body: a triangle, its corner and a small disk, three actors that move together. -/
def body (a b c : Q) : Array Item :=
  #[Plane.Exact.polygon [a, b, c] |>.filled |>.accent 2 |>.actor "T1",
    Plane.Exact.point a |>.accent 2 |>.actor "T2",
    Plane.Exact.disk c (1 / 5 : Rat) |>.accent 2 |>.actor "T3"]

/-- The centres of the turns, drawn in every key. -/
def centres : Array Item :=
  #[Plane.Exact.point ((0, 0) : Q) |>.faint, Plane.Exact.label "O" ((0, 0) : Q) .belowLeft |>.faint,
    Plane.Exact.point ((1, 1) : Q) |>.faint, Plane.Exact.label "C" ((1, 1) : Q) .above |>.faint]

/-- A point turned about two centres in turn (a quarter about `O`, then a half about `C`), a rigid
body of three items turned with it in the first step, a point that appears, and a point that
slides. -/
def twoCentresMotion : Motion where
  keys :=
    let bodyBefore := body (-2, 0) (-3, 0) (-2, 1)
    let bodyAfter := body (0, -2) (0, -3) (-1, -2)
    let b := Plane.Exact.point ((3, 2) : Q) |>.accent 0 |>.actor "B"
    let s := fun (p : Q) => Plane.Exact.point p |>.marker .square |>.actor "S"
    #[{ items := centres ++ bodyBefore ++ #[pointA (1, 0), s (2, -1)], width := 360 },
      { items := centres ++ bodyAfter ++ #[pointA (0, 1), s (2, -1)], width := 360 },
      { items := centres ++ bodyAfter ++ #[pointA (2, 1), b, s (2, -1)], width := 360 },
      { items := centres ++ bodyAfter ++ #[pointA (2, 1), b, s (3, -1)], width := 360 }]
  captions := #["Key 1 of 4.", "Key 2 of 4: A and the triangle turned a quarter about O.",
    "Key 3 of 4: A turned a half about C; B appears.", "Key 4 of 4: S slides one to the right."]
  steps :=
    let quarter := Plane.Exact.turnAbout ((0, 0) : Q) (1 / 4)
    #[{ moves := #[("A", quarter), ("T1", quarter), ("T2", quarter), ("T3", quarter)] },
      { moves := #[("A", Plane.Exact.turnAbout ((1, 1) : Q) (1 / 2)), ("B", .appear)] },
      { moves := #[("S", Plane.Exact.slideFromTo ((2, -1) : Q) (3, -1))] }]
  info :=
    let description := "A turns about O and then about C; the triangle turns with it about O."
    { title := "Turns about two centres", description }

/-- A large disk with its centre and an upright label, turned a fifth about an outside centre `O`,
then an idle step: a circle turned by 72°, which the next key draws with its own cubics. -/
def fifthMotion : Motion where
  keys :=
    let diskAt := fun (a : Float) =>
      let c := Plane.polar 2.5 a
      (group #[Plane.disk c 1.2 |>.accent 1, Plane.point c |>.accent 1,
        Plane.label "D" c .above |>.accent 1]).actor "D"
    let o := #[Plane.point ⟨0, 0⟩ |>.faint, Plane.label "O" ⟨0, 0⟩ .belowLeft |>.faint]
    let at72 := diskAt (2 * Plane.pi / 5)
    #[{ items := o.push (diskAt 0), width := 360 }, { items := o.push at72, width := 360 },
      { items := o.push at72, width := 360 }]
  captions := #["Key 1 of 3: the disk D.", "Key 2 of 3: D turned a fifth about O.",
    "Key 3 of 3: nothing moves."]
  steps := #[{ moves := #[("D", Plane.Exact.turnAbout ((0, 0) : Q) (1 / 5))] }, MotionStep.idle]
  info := { title := "A fifth of a turn", description := "The disk D turns about O by 72°." }

/-- The backdrop of `announceMotion`: the centres `A` and `B` of its turns, faint. -/
def announceBackdrop : Array Item :=
  #[Plane.Exact.point ((0, 0) : Q) |>.faint, Plane.Exact.label "A" ((0, 0) : Q) .belowLeft |>.faint,
    Plane.Exact.point ((0, 2) : Q) |>.faint, Plane.Exact.label "B" ((0, 2) : Q) .aboveLeft |>.faint]

/-- The triangle of `announceMotion` with the vertices `a`, `b` and `c`. -/
def announceTriangle (a b c : Q) : Item :=
  Plane.Exact.polygon [a, b, c] |>.filled |>.accent 0 |>.actor "T"

/-- The ring that marks the centre `c` of the next turn, an actor `id`. -/
def announceMark (id : String) (c : Q) : Item :=
  Plane.Exact.circle c (3 / 10 : Rat) |>.accent 1 |>.actor id

/-- A triangle turned a quarter about `A`, then a quarter about `B`, then slid down, a ring marking
the centre of each turn before it: the ring at `A` is there on key 0; during the rest on key 1
(0.9 s, its own) the ring at `A` fades out in the first 0.2 s and the ring at `B` fades in over the
next 0.2 s, then stands with the triangle for 0.5 s; the ring at `B` fades out in the last 0.3 s
of the turn about `B`. Key 2, after that turn, is not a still: the motion rests on it for 0.3 s and
slides on. -/
def announceMotion : Motion where
  keys :=
    let k := fun (t : Item) (marks : Array Item) =>
      ({ items := announceBackdrop ++ #[t] ++ marks, width := 320 } : Figure)
    #[k (announceTriangle (1, 0) (2, 0) (1, 1)) #[announceMark "mA" (0, 0)],
      k (announceTriangle (0, 1) (0, 2) (-1, 1)) #[announceMark "mB" (0, 2)],
      k (announceTriangle (1, 2) (0, 2) (1, 1)) #[],
      k (announceTriangle (1, 0) (0, 0) (1, -1)) #[]]
  captions := #["The triangle; the ring at A marks the next turn, a quarter about A.",
    "Turned a quarter about A; the ring at B marks the next turn, a quarter about B.", "",
    "Turned a quarter about B, then slid down by 2."]
  steps := #[{ moves := #[("T", Plane.Exact.turnAbout ((0, 0) : Q) (1 / 4))] },
    { moves := #[("T", Plane.Exact.turnAbout ((0, 2) : Q) (1 / 4)), ("mB", .vanish)],
      windows := #[("mB", .last (3 / 10))] },
    { moves := #[("T", Plane.Exact.slideFromTo ((1, 2) : Q) (1, 0))] }]
  keyOptions := #[{},
    { rest := some (9 / 10),
      fades := #[("mA", .vanish, .seconds 0 (1 / 5)), ("mB", .appear, .seconds (1 / 5) (2 / 5))] },
    { still := false, rest := some (3 / 10) }, {}]
  info := { title := "A mark that announces the next turn",
            description := "A triangle turns about A, then about B, then slides down; a ring marks \
              the centre of each turn before it." }

/-- The golden motions, by file name. -/
def golden : Array (String × Motion) :=
  #[("motion-turn", turnMotion), ("motion-two-centres", twoCentresMotion),
    ("motion-fifth", fifthMotion), ("motion-announce", announceMotion)]

/-- `turnMotion` with a first hold of 2 seconds: a probe that switches reduced motion on at a
fixed 0.3 s and compares at about 2 s sees the first rest at both moments, so a frozen picture
would pass it. Written for the browser check only (no golden file). -/
def longHoldMotion : Motion := { turnMotion with pacing := { firstHold := 2 } }

/-- `turnMotion` paced slowly, with a cycle of about half a minute: a probe that waits for longer
than the cycle shows in the check's duration. Written for the browser check only. -/
def longCycleMotion : Motion :=
  { turnMotion with pacing := { turn := 12, firstHold := 6, hold := 4, idle := 4, lastHold := 4 } }

/-! ### Small motions for the rules -/

/-- `turnMotion` with other steps. -/
def withSteps (steps : Array MotionStep) : Motion := { turnMotion with steps }

/-- `turnMotion` with its key `k` changed. -/
def withKey (k : Nat) (f : Figure → Figure) : Motion :=
  { turnMotion with keys := turnMotion.keys.modify k f }

/-- Whether some problem of the motion is an error whose message contains `s`. -/
def hasError (m : Motion) (s : String) : Bool :=
  m.problems.any fun p => p.severity == .error && (p.message.splitOn s).length > 1

/-- Whether some problem of the motion is a note whose message contains `s`. -/
def hasNote (m : Motion) (s : String) : Bool :=
  m.problems.any fun p => p.severity == .note && (p.message.splitOn s).length > 1

/-- Whether the motion has no error. -/
def noErrors (m : Motion) : Bool := m.problems.all (·.severity == .note)

/-- The title and description of the small motions. -/
def testInfo : Canvas.ShapeInfo := { title := "A test motion", description := "For the checks." }

/-- The motion at the level `.warn`, where what crossfades is a note. -/
def warned (m : Motion) : Motion := { m with checks := .warn }

/-- Five points that appear in the same step, around a point that is always there. -/
def batchMotion : Motion where
  keys :=
    let pts := (List.range 5).toArray.map fun (i : Nat) =>
      Plane.Exact.point (((i : Rat), (1 : Rat)) : Q) |>.accent 1 |>.actor s!"B{i}"
    #[{ items := #[Plane.Exact.point ((0, 0) : Q), Plane.Exact.point ((4, 0) : Q)] },
      { items := #[Plane.Exact.point ((0, 0) : Q), Plane.Exact.point ((4, 0) : Q)] ++ pts }]
  captions := #["Before.", "After."]
  steps := #[{ moves := (List.range 5).toArray.map fun i => (s!"B{i}", .appear) }]
  info := testInfo

/-- A disk whose radius grows from 1 to 2 (`interpolated`), or that becomes a square. -/
def morphMotion (interpolated : Bool) : Motion where
  keys :=
    let after := if interpolated then Plane.Exact.disk ((0, 0) : Q) (2 : Rat)
      else Plane.Exact.polygon [((-1, -1) : Q), (1, -1), (1, 1), (-1, 1)] |>.filled
    #[{ items := #[Plane.Exact.disk ((0, 0) : Q) (1 : Rat) |>.actor "D",
          Plane.Exact.point ((3, 3) : Q), Plane.Exact.point ((-3, -3) : Q)] },
      { items := #[after.actor "D", Plane.Exact.point ((3, 3) : Q),
          Plane.Exact.point ((-3, -3) : Q)] }]
  captions := #["Radius 1.", "After."]
  steps := #[{ moves := #[("D", .morph)] }]
  info := testInfo

/-- A triangle whose top vertex runs along the unit circle from `(1, 0)` to `(0, 1)`, with exact
figures between the keys at the sample fractions (`Motion.between`). -/
def sampledMotion : Motion :=
  let tri := fun (x y : Float) =>
    ({ items := #[Plane.polygon #[⟨-2, -2⟩, ⟨2, -2⟩, ⟨x, y⟩] |>.actor "T",
      Plane.point ⟨-3, -3⟩, Plane.point ⟨3, 3⟩] } : Figure)
  let at_ := fun (q : Rat) =>
    let a := Exact.toFloat q * Plane.pi / 2
    tri a.cos a.sin
  { keys := #[at_ 0, at_ 1], captions := #["Start.", "End."],
    steps := #[{ moves := #[("T", .morph)] }], morphSamples := 4, info := testInfo,
    between := fun j q => if j == 0 then some (at_ q) else none }

/-- An actor with an automatic label that slides next to another label: the placement chosen on
key 0 (above right) is kept on key 1, where it meets the other label. -/
def keptMotion : Motion where
  keys :=
    let other := Plane.Exact.label "M" ((2, 0) : Q) .aboveRight |>.faint
    let actor := fun (p : Q) =>
      (group #[Plane.Exact.point p, Plane.Exact.label "L" p .auto]).actor "L"
    #[{ items := #[other, actor (0, 0), Plane.Exact.point ((-1, 1) : Q)] },
      { items := #[other, actor (2, 0), Plane.Exact.point ((-1, 1) : Q)] }]
  captions := #["L at the origin.", "L slid by 2."]
  steps := #[{ moves := #[("L", Plane.Exact.slideFromTo ((0, 0) : Q) (2, 0))] }]
  info := testInfo

/-- The frame's corners of the small motions below: two faint points. -/
def corners : Array Item := #[Plane.Exact.point ((-3, -3) : Q) |>.faint,
  Plane.Exact.point ((3, 3) : Q) |>.faint]

/-- A motion of two keys from the actor items `a` and `b` and the move `mv` of the actor `X`. -/
def twoKeys (a b : Item) (mv : Move) (allowFull : Bool := false) : Motion where
  keys := #[{ items := corners.push (a.actor "X") }, { items := corners.push (b.actor "X") }]
  captions := #["Before.", "After."]
  steps := #[{ moves := #[("X", mv)], allowFullTurns := allowFull }]
  info := testInfo

/-- A point slid by one to the right, landing `miss` pixels to the right of where the slide
carries it (the frame's scale is that of `twoKeys` with these corners). -/
def missBy (miss : Float) : Motion :=
  let scale := (twoKeys (Plane.point ⟨0, 0⟩) (Plane.point ⟨1, 0⟩)
    (.slide ⟨1, 0⟩)).env.frame.scale
  twoKeys (Plane.point ⟨0, 0⟩) (Plane.point ⟨1 + miss / scale, 0⟩) (.slide ⟨1, 0⟩)

/-- Two overlapping disks drawn in the other order on the second key. -/
def zswap : Motion where
  keys :=
    let a := Plane.Exact.disk ((0, 0) : Q) (1 : Rat) |>.accent 0 |>.actor "A"
    let b := Plane.Exact.disk ((1 / 2, 0) : Q) (1 : Rat) |>.accent 1 |>.actor "B"
    #[{ items := corners ++ #[a, b] }, { items := corners ++ #[b, a] }]
  captions := #["A under B.", "B under A."]
  steps := #[MotionStep.idle]
  info := testInfo

/-- The backdrop of `incidenceMotion`: `turnBackdrop` and a small disk. -/
def incidenceBackdrop : Array Item :=
  turnBackdrop.push (Plane.Exact.disk ((-1 / 2, -1 / 2) : Q) (1 / 5 : Rat) |>.faint
    |>.named "the small disk")

/-- The point `P` on the unit circle, recorded outside the small disk too when `outside`, in the
accent `tone`. -/
def pointRec (p : Q) (outside : Bool) (tone : Nat := 0) : Item :=
  let pt := Plane.Exact.point p |>.accent tone |>.incident .on "the unit circle"
  let pt := if outside then pt.incident .outside "the small disk" else pt
  (group #[pt, Plane.Exact.label "P" p .aboveRight |>.accent tone]).actor "P"

/-- `turnMotion` with a point whose recorded incidences change in the idle step, from key 1 to
key 2, or with `atTurn` in the turn, from key 0 to key 1 (and, with `tone := 1`, whose colour
changes in the turn too). -/
def incidenceMotion (tone : Nat := 0) (atTurn : Bool := false) : Motion :=
  { turnMotion with keys :=
    #[{ items := incidenceBackdrop.push (pointRec (1, 0) false), width := 320 },
      { items := incidenceBackdrop.push (pointRec (0, 1) atTurn tone), width := 320 },
      { items := incidenceBackdrop.push (pointRec (0, 1) true tone), width := 320 }] }

/-- The placement of the first label among the leaves of the actor `id` of a figure. -/
def labelPlacement (fig : Figure) (id : String) : Option Placement :=
  (fig.actor? id).bind fun it => it.leaves.findSome? fun lf => match lf.geom with
    | .label _ _ pl _ => some pl
    | _ => none

/-- The rule checks. -/
def ruleChecks : Array (String × Bool) := Id.run do
  let mut r : Array (String × Bool) := #[]
  r := r.push ("motion: the golden motions are well formed and have no problem",
    golden.all fun (_, m) => decide m.WellFormed && m.problems.isEmpty)
  r := r.push ("motion: a wrong angle is an error",
    hasError (withSteps #[{ moves := #[("P", Plane.Exact.turnAbout ((0, 0) : Q) (1 / 5))] },
      MotionStep.idle]) "does not carry key 0 onto key 1")
  r := r.push ("motion: a wrong centre is an error",
    hasError (withSteps #[{ moves := #[("P", Plane.Exact.turnAbout ((1 / 2, 0) : Q) (1 / 4))] },
      MotionStep.idle]) "does not carry key 0 onto key 1")
  r := r.push ("motion: a turn of an item that did not move is an error",
    hasError (withSteps #[turnMotion.steps[0]!,
      { moves := #[("P", Plane.Exact.turnAbout ((0, 0) : Q) (1 / 4))] }])
      "does not carry key 1 onto key 2")
  let whole := fun (allow : Bool) => withSteps #[turnMotion.steps[0]!,
    { moves := #[("P", Plane.Exact.turnAbout ((0, 0) : Q) 1)], allowFullTurns := allow }]
  r := r.push ("motion: a whole turn is an error unless the step allows it, and then a note",
    hasError (whole false) "is a whole turn or more" && noErrors (whole true) &&
      hasNote (whole true) "the arrival check cannot see the turn")
  r := r.push ("motion: 6/5 of a turn is an error where 1/5 lands; -4/5 lands (direction unseen)",
    let pent := fun (start : Nat) => Plane.polygon ((Array.range 5).map fun i =>
      let a := ((i + start : Nat).toFloat) * 2 * Plane.pi / 5
      (⟨a.cos, a.sin⟩ : Point))
    noErrors (twoKeys (pent 0) (pent 1) (Plane.Exact.turnAbout ((0, 0) : Q) (1 / 5))) &&
      hasError (twoKeys (pent 0) (pent 1) (Plane.Exact.turnAbout ((0, 0) : Q) (6 / 5)))
        "whole turn" &&
      noErrors (twoKeys (pent 0) (pent 1) (Plane.Exact.turnAbout ((0, 0) : Q) (-4 / 5))) &&
      -- the same vertex list after a symmetry turn is refused: the vertices must be turned
      hasError (twoKeys (pent 0) (pent 0) (Plane.Exact.turnAbout ((0, 0) : Q) (1 / 5)))
        "does not carry")
  r := r.push ("motion: an unseen turn of the turn's centre, or of a rigid body's part, is no note",
    let d := Plane.Exact.disk ((0, 0) : Q) (1 / 2 : Rat)
    let quarter := Plane.Exact.turnAbout ((0, 0) : Q) (1 / 4)
    let body : Motion :=
      { keys := #[{ items := corners ++
            #[d.actor "C", Plane.Exact.point ((2, 0) : Q) |>.actor "R"] },
          { items := corners ++ #[d.actor "C", Plane.Exact.point ((0, 2) : Q) |>.actor "R"] }],
        captions := #["Before.", "After."], info := testInfo,
        steps := #[{ moves := #[("C", quarter), ("R", quarter)] }] }
    noErrors (twoKeys d d (Plane.Exact.turnAbout ((0, 0) : Q) (1 / 3))) &&
      !hasNote (twoKeys d d (Plane.Exact.turnAbout ((0, 0) : Q) (1 / 3))) "cannot see" &&
      noErrors body && !hasNote body "cannot see")
  r := r.push ("motion: a slide that misses by 0.02 px is an error; by 0.005 px it lands",
    hasError (missBy 0.02) "does not carry key 0 onto key 1" && noErrors (missBy 0.005))
  r := r.push ("motion: a polygon with only a later vertex out of place is an error",
    let tri := fun (z : Float) => Plane.polygon #[⟨0, 0⟩, ⟨1, 0⟩, ⟨0, z⟩]
    let slid := Plane.polygon #[⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 1.1⟩]
    hasError (twoKeys (tri 1) slid (.slide ⟨1, 0⟩)) "does not carry" &&
      noErrors (twoKeys (tri 1) (Plane.polygon #[⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 1⟩])
        (.slide ⟨1, 0⟩)))
  r := r.push ("motion: a disk whose radius changes under a slide is an error",
    hasError (twoKeys (Plane.Exact.disk ((0, 0) : Q) (1 : Rat))
      (Plane.Exact.disk ((1, 0) : Q) (6 / 5 : Rat)) (.slide ⟨1, 0⟩)) "changes its radius")
  r := r.push ("motion: a key that draws its items in another order is an error",
    hasError zswap "draws its items in another order" && hasError zswap "at the rest on key 1")
  r := r.push ("motion: a motion without a title or description is an error under fail",
    hasError { turnMotion with info := {} } "no title" &&
      hasError { turnMotion with info := { title := "t" }, captions := #["", "", ""] }
        "neither a description nor captions" &&
      noErrors { turnMotion with info := { title := "t" } } &&
      noErrors (warned { turnMotion with info := {} }))
  let missing : Motion := { turnMotion with keys := turnMotion.keys.pop }
  r := r.push ("motion: a missing key is an error, and the motion is not well formed",
    !decide missing.WellFormed && hasError missing "needs one key more than steps")
  r := r.push ("motion: captions that are not one per key are an error",
    hasError { turnMotion with captions := #["one"] } "1 captions for 3 keys")
  r := r.push ("motion: a poster that is not a key is an error",
    hasError { turnMotion with poster := 3 } "the poster is key 3")
  r := r.push ("motion: a turn of an actor missing from the next key is an error",
    hasError (withKey 1 fun f => { f with items := f.items.pop }) "has a turn but is not in key 1")
  r := r.push ("motion: an appearance of an actor already there is an error",
    hasError (withSteps #[{ moves := #[("P", .appear)] }, MotionStep.idle])
      "appears but is already")
  r := r.push ("motion: moves in an idle step are an error",
    hasError (withSteps #[turnMotion.steps[0]!,
      { MotionStep.idle with moves := #[("P", .vanish)] }]) "is idle but declares moves")
  r := r.push ("motion: two moves of one actor in a step are an error",
    hasError (withSteps #[{ moves := #[("P", Plane.Exact.turnAbout ((0, 0) : Q) (1 / 4)),
      ("P", .morph)] }, MotionStep.idle]) "has more than one move")
  r := r.push ("motion: a line in a turning actor is an error",
    let withLine := fun (p : Q) => (group #[Plane.Exact.point p |>.incident .on "the unit circle",
      Plane.Exact.line ((0, 0) : Q) p |>.faint]).actor "P"
    hasError { turnMotion with keys := turnMotion.keys.mapIdx fun k f =>
      { f with items := f.items.pop.push (withLine (if k == 0 then (1, 0) else (0, 1))) } }
      "cannot turn")
  -- what changes without a move crossfades, with a note
  let q := (group #[Plane.Exact.point ((0, 1) : Q) |>.accent 0 |>.incident .on "the unit circle",
    Plane.Exact.label "Q" ((0, 1) : Q) .aboveRight |>.accent 0]).actor "P"
  let relabelled := withKey 2 fun f => { f with items := f.items.pop.push q }
  r := r.push ("motion: an actor that changes without a move is an error under fail",
    hasError relabelled "P changes without a declared move" &&
      (match relabelled.svg? with | .error _ => true | .ok _ => false))
  r := r.push ("motion: under warn it is a note, crossfaded in two layers",
    noErrors (warned relabelled) && hasNote (warned relabelled) "P changes without" &&
      ((warned relabelled).plan.layers.filter (·.version.actor == some "P")).size == 2)
  r := r.push ("motion: an actor that leaves or comes without vanish or appear is an error",
    let gone := withKey 2 fun f => { f with items := f.items.pop }
    let gone := { gone with steps := #[turnMotion.steps[0]!, {}] }
    hasError gone "leaves without a declared disappearance" &&
      hasNote (warned gone) "leaves without a declared disappearance")
  let o := Plane.Exact.label "O" ((0, 0) : Q) .below |>.faint
  let moved := withKey 2 fun f => { f with items := f.items.modify 2 fun _ => o }
  r := r.push ("motion: an item without an id that changes is a note",
    noErrors moved && hasNote moved "1 items without an id fade out and 1 fade in")
  let wrong := withSteps #[{ moves := #[("P", Plane.Exact.turnAbout ((0, 0) : Q) (1 / 5))] },
    MotionStep.idle]
  r := r.push ("motion: fail is the default; notes alone never stop a build, an error does",
    turnMotion.checks == .fail && !moved.problemsFail && wrong.problemsFail &&
      (match wrong.svg? with | .error _ => true | .ok _ => false) &&
      (match turnMotion.svg? with
        | .ok svg => svg == turnMotion.toSvgUnchecked
        | .error _ => false) &&
      !(warned wrong).problemsFail &&
      ({ turnMotion with checks := .ignore, poster := 9 } : Motion).checkMessages.isEmpty)
  r := r.push ("motion: a declared turn that misses its key is not animated as a turn",
    ((warned wrong).plan.layers.filter (·.version.actor == some "P")).size == 2)
  r := r.push ("motion: the angles of the chain at the keys are the exact sums of the turns",
    (List.range 4).map (twoCentresMotion.keyAngle "A") == [0, -90, -270, -270] &&
      (List.range 4).map (fun k => Exact.toFloat (-(360 * twoCentresMotion.turnSum "A" k))) ==
        [0, -90, -270, -270] &&
      (List.range 4).map (twoCentresMotion.keyAngle "S") == [0, 0, 0, 0])
  -- kept placements
  let k0 := keptMotion.keyFigure 0
  let k1 := keptMotion.keyFigure 1
  let own := (commonView keptMotion.keys)[1]!.autoPlaced
  r := r.push ("motion: an automatic label is placed on the actor's first key and kept",
    labelPlacement k0 "L" == labelPlacement k1 "L" && labelPlacement k1 "L" != some .auto &&
      labelPlacement own "L" != labelPlacement k1 "L")
  r := r.push ("motion: a kept placement must pass the checks on every key",
    own.problems.isEmpty && hasError keptMotion "key 1:")
  return r

/-! ### The layout -/

/-- The elements of a tree named `name`, at most `fuel` deep, in document order. -/
def elements (name : String) : Nat → Node → Array Node
  | 0, _ => #[]
  | _, .text _ => #[]
  | fuel + 1, n@(.element m _ cs) =>
    (if m == name then #[n] else #[]) ++ cs.flatMap (elements name fuel)

/-- The value of an attribute of an element (empty when it has none). -/
def attrOf (n : Node) (key : String) : String :=
  match n with
  | .element _ as _ => (Smil.attr? as key).getD ""
  | _ => ""

/-- The number of `animate` elements of the tree animating `attr`. -/
def animCount (root : Node) (attr : String) : Nat :=
  ((elements "animate" 256 root) ++ (elements "animateTransform" 256 root)).filter
    (attrOf · "attributeName" == attr) |>.size

/-- The groups of the tree whose own `animateTransform` holds, among their descendants, the actors
`ids`. -/
def chainHolding (root : Node) (ids : List String) : Nat :=
  ((elements "g" 256 root).filter fun g => match g with
    | .element _ _ cs =>
      cs.any (fun c => match c with | .element "animateTransform" .. => true | _ => false) &&
        let actors := (elements "g" 256 g).map (attrOf · "data-pilean-actor")
        ids.all (actors.contains ·)
    | _ => false).size

/-- The paths of a drawing, at most `fuel` deep (its groups' transforms left out). -/
def allPaths : Nat → Canvas.Shape → Array Path
  | 0, _ => #[]
  | _, .path q .. => #[q]
  | _, .text .. => #[]
  | fuel + 1, .group cs .. => cs.flatMap (allPaths fuel)
  | fuel + 1, .tagged _ c => allPaths fuel c

/-- The layout checks. -/
def layoutChecks : Array (String × Bool) := Id.run do
  let mut r : Array (String × Bool) := #[]
  let root := twoCentresMotion.svgRootUnchecked
  -- the triangle's three actors in one chain: one group holds them all, with one turn
  r := r.push ("motion: actors that move alike share one chain",
    chainHolding root ["T1", "T2", "T3"] == 1 &&
      (twoCentresMotion.plan.runs.flatten.any fun sub => sub.size == 3))
  r := r.push ("motion: a point turned about two centres sits in two groups, the earliest inner",
    let rotates := (elements "animateTransform" 256 root).filter (attrOf · "type" == "rotate")
    let centreOf := fun (a : Node) =>
      " ".intercalate ((((attrOf a "values").splitOn ";").getD 0 "").splitOn " " |>.drop 1)
    let fr := twoCentresMotion.env.frame
    let o := pointText (quantPoint (fr.toScreen ⟨0, 0⟩))
    let c := pointText (quantPoint (fr.toScreen ⟨1, 1⟩))
    -- in document order, leaving out the counter-rotations of upright leaves (about their own
    -- anchors): the triangle's turn about O, then A's turn about C (the outer group), then A's
    -- turn about O (the inner group)
    (rotates.toList.map centreOf).filter (fun x => x == o || x == c) == [o, c, o])
  r := r.push ("motion: a point's marker and its label share one counter-rotation",
    ((elements "g" 256 turnMotion.svgRootUnchecked).filter
      (attrOf · "data-pilean-upright" != "")).size
      == 1)
  let broot := batchMotion.svgRootUnchecked
  r := r.push ("motion: points that appear in the same step share one opacity animation",
    animCount broot "opacity" == 2 && batchMotion.problems.isEmpty)
  -- morphs
  let grow := morphMotion true
  r := r.push ("motion: a disk whose radius changes is a morph of its path data",
    grow.problems.isEmpty && animCount grow.svgRootUnchecked "d" ≥ 1 &&
      (grow.plan.layers.filter (·.version.actor == some "D")).size == 1)
  -- the baked disk half way through the morph is the disk of the radius half way
  let p := grow.plan
  let seg := grow.timeline.segments.find? (·.kind == .move 0)
  r := r.push ("motion: the baked disk of a morph is the disk of the interpolated radius",
    match seg with
    | some s =>
      let t := Exact.toFloat (s.start + s.dur / 2)
      -- the eased progress at the written key times (within 1e-7 of the standard easing's 0.5)
      let f := (p.clock.locate t).2
      let fr := p.env.frame
      let expected := Canvas.circle (fr.toScreen ⟨0, 0⟩) (fr.scale * (1 + f))
      (f - 0.5).abs < 1e-7 && (allPaths 64 (p.figureAtUnchecked t)).any fun q =>
        q.cmds.size == expected.cmds.size &&
        (q.cmds.zip expected.cmds).all fun (a, b) =>
          (a.points.zip b.points).all fun (x, y) => x.dist y < 1e-9
    | none => false)
  let square := morphMotion false
  r := r.push ("motion: a morph that cannot be interpolated is an error; under warn it crossfades",
    hasError square "cannot be interpolated" && noErrors (warned square) &&
      ((warned square).plan.layers.filter (·.version.actor == some "D")).size == 2)
  let late : Motion :=
    { keys := #[0, 1, 2].map fun (k : Nat) =>
        let c : Q := if k == 0 then (0, 0) else (1, 0)
        let r : Rat := if k == 2 then 2 else 1
        { items := #[Plane.Exact.disk c r |>.actor "D", Plane.Exact.point ((4, 4) : Q),
            Plane.Exact.point ((-3, -3) : Q)] },
      captions := #["", "", ""], info := testInfo, checks := .warn,
      steps := #[{ moves := #[("D", Plane.Exact.slideFromTo ((0, 0) : Q) (1, 0))] },
        { moves := #[("D", .morph)] }] }
  r := r.push ("motion: a morph after a slide of its layer crossfades under warn, with a note",
    noErrors late && hasNote late "cannot be interpolated" &&
      (late.plan.layers.filter (·.version.actor == some "D")).size == 2)
  r := r.push ("motion: a morph with figures between its keys is sampled",
    sampledMotion.problems.isEmpty && sampledMotion.samplesOf sampledMotion.keysOf 0 == 4 &&
      sampledMotion.timeline.segments.size ==
        (Timeline.build sampledMotion.animSteps sampledMotion.pacing).segments.size + 3 &&
      animCount sampledMotion.svgRootUnchecked "d" == 1)
  return r

/-! ### The writer against the baker -/

/-- The transform of a value of an `animateTransform` of `type`. -/
def transformOf (type : String) (v : Array Float) : Affine :=
  if type == "rotate" then rotAbout ⟨v.getD 1 0, v.getD 2 0⟩ (v.getD 0 0)
  else Affine.translate (v.getD 0 0) (v.getD 1 0)

/-- A point written as `x y`. -/
def pointOf (s : String) : Point :=
  match (s.splitOn " ").map Raster.parseNumber? with
  | [some x, some y] => ⟨x, y⟩
  | _ => ⟨0, 0⟩

/-- What the written tree shows at the time `t`, read with `Smil.valueAt` alone: every element
with `data-pilean-actor` (its anchor) or `data-pilean-upright` (its anchor) in document order,
with the page point its anchor is drawn at, its opacity, and the whole transform its content is
under (`none` where an animation does not evaluate), at most `fuel` deep. -/
def shown (t : Float) : Nat → Affine → Float → Node →
    Option (Array (String × Point × Float × Affine))
  | 0, _, _, _ => some #[]
  | _, _, _, .text _ => some #[]
  | fuel + 1, M, o, .element _ attrs cs => do
    let mut M := M
    let mut o := o
    for c in cs do
      if let .element n as _ := c then
        if n == "animateTransform" then
          let v ← Smil.valueAt c t
          M := M.comp (transformOf ((Smil.attr? as "type").getD "") v)
        else if n == "animate" && Smil.attr? as "attributeName" == some "opacity" then
          o := o * (← Smil.valueAt c t).getD 0 1
    let upright := Smil.attr? attrs "data-pilean-upright"
    let own := match Smil.attr? attrs "data-pilean-actor", upright with
      | some id, _ =>
        let a := pointOf ((Smil.attr? attrs "data-pilean-anchor").getD "")
        #[(s!"actor {id}", M.apply a, o, M)]
      | none, some a => #[("upright", M.apply (pointOf a), o, M)]
      | none, none => #[]
    let rest ← cs.mapM (shown t fuel M o)
    return own ++ rest.flatten

/-- Whether `s` contains `t`. -/
def has (s t : String) : Bool := (s.splitOn t).length > 1

/-- The live group of a motion's SVG. -/
def liveGroup (m : Motion) : Node :=
  ((elements "g" 256 m.svgRootUnchecked).find? (attrOf · "class" == Animation.liveClass)).getD
    (.text "")

/-- Whether two transforms agree within `tol` in every coefficient. -/
def affineNear (a b : Affine) (tol : Float) : Bool :=
  [(a.a, b.a), (a.b, b.b), (a.c, b.c), (a.d, b.d), (a.e, b.e), (a.f, b.f)].all fun (x, y) =>
    (x - y).abs < tol

/-- The times of the agreement checks: 50 through the cycle. -/
def sampleTimes (cycle : Rat) : List Rat :=
  (List.range 50).map fun i => cycle * (i * 100 + 37 : Nat) / 5000

/-- Whether, at 50 times through the cycle, the written tree (`shown`, read with `Smil.valueAt`)
shows what the baker has (`MotionPlan.markersAt`): as many actors and upright groups as the plan
declares (its layers with an actor, and their `uprights`), each anchor within `1e-6` px, each
opacity within `1e-6`, and each whole transform within `1e-6` in every coefficient (so an upright
leaf is translated, not turned, on both sides). -/
def agrees (m : Motion) : Bool :=
  let p := m.plan
  let live := liveGroup m
  let actors := (p.layers.filter fun L => L.version.actor.isSome).size
  let ups := (p.layers.map (·.uprights.size)).foldl (· + ·) 0
  (sampleTimes p.timeline.cycle).all fun tr =>
    let t := Exact.toFloat tr
    match shown t 256 Affine.id 1 live with
    | none => false
    | some written =>
      let baked := p.markersAt t
      (written.filter (·.1 != "upright")).size == actors &&
        (written.filter (·.1 == "upright")).size == ups &&
        written.size == baked.size &&
        (written.zip baked).all fun ((n, q, o, M), (n', q', o', M')) =>
          n == n' && q.dist q' < 1e-6 && (o - o').abs < 1e-6 && affineNear M M' 1e-6

/-- Where the motion's model puts the anchor of the actor `id` at the exact time `t`, computed
apart from the plan: its first leaf's first anchor on the key `first`, then each declared turn or
slide of the steps from `first` on, the step under way by the eased fraction of the unsplit
timeline (`Timeline.locate`), a turn by `-360 q` degrees about the page point of its centre, a
slide by the page image of its vector. -/
def modelAnchor (m : Motion) (id : String) (first : Nat) (t : Rat) : Option Point := do
  let K := m.keysOf
  let f := K.env.frame
  let lf ← ((K.figure first).actor? id).bind (·.leaves[0]?)
  let a0 ← (anchors f K.env.style lf.geom)[0]?
  let tl := m.baseTimeline
  let (kind, e) := tl.locate t
  let (key, frac) := match kind with
    | .rest k => (k, (0 : Float))
    | .move j => (j, e)
    | .seamIn => (0, 0)
    | .seamOut => (m.keys.size - 1, 0)
  let step := fun (pt : Point) (j : Nat) (x : Float) => match m.moveOf j id with
    | some (.turn c q) =>
      let c' := f.toScreen c
      let θ := -(360 * Exact.toFloat q) * x * Plane.pi / 180
      let d := pt - c'
      (⟨c'.x + d.x * θ.cos - d.y * θ.sin, c'.y + d.x * θ.sin + d.y * θ.cos⟩ : Point)
    | some (.slide v) => pt + (⟨f.scale * v.x * x, -(f.scale * v.y) * x⟩ : Point)
    | _ => pt
  let p := (List.range (key - first)).foldl (fun pt i => step pt (first + i) 1) a0
  return if frac > 0 then step p key frac else p

/-- Whether the baker (`MotionPlan.chainAt` on each actor layer's anchor) agrees with the model
computed apart from the plan (`modelAnchor`) within `1e-3` px (the written numbers are rounded
to 4 and 6 decimals), at the 50 times, for every actor layer fully shown then, outside sampled
morph steps (whose turns follow the eased motion piecewise linearly, `sampledAgrees`). -/
def modelAgrees (m : Motion) : Bool :=
  let p := m.plan
  let K := m.keysOf
  let tl := m.baseTimeline
  (sampleTimes p.timeline.cycle).all fun tr =>
    let t := Exact.toFloat tr
    let sampled := match (tl.locate tr).1 with
      | .move j => m.samplesOf K j > 1
      | _ => false
    sampled || p.layers.all fun L =>
      match L.version.actor, L.anchor with
      | some id, some a =>
        p.opacityAt L t * p.seamAt t < 1 ||
          (modelAnchor m id L.version.first tr).any fun q =>
            ((p.chainAt L t).apply a).dist q < 1e-3
      | _, _ => true

/-- A disk that grows through exact figures between its keys while a point turns a quarter in the
same step: the step is sampled (`morphSamples = 4`). -/
def sampledTurn : Motion :=
  let fig := fun (q : Rat) =>
    let a := Exact.toFloat q * Plane.pi / 2
    let items := corners ++ #[Plane.disk ⟨0, 0⟩ (1 + Exact.toFloat q) |>.actor "D",
      Plane.point ⟨2.5 * a.cos, 2.5 * a.sin⟩ |>.actor "R"]
    ({ items } : Figure)
  { keys := #[fig 0, fig 1], captions := #["Start.", "End."], info := testInfo,
    steps := #[{ moves := #[("D", .morph), ("R", Plane.Exact.turnAbout ((0, 0) : Q) (1 / 4))] }],
    morphSamples := 4, between := fun j q => if j == 0 then some (fig q) else none }

/-- The largest difference, at 200 times through the sampled step of `sampledTurn`, between the
written angle of the turn (`Smil.valueAt`) and the eased angle of the step (`-90` times the
step's easing at the fraction of its time), in degrees. -/
def sampledError : Float :=
  let p := sampledTurn.plan
  let base := Timeline.build sampledTurn.animSteps sampledTurn.pacing
  match base.segments.find? (·.kind == .move 0) with
  | none => 1e9
  | some s =>
    -- the turn about the origin (not the point's counter-rotation, about its own anchor)
    let o := pointText (quantPoint (p.env.frame.toScreen ⟨0, 0⟩))
    let rot := (elements "animateTransform" 256 sampledTurn.svgRootUnchecked).find? fun a =>
      attrOf a "type" == "rotate" && (attrOf a "values").startsWith s!"0 {o};"
    match rot with
    | none => 1e9
    | some a =>
      (List.range 201).foldl (init := 0) fun acc i =>
        let x := i.toFloat / 200
        let t := Exact.toFloat s.start + x * Exact.toFloat s.dur
        let written := ((Smil.valueAt a t).bind (·[0]?)).getD 1e9
        max acc (written - (-90) * s.easing.eval x).abs

/-- The largest difference, in degrees, between the written angle of the turn of `sampledTurn` and
the eased angle at the times where the step's easing has done a quarter, a half and three
quarters of the step (found here by 64 halvings of `Easing.eval`): there the piecewise linear
motion of a sampled step meets the eased one. -/
def sampledKnotError : Float :=
  let base := Timeline.build sampledTurn.animSteps sampledTurn.pacing
  let p := sampledTurn.plan
  let o := pointText (quantPoint (p.env.frame.toScreen ⟨0, 0⟩))
  let rot := (elements "animateTransform" 256 sampledTurn.svgRootUnchecked).find? fun a =>
    attrOf a "type" == "rotate" && (attrOf a "values").startsWith s!"0 {o};"
  match base.segments.find? (·.kind == .move 0), rot with
  | some s, some a =>
    [0.25, 0.5, 0.75].foldl (init := 0) fun acc (y : Float) =>
      let x := Id.run do
        let mut lo : Float := 0
        let mut hi : Float := 1
        for _ in [0:64] do
          let mid := (lo + hi) / 2
          if s.easing.eval mid < y then lo := mid else hi := mid
        return (lo + hi) / 2
      let t := Exact.toFloat s.start + x * Exact.toFloat s.dur
      let written := ((Smil.valueAt a t).bind (·[0]?)).getD 1e9
      max acc (written - (-90) * y).abs
  | _, _ => 1e9

/-- The checks of the writer against the baker and of the outputs. -/
def outputChecks : Array (String × Bool) := Id.run do
  let mut r : Array (String × Bool) := #[]
  let all := golden ++ #[("batch", batchMotion), ("morph", morphMotion true),
    ("crossfade", morphMotion false), ("sampled", sampledMotion), ("kept", keptMotion)]
  for (name, m) in all ++ #[("sampled turn", sampledTurn)] do
    r := r.push (s!"motion {name}: the written tree shows what the baker draws, at 50 times",
      agrees m)
    r := r.push (s!"motion {name}: the baker follows the model, computed apart, at 50 times",
      modelAgrees m)
    let svg := m.toSvgUnchecked
    r := r.push (s!"motion {name}: the SVG is inert, keeps the invariant and runs on one clock",
      Svg.isInert svg && Smil.invariantProblem? 256 m.svgRootUnchecked == none &&
        Smil.clockProblem? m.svgRootUnchecked == none && svg == m.toSvgUnchecked)
  r := r.push ("motion: a turn in a sampled step meets the eased angle at the samples' times and \
      follows it within 90/4 degrees between them",
    sampledTurn.problems.isEmpty && sampledTurn.samplesOf sampledTurn.keysOf 0 == 4 &&
      sampledError < 90 / 4 && sampledKnotError < 1e-3)
  -- the rest tolerance: paths alone, then texts
  let paths : Figure :=
    { items := #[Plane.circle ⟨0, 0⟩ 1, Plane.point ⟨1.5, 1.5⟩,
      Plane.point ⟨-1.5, -1.5⟩] }
  let still := drawnOf 256 Affine.id 1 paths.draw
  let shifted := fun (dx : Float) => drawnOf 256 (Affine.translate dx 0) 1 paths.draw
  r := r.push ("rest check: a drawing 0.25 px off is refused, 0.03 px off passes",
    (drawingDiff (shifted 0.25) still).isSome && (drawingDiff (shifted 0.03) still).isNone)
  -- a circle of radius 100 px: its allowance is 0.05 + 5.5e-4 · 100 = 0.105 px
  let ring := fun (dx : Float) =>
    #[Drawn.path "p" ((Canvas.circle ⟨200 + dx, 200⟩ 100).flatten 0.01)]
  r := r.push ("rest check: a circle of radius 100 px 0.2 px off is refused, 0.04 px off passes",
    (drawingDiff (ring 0.2) (ring 0)).isSome && (drawingDiff (ring 0.04) (ring 0)).isNone)
  let labelled : Figure := { paths with items := paths.items.push (Plane.label "T" ⟨0, 0⟩) }
  let lstill := drawnOf 256 Affine.id 1 labelled.draw
  let textMoved := fun (dx turn : Float) => lstill.map fun
    | .text k a t => Drawn.text k (a + (⟨dx, 0⟩ : Point)) (t + turn)
    | d => d
  r := r.push ("rest check: a text 0.2 px off or turned by 0.01 radians is refused",
    (lstill.any fun | .text .. => true | _ => false) &&
      (drawingDiff (textMoved 0.2 0) lstill).isSome &&
      (drawingDiff (textMoved 0 0.01) lstill).isSome &&
      (drawingDiff (textMoved 0.02 0) lstill).isNone)
  let native : Motion :=
    { turnMotion with keys := turnMotion.keys.map ({ · with textAsShapes := false }) }
  r := r.push ("motion: a motion written with SVG text elements passes its checks",
    native.problems.isEmpty && has native.toSvgUnchecked "<text")
  -- recorded incidences describe a key, not the drawing
  let inc := incidenceMotion
  let live := Svg.render 0 (liveGroup inc)
  r := r.push ("motion: an actor whose recorded incidences change is one actor, written plain",
    inc.problems.isEmpty && (inc.plan.layers.filter (·.version.actor == some "P")).size == 1 &&
      !has live "outside the small disk" && !has live "on the unit circle" &&
      has (inc.keyFigure 2).toSvg "on the unit circle, outside the small disk")
  let incTurn := incidenceMotion (atTurn := true)
  r := r.push ("motion: records that change across a turn do not stop the turn from landing",
    incTurn.problems.isEmpty &&
      (incTurn.plan.layers.filter (·.version.actor == some "P")).size == 1)
  r := r.push ("motion: an item without an id whose records change is not crossfaded",
    let o := fun (outside : Bool) =>
      let pt := Plane.Exact.point ((0, -1) : Q) |>.faint |>.incident .on "the unit circle"
      if outside then pt.incident .outside "the small disk" else pt
    let m := { inc with keys := inc.keys.mapIdx fun k f =>
      { f with items := f.items.push (o (k == 2)) } }
    m.problems.isEmpty && !hasNote (warned m) "items without an id")
  r := r.push ("motion: an actor whose look changes in anything else is still refused",
    hasError (incidenceMotion 1) "does not carry key 0 onto key 1")
  r := r.push ("motion: the base title drops exactly the recorded words",
    baseTitle #[(.on, "c"), (.outside, "d")] "A, on c, outside d" == "A" &&
      baseTitle #[(.on, "c")] "on c" == "" && baseTitle #[(.on, "c")] "A, on b" == "A, on b")
  r := r.push ("motion: a plan whose counter-rotations are off is refused by the writer check",
    let p := turnMotion.plan
    let bad : MotionPlan := { p with layers := p.layers.map fun L =>
      { L with uprights := L.uprights.map fun u =>
        { u with values := u.values.map fun v => #[2 * v.getD 0 0, v.getD 1 0, v.getD 2 0] } } }
    (Motion.writerProblems p).isEmpty && !(Motion.writerProblems bad).isEmpty)
  r := r.push ("motion: the long-hold fixture is checked and holds its first key for 2 s",
    noErrors longHoldMotion && longHoldMotion.svg?.toOption.isSome &&
      longHoldMotion.timeline.cycle == turnMotion.timeline.cycle + 2 - 1.2)
  for (name, m) in golden do
    r := r.push (s!"motion {name}: at every rest the baker draws the key still, every element",
      (m.restProblems m.keysOf m.plan).isEmpty &&
        (match m.svg? with | .ok svg => svg == m.toSvgUnchecked | .error _ => false))
    r := r.push (s!"motion {name}: the stills are the key figures, byte for byte",
      (List.range m.keys.size).all fun k =>
        (m.keyFigure k).toSvg == ((commonView m.keys)[k]!).toSvg)
    let a := m.toAnimationUnchecked
    r := r.push (s!"motion {name}: the animation is one cycle, its poster the poster key's rest",
      (a.duration - Exact.toFloat m.timeline.cycle).abs < 1e-12 &&
        a.posterTime == some (Exact.toFloat (m.timeline.restTime m.poster)) &&
        a.width == (m.keyFigure 0).pixelSize.1 && a.height == (m.keyFigure 0).pixelSize.2)
  return r

/-! ### Rests of their own, fades in part of a step or a rest, and keys that are not stills -/

/-- `turnMotion` with its turn on a steep curve (`0.83 0 0.17 1`) and a mark that vanishes in
the first 0.6 of that step: the part of the curve over `[0, 0.6]` is no timing curve, so it is
halved (`easedParts`), and the turn is checked inside each part and at every boundary. -/
def steepMotion : Motion :=
  let mark := Plane.Exact.point ((-1, -1) : Q) |>.accent 2 |>.actor "X"
  { turnMotion with
    keys := turnMotion.keys.mapIdx fun k f => if k == 0 then { f with items := f.items.push mark }
      else f
    steps := #[
      { moves := #[("P", Plane.Exact.turnAbout ((0, 0) : Q) (1 / 4)), ("X", .vanish)],
        windows := #[("X", .fractions 0 (3 / 5))], easing := some (.spline 0.83 0 0.17 1) },
      MotionStep.idle] }

/-- `announceMotion` with other key options. -/
def announceWith (f : Array MotionKey → Array MotionKey) : Motion :=
  { announceMotion with keyOptions := f announceMotion.keyOptions }

/-- `announceMotion` with other steps. -/
def announceSteps (f : Array MotionStep → Array MotionStep) : Motion :=
  { announceMotion with steps := f announceMotion.steps }

/-- The opacity at the time `t` of the `n`-th layer of the actor `id` (in the order of the
document) in the written tree `root`, read with `Smil.valueAt` alone (`shown`), the seam's
included. -/
def writtenOpacity (root : Node) (id : String) (n : Nat) (t : Float) : Option Float := do
  let ms ← shown t 256 Affine.id 1 root
  let mine := ms.filter (·.1 == s!"actor {id}")
  return (← mine[n]?).2.2.1

/-- The tree with every opacity animation of a group that holds the actor `id` set to `0` at
every boundary, at most `fuel` deep: a fade of the actor that never starts. -/
def silence (id : String) : Nat → Node → Node
  | 0, n => n
  | _, .text t => .text t
  | fuel + 1, .element name attrs cs =>
    let holds := (elements "g" 256 (.element name attrs cs)).any fun g =>
      attrOf g "data-pilean-actor" == id
    let cs := cs.map fun c => match c with
      | .element "animate" as ks =>
        if holds && Smil.attr? as "attributeName" == some "opacity" then
          let vals := ((Smil.attr? as "values").getD "").splitOn ";"
          .element "animate" (as.map fun (k, v) =>
            if k == "values" then (k, ";".intercalate (vals.map fun _ => "0")) else (k, v)) ks
        else c
      | _ => silence id fuel c
    .element name attrs cs

/-- Whether `x` and `y` are within `tol`. -/
def near (x y tol : Float) : Bool := (x - y).abs ≤ tol

/-- The checks of rests of their own, fades in part of a step or of a rest, and keys that are not
stills, with a mutation of each rule caught by its named check. -/
def featureChecks : Array (String × Bool) := Id.run do
  let mut r : Array (String × Bool) := #[]
  let m := announceMotion
  let base := m.baseTimeline
  let rest := fun (k : Nat) => kindDur base (.rest k)
  r := r.push ("motion rests: a key's own rest wins; the others rest as the pacing says",
    rest 0 == m.pacing.firstHold && rest 1 == 9 / 10 && rest 2 == 3 / 10 &&
      rest 3 == m.pacing.lastHold &&
      kindDur (announceWith (·.set! 0 { rest := some 2 })).baseTimeline (.rest 0) == 2 &&
      kindDur (announceWith (·.set! 3 { rest := some (1 / 2) })).baseTimeline (.rest 3) == 1 / 2)
  r := r.push ("motion rests: a rest of its own of 0 s is an error (mutation)",
    hasError (announceWith (·.set! 3 { rest := some 0 })) "is not longer than zero" &&
      hasError (announceWith (·.set! 0 { rest := some (-1) })) "is not longer than zero")
  -- the windows
  r := r.push ("motion windows: a window outside its step or rest is an error (mutation)",
    hasError (announceSteps (·.modify 1 fun s => { s with windows := #[("mB", .fractions (1 / 2)
      (6 / 5))] })) "runs outside the step" &&
      hasError (announceWith (·.modify 1 fun o => { o with fades := #[("mA", .vanish,
        .seconds 0 2), ("mB", .appear, .seconds (1 / 5) (2 / 5))] })) "runs outside the rest" &&
      hasError (announceSteps (·.modify 1 fun s => { s with windows := #[("mB", .fractions (1 / 2)
        (1 / 2))] })) "ends where it starts")
  r := r.push ("motion windows: two windows on one actor in a step or a rest are an error \
      (mutation)",
    hasError (announceSteps (·.modify 1 fun s => { s with windows := s.windows.push ("mB",
      .first (1 / 10)) })) "more than one window" &&
      hasError (announceWith (·.modify 1 fun o => { o with fades := o.fades.push ("mA", .appear,
        .seconds (1 / 2) (3 / 5)) })) "fades more than once")
  r := r.push ("motion windows: a window on a turn, or on an actor without a move, is an error",
    hasError (announceSteps (·.modify 1 fun s => { s with windows := #[("T", .first (1 / 2))] }))
      "only an appearance or a disappearance runs in part of a step" &&
      hasError (announceSteps (·.modify 0 fun s => { s with windows := #[("mA", .first (1 / 2))] }))
      "has a window but no move")
  r := r.push ("motion rest fades: an actor that fades during a rest and moves in the step before \
      it is an error (mutation)",
    -- the ring at A turns with the triangle in step 1 and still vanishes during the rest on key 1
    let moved := { m with steps := m.steps.modify 0 fun s =>
      { s with moves := s.moves.push ("mA", Plane.Exact.turnAbout ((0, 0) : Q) (1 / 4))} }
    hasError moved "fades during the rest and also has a turn in step 1")
  r := r.push ("motion rest fades: fades that run to the end of the rest, overlapping windows, and \
      fades that contradict the keys are errors",
    hasError (announceWith (·.modify 1 fun o => { o with fades := #[("mA", .vanish,
      .seconds 0 (1 / 5)), ("mB", .appear, .last (1 / 5))] })) "never shown still" &&
      hasError (announceWith (·.modify 1 fun o => { o with fades := #[("mA", .vanish,
        .seconds 0 (1 / 5)), ("mB", .appear, .seconds (1 / 5) (17 / 20))] }))
        "less than 1/10 s" &&
      hasError (announceWith (·.modify 1 fun o => { o with fades := #[("mA", .vanish,
        .seconds 0 (3 / 10)), ("mB", .appear, .seconds (1 / 5) (2 / 5))] })) "overlap" &&
      hasError (announceWith (·.modify 1 fun o => { o with fades := #[("mA", .appear,
        .seconds 0 (1 / 5)), ("mB", .appear, .seconds (1 / 5) (2 / 5))] }))
        "appears but is not in key 1" &&
      hasError (announceWith (·.modify 0 fun o => { o with fades := #[("mA", .vanish,
        .first (1 / 5))] })) "no key before key 0" &&
      -- without its fades, the rings come and go without a declared move
      hasError (announceWith (·.modify 1 fun o => { o with fades := #[] }))
        "leaves without a declared disappearance")
  r := r.push ("motion stills: a poster that is not a still is an error and stops the motion at \
      every level (mutation)",
    hasError { m with poster := 2 } "which is not a still" &&
      (PILean.Trust.ToCheckedMotion.checked
        ({ m with poster := 2, checks := .warn } : Motion)).stopped)
  r := r.push ("motion stills: a caption of a key that is not a still is a note",
    hasNote { m with captions := m.captions.set! 2 "Passed through." } "is not a still")
  -- the timeline: the rest on key 1 and the turn about B divided at the windows' ends
  let tl := m.timeline
  let kinds := tl.segments.toList.map (·.kind)
  r := r.push ("motion windows: the rest on key 1 is cut at 0.2 s and 0.4 s, the turn about B at \
      0.7 s; the parts tile the cycle",
    kinds.count (.rest 1) == 3 && kinds.count (.move 1) == 2 && kinds.count (.rest 2) == 1 &&
      (tl.segments.filter (·.kind = .rest 1)).map (·.dur) == #[1 / 5, 1 / 5, 1 / 2] &&
      (tl.segments.filter (·.kind = .move 1)).map (·.dur) == #[7 / 10, 3 / 10] &&
      tl.cycle == base.cycle &&
      (tl.segments.toList.zip tl.segments.toList.tail).all (fun (a, b) => a.stop == b.start) &&
      (tl.segments[0]?.map (·.start)) == some 0 &&
      (tl.segments.back?.map (·.stop)) == some tl.cycle)
  r := r.push ("motion windows: the key is shown still in the last part of its rest, after its \
      fades",
    tl.restTime 1 == ((tl.stillPart? 1).map (fun s => s.start + s.dur / 2)).getD 0 &&
      ((tl.stillPart? 1).map (·.dur)) == some (1 / 2))
  -- the written opacities, read with `Smil.valueAt`, against the model
  let root := liveGroup m
  let r1 := Exact.toFloat ((tl.segments.find? (·.kind = .rest 1)).map (·.start) |>.getD 0)
  let s1 := Exact.toFloat ((tl.segments.find? (·.kind = .move 1)).map (·.start) |>.getD 0)
  let op := fun (id : String) (t : Float) => (writtenOpacity root id 0 t).getD (-1)
  r := r.push ("motion fades: the ring at A fades out in the first 0.2 s of the rest on key 1, the \
      ring at B in over the next 0.2 s, then stands; it fades out in the last 0.3 s of the turn",
    near (op "mA" (r1 - 0.05)) 1 1e-6 && near (op "mA" (r1 + 0.1)) 0.5 1e-3 &&
      near (op "mA" (r1 + 0.25)) 0 1e-6 &&
      near (op "mB" (r1 + 0.1)) 0 1e-6 && near (op "mB" (r1 + 0.3)) 0.5 1e-3 &&
      near (op "mB" (r1 + 0.6)) 1 1e-6 && near (op "mB" (s1 + 0.5)) 1 1e-6 &&
      (op "mB" (s1 + 0.85) > 0.05 && op "mB" (s1 + 0.85) < 0.95) &&
      near (op "mB" (s1 + 1.05)) 0 1e-6)
  r := r.push ("motion fades: a fade that never starts is caught by the opacity samples \
      (mutation)",
    let bad := silence "mB" 256 root
    near (op "mB" (r1 + 0.6)) 1 1e-6 &&
      ((writtenOpacity bad "mB" 0 (r1 + 0.6)).map (near · 1 1e-3)) == some false)
  -- the turn in a divided step follows its eased angle
  let T := (m.plan.layers.find? (·.version.actor == some "T")).getD default
  let eased := fun (x : Float) => Easing.standard.eval x
  r := r.push ("motion windows: the turn about B, its step divided at 0.7 s, follows the step's \
      eased angle in the written picture",
    let p := m.plan
    [0.25, 0.5, 0.7, 0.8, 0.95].all fun (x : Float) =>
      let t := s1 + x
      let M := p.chainAt T t
      let ms := (shown t 256 Affine.id 1 root).getD #[]
      let w := (ms.find? (·.1 == "actor T")).map (·.2.2.2)
      -- the written transform is the baker's, and the turn is at the eased angle: the vertex
      -- (0, 1) of key 1, on the page, lands where the eased turn about B puts it
      w.any (affineNear · M 1e-6) &&
        let f := p.env.frame
        let c := f.toScreen ⟨0, 2⟩
        let q := f.toScreen ⟨0, 1⟩
        let θ := -(Plane.pi / 2) * eased x
        let d := q - c
        let want : Point := ⟨c.x + d.x * θ.cos - d.y * θ.sin, c.y + d.x * θ.sin + d.y * θ.cos⟩
        -- the chain carries the vertex (1, 0) of key 0 by the turn about A, done, and the turn
        -- about B, in progress
        (M.apply (f.toScreen ⟨1, 0⟩)).dist want < 0.05)
  r := r.push ("motion windows: a step on a steep curve whose part is no timing curve is halved \
      there, every part exact, and the turn follows its eased angle across every boundary",
    let sm := steepMotion
    let p := sm.plan
    let parts := p.timeline.segments.filter (·.kind = .move 0)
    sm.problems.isEmpty && parts.size == 3 && sm.inexactSteps sm.keysOf == #[] &&
      modelAgrees sm &&
      (Easing.spline 0.83 0 0.17 1).part 0 0.6 == none)
  -- the outputs of a motion with a key that is not a still
  let c := PILean.Trust.ToCheckedMotion.checked m
  let names := (PILean.Trust.motionOutputs c).map fun o => s!"{o.name}.{o.format.name}"
  r := r.push ("motion stills: a key that is not a still has no files; the others keep their key's \
      number",
    names.contains "-key-0.svg" && names.contains "-key-1.png" && names.contains "-key-3.svg" &&
      !names.contains "-key-2.svg" && !names.contains "-key-2.png" &&
      c.main.stills.size == 3 && c.stillKeys == #[0, 1, 3] &&
      c.summary.stills == some #[0, 1, 3] && c.summary.keys == 4)
  r := r.push ("motion stills: the page counts the stills, not the keys",
    let d := c.page c.main
    d.stills.frames.size == 3 && d.stills.stepCaptions.size == 3 && d.stillKeys == #[0, 1, 3] &&
      d.rests.size == 4 && ((d.rests[1]?).map (·.fades.size)) == some 2 &&
      ((d.rests[2]?).map (·.still)) == some false &&
      has (d.words) "4 key frames, 3 of them shown as stills")
  r := r.push ("motion stills: the record of a motion with stills reads back; a bad one does not",
    let s := c.summary
    PILean.Trust.MotionSummary.ofText? s.text == some s &&
      has s.text ";stills=0,1,3" &&
      PILean.Trust.MotionSummary.ofText? (s.text ++ ",4") == none &&
      PILean.Trust.MotionSummary.ofText?
        ((s.text.splitOn ";stills=").headD "" ++ ";stills=0,1,2,3") == none &&
      PILean.Trust.MotionSummary.ofText?
        ((s.text.splitOn ";stills=").headD "" ++ ";stills=1,0") == none)
  r := r.push ("motion windows: the step table gives each fade its window, in seconds",
    let rows := m.stepRows
    let fades := (rows[1]?).map fun row => row.moves.filterMap (·.window)
    fades == some #[(7 / 10, 1)] &&
      ((m.restRows[1]?).map fun rr => rr.fades.map (·.window)) ==
        some #[some (0, 1 / 5), some (1 / 5, 2 / 5)])
  return r

/-- All checks. -/
def checks : Array (String × Bool) := ruleChecks ++ layoutChecks ++ outputChecks ++ featureChecks

/-! ### Files for the browser check -/

/-- A number as JSON. -/
def num (x : Float) : String := if x.isFinite then toString x else "0"

/-- A page point as JSON. -/
def pt (p : Point) : String := s!"[{num p.x}, {num p.y}]"

/-- Whether some actor that turns has a label or a point's marker, from the motion's model: then
its picture must have upright groups. -/
def turningMarks (m : Motion) : Bool :=
  (m.steps.mapIdx fun j s => (j, s)).any fun (j, s) => s.moves.any fun (id, mv) =>
    match mv, (m.keys.getD j default).actor? id with
    | .turn .., some it => it.leaves.any (·.geom.upright)
    | _, _ => false

/-- The version of the expectations' format (`expectations`, `MotionPanelsChecks.expectations`),
which the browser checks require: 2 has the rests' ends, the slides, the declared moves and the
actors' drawings; 3 has the opacity of every appearance and disappearance before, in and after its
window (`opacities`), whether each key is a still, the part of each rest in which its key is shown
still (`from`, `until`), and the samples of a turn or a slide over its whole step. -/
def expectationsFormat : Nat := 3

/-- The span of step `j` in the timeline `tl`, in seconds: from the start of its first segment to
the end of its last (a step divided for a morph or for its fades has several). -/
def stepSpan (tl : Timeline) (j : Nat) : Option (Float × Float) := do
  let segs := tl.segments.filter (·.kind = .move j)
  let a ← segs[0]?
  let b ← segs.back?
  return (Exact.toFloat a.start, Exact.toFloat (b.start + b.dur))

/-- The span of the rest on key `k` in the timeline `tl`, in seconds (all its parts). -/
def restSpan (tl : Timeline) (k : Nat) : Option (Float × Float) := do
  let segs := tl.segments.filter (·.kind = .rest k)
  let a ← segs[0]?
  let b ← segs.back?
  return (Exact.toFloat a.start, Exact.toFloat (b.start + b.dur))

/-- The eased fraction of step `j` of the timeline `base` (undivided) at the fraction `x` of its
time, with the step's easing as written (its control values to six decimals). -/
def stepEased (base : Timeline) (j : Nat) (x : Float) : Float :=
  match base.segments.find? (·.kind = .move j) with
  | some s =>
    let (a, b, c, d) := s.easing.controls
    (Easing.spline (quant 6 a) (quant 6 b) (quant 6 c) (quant 6 d)).eval x
  | none => x

/-- Samples of step `j` of the timeline `tl` (undivided, `base`), with the eased fraction of the
step done at each, as JSON: at a quarter, a half and three quarters of its time, and, when the step
is divided into parts (for the windows of its fades or for a sampled morph), also at every boundary
between two parts and in the middle of every part, so that a turn is checked inside each part and
where one part ends and the next begins. -/
def stepSamplesJson (tl base : Timeline) (j : Nat) : Option String := do
  let (a, b) ← stepSpan tl j
  let parts := tl.segments.filter (·.kind = .move j)
  let inner : List Float := if parts.size ≤ 1 then [] else
    (parts.toList.drop 1).map (fun s => (Exact.toFloat s.start - a) / (b - a)) ++
      parts.toList.map fun s =>
        (Exact.toFloat (s.start + s.dur / 2) - a) / (b - a)
  let xs := [0.25, 0.5, 0.75] ++ inner
  let samples := xs.map fun (x : Float) =>
    s!"\{\"t\": {num (a + x * (b - a))}, \"f\": {num (stepEased base j x)}}"
  return s!"[{", ".intercalate samples}]"

/-- The fades of a motion as the expectations list them, from its plan `p` on the timeline `tl`
(undivided, `base`), its fades in part of a step or a rest `F` and its steps and keys: for every
appearance and disappearance (a step's, in its window or through the whole step, and a rest's),
the actor's marked name with the prefix `pfx`, which of the actor's marked layers it is (`nth`, in
the order of the document), and the plan's opacity of that layer (with the seam's) before its
window starts, in its middle and after it ends (`0.05 s` out, within the cycle), as JSON. -/
def opacitiesJson (m : Motion) (p : MotionPlan) (F : MotionFades) (base : Timeline)
    (pfx : String := "") : List String :=
  let tl := p.timeline
  let cycle := Exact.toFloat tl.cycle
  let order := (p.runs.flatMap fun run => run.flatMap id).toList
  -- the layer of the actor `id` that a fade begins (`first`) or ends (`last`)
  let nthOf := fun (id : String) (pick : MotionVersion → Bool) => do
    let mine := order.filter fun i => (p.layers.getD i default).version.actor == some id
    let i ← mine.findIdx? fun i => pick (p.layers.getD i default).version
    return i
  let markerAt := fun (id : String) (n : Nat) (t : Float) =>
    let tt := t - cycle * (t / cycle).floor
    let ms := (p.markersAt tt).filter (·.1 == s!"actor {Canvas.safeToken id}")
    ((ms[n]?).map (·.2.2.1)).getD 0
  let one := fun (id kind : String) (n : Nat) (t0 t1 : Float) =>
    let ts := [t0 - 0.05, (t0 + t1) / 2, t1 + 0.05]
    let samples := ts.map fun t =>
      let tt := t - cycle * (t / cycle).floor
      s!"\{\"t\": {num tt}, \"o\": {num (markerAt id n t)}}"
    s!"\{\"id\": \"{pfx}{Canvas.safeToken id}\", \"nth\": {n}, \"kind\": \"{kind}\", \
      \"from\": {num t0}, \"until\": {num t1}, \"samples\": [{", ".intercalate samples}]}"
  let stepFades := (List.range m.steps.size).flatMap fun j =>
    let s := m.steps.getD j {}
    let d := Exact.toFloat (kindDur base (.move j))
    s.moves.toList.filterMap fun (id, mv) => do
      let (pick, kind) ← match mv with
        | .appear => some ((fun (v : MotionVersion) => v.first == j + 1), "appearance")
        | .vanish => some ((fun (v : MotionVersion) => v.last == j), "disappearance")
        | _ => none
      let (a, _) ← stepSpan tl j
      let (wa, wb) := ((F.steps.getD j #[]).find? (·.1 == id)).map (fun (_, _, x, y) =>
        (Exact.toFloat x, Exact.toFloat y)) |>.getD (0, 1)
      let n ← nthOf id pick
      return one id kind n (a + wa * d) (a + wb * d)
  let restFades := (List.range m.keys.size).flatMap fun k =>
    let d := Exact.toFloat (kindDur base (.rest k))
    (F.rests.getD k #[]).toList.filterMap fun (id, f, wa, wb) => do
      let (a, _) ← restSpan tl k
      let (pick, kind) := match f with
        | .appear => ((fun (v : MotionVersion) => v.first == k), "appearance")
        | .vanish => ((fun (v : MotionVersion) => v.last + 1 == k), "disappearance")
      let n ← nthOf id pick
      return one id kind n (a + Exact.toFloat wa * d) (a + Exact.toFloat wb * d)
  stepFades ++ restFades

/-- How many turns and slides the motion's steps declare, as JSON. -/
def declaredMoves (ms : Array Motion) : String :=
  let count := fun (p : Move → Bool) => ms.foldl (init := 0) fun n m =>
    m.steps.foldl (init := n) fun n s => n + (s.moves.filter (p ·.2)).size
  let turns := count fun | .turn .. => true | _ => false
  let slides := count fun | .slide _ => true | _ => false
  s!"\{\"turns\": {turns}, \"slides\": {slides}}"

/-- Each actor of `fig` with a fingerprint of its drawing in `e` (the first 16 digits of the
SHA-256 of its SVG text), as JSON members, its id prefixed by `pfx`: two rests whose fingerprints
differ draw that actor otherwise, even where its anchor is the same (a morph). -/
def actorShapes (e : Env) (fig : Figure) (pfx : String := "") : List String :=
  fig.items.toList.filterMap fun it => it.actorId?.map fun id =>
    let h := (PILean.Sha256.hex (PILean.Sha256.hash (itemText e fig.svgMode it).toUTF8)).take 16
    s!"\"{pfx}{Canvas.safeToken id}\": \"{h}\""

/-- What `tools/motion-browser-check.py` expects of the motion's SVG, as JSON (format
`expectationsFormat`): the cycle; the turns and slides the steps declare; for each key whether it
is a still and, at the middle of the part of its rest in which it is shown still (after the fades
of the rest, `Timeline.restTime`; that part's start and end too), every actor's anchor in the key's
still, every actor's drawing as a fingerprint (`actorShapes`), and every upright group's anchor
where the plan draws it (which the rest check holds to the still); for every turn, its centre, the
actor's anchor where the turn starts, its angle in SVG's degrees, and the times at a quarter, a
half and three quarters of its step with the eased fraction of the turn done then; for every slide
(of an actor that does nothing else in its step), the actor's anchors in the two keys and the same
times and fractions; and the opacity of every appearance and disappearance before, in and after
its window (`opacitiesJson`). -/
def expectations (name : String) (m : Motion) : String :=
  let K := m.keysOf
  let p := m.planIn K K.env
  let base := m.baseTimeline
  let F := m.fadesOn K base
  let st := K.env.style
  let anchorOf := fun (fig : Figure) (id : String) =>
    (fig.actor? id).bind fun it => (it.leaves[0]?).bind fun lf =>
      (anchors p.env.frame st lf.geom)[0]?
  let still := p.layers.filter (·.geoms.isNone)
  let rests := (List.range m.keys.size).map fun k =>
    let fig := K.figure k
    let ids := (still.filterMap (·.version.actor)).toList.eraseDups.filter fig.hasActor
    let actors := ids.filterMap fun id => (anchorOf fig id).map fun a =>
      s!"\{\"id\": \"{Canvas.safeToken id}\", \"at\": {pt a}}"
    let t := Exact.toFloat (p.timeline.restTime k)
    let ups := ((p.markersAt t).filter (·.1 == "upright")).toList.map fun (_, q, _) => pt q
    let seg := p.timeline.stillPart? k
    let lo := Exact.toFloat ((seg.map (·.start)).getD 0)
    let hi := Exact.toFloat ((seg.map fun s => s.start + s.dur).getD 0)
    s!"\{\"key\": {k}, \"still\": {m.isStill k}, \"t\": {num t}, \"from\": {num lo}, \
      \"until\": {num hi}, \"actors\": [{", ".intercalate actors}], \
      \"uprights\": [{", ".intercalate ups}], \
      \"shapes\": \{{", ".intercalate (actorShapes K.env fig)}}}"
  let tl := p.timeline
  let turns := still.toList.flatMap fun L => match L.version.actor with
    | none => []
    | some id => L.links.toList.filterMap fun
      | .turn j c deg => do
        let start ← anchorOf (K.figure j) id
        let samples ← stepSamplesJson tl base j
        return s!"\{\"id\": \"{Canvas.safeToken id}\", \"step\": {j}, \"centre\": {pt c}, \
          \"start\": {pt start}, \"sweep\": {num deg}, \"samples\": {samples}}"
      | .slide .. => none
  -- the slides: an actor whose only move in its step is a slide, from its anchor in the step's
  -- first key to its anchor in the next
  let slides := still.toList.flatMap fun L => match L.version.actor with
    | none => []
    | some id => L.links.toList.filterMap fun
      | .slide j _ => do
        guard ((L.links.filter (·.step == j)).size == 1)
        let a ← anchorOf (K.figure j) id
        let b ← anchorOf (K.figure (j + 1)) id
        let samples ← stepSamplesJson tl base j
        return s!"\{\"id\": \"{Canvas.safeToken id}\", \"step\": {j}, \"from\": {pt a}, \
          \"to\": {pt b}, \"samples\": {samples}}"
      | .turn .. => none
  let ups := (p.layers.map (·.uprights.size)).foldl (· + ·) 0
  s!"\{\"format\": {expectationsFormat}, \"name\": \"{name}\", \"svg\": \"{name}.svg\", \
    \"poster_png\": \"{name}-poster.png\", \"declared\": {declaredMoves #[m]}, \
    \"cycle\": {num (Exact.toFloat p.timeline.cycle)}, \"uprights\": {ups}, \
    \"turning_marks\": {turningMarks m}, \
    \"rests\": [{", ".intercalate rests}], \"turns\": [{", ".intercalate turns}], \
    \"slides\": [{", ".intercalate slides}], \
    \"opacities\": [{", ".intercalate (opacitiesJson m p F base)}]}\n"

/-- A motion with what real motions have and the golden ones lack, for the browser checks: five
points that appear together in one step (one opacity animation for five layers), a faint thin
segment that appears over a disk that slides under it (overlapping actors), a translucent
triangle that vanishes during a rest, a point that slides next to where another fades in, an
item without an id that changes between two keys (crossfaded, a note), and many fades in a long
cycle. -/
def crowdMotion : Motion where
  keys :=
    let pts := (List.range 5).toArray.map fun (i : Nat) =>
      Plane.Exact.point (((i : Rat), (2 : Rat)) : Q) |>.accent 1 |>.actor s!"B{i}"
    let disk := fun (x : Rat) => Plane.Exact.disk ((x, (0 : Rat)) : Q) (1 / 2 : Rat) |>.accent 0
      |>.actor "D"
    let seg := Plane.Exact.segment ((0, 0) : Q) ((4, 0) : Q) |>.faint |>.actor "S"
    let tri := Plane.Exact.polygon [((1, -1) : Q), (3, -1), (2, -2)] |>.filled |>.fillOpacity 0.3
      |>.accent 2 |>.actor "T"
    let mover := fun (x : Rat) => Plane.Exact.point ((x, (13 / 5 : Rat)) : Q) |>.accent 3
      |>.actor "M"
    let target := Plane.Exact.point ((3, 3) : Q) |>.accent 1 |>.actor "G"
    let mark := fun (y : Rat) => Plane.Exact.point (((-1 : Rat), y) : Q) |>.faint
    let corners := #[Plane.Exact.point ((-2, -3) : Q) |>.faint, Plane.Exact.point ((5, 4) : Q)
      |>.faint]
    #[{ items := corners ++ #[mark 0, disk 0, tri, mover 0] },
      { items := corners ++ #[mark 0, disk 0, tri, mover 0] ++ pts },
      { items := corners ++ #[mark 1, disk 2, tri, mover 0, seg] ++ pts },
      { items := corners ++ #[mark 1, disk 2, mover 3, seg, target] ++ pts },
      { items := corners ++ #[mark 1, disk 4, mover 3, target] ++ pts }]
  captions := #["Start.", "Five points appear.", "A segment appears over the sliding disk.",
    "The triangle fades; a point slides next to where another appears.", "The segment vanishes."]
  steps := #[{ moves := (List.range 5).toArray.map fun i => (s!"B{i}", .appear) },
    { moves := #[("D", Plane.Exact.slideFromTo ((0, 0) : Q) (2, 0)), ("S", .appear)],
      windows := #[("S", .fractions (1 / 4) (3 / 4))] },
    { moves := #[("M", Plane.Exact.slideFromTo ((0, 13 / 5) : Q) (3, 13 / 5)), ("G", .appear)] },
    { moves := #[("D", Plane.Exact.slideFromTo ((2, 0) : Q) (4, 0)), ("S", .vanish)] }]
  keyOptions := #[{}, {}, {}, { rest := some (6 / 5), fades := #[("T", .vanish, .first (1 / 2))] },
    {}]
  info := testInfo
  checks := .warn

/-- The motions written for the browser check besides the golden ones: a long first hold, a long
cycle, and a morph alone (a disk whose radius grows, its anchor unchanged). -/
def browserOnly : Array (String × Motion) :=
  #[("motion-long-hold", longHoldMotion), ("motion-long-cycle", longCycleMotion),
    ("motion-morph", morphMotion true), ("motion-crowd", crowdMotion),
    ("motion-steep", steepMotion)]

/-- Writes the golden motions and `browserOnly` into `dir` for `tools/motion-browser-check.py`:
each motion's SVG, the SVG of each key's still, the poster still's PNG and the expectations
(`expectations`). -/
def writeBrowserFiles (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  for (name, m) in golden ++ browserOnly do
    IO.FS.writeFile (dir / s!"{name}.svg") m.toSvgUnchecked
    for k in [0:m.keys.size] do
      IO.FS.writeFile (dir / s!"{name}-key{k}.svg") (m.keyFigure k).toSvg
    IO.FS.writeBinFile (dir / s!"{name}-poster.png") ((m.keyFigure m.poster).toPng.getD .empty)
    IO.FS.writeFile (dir / s!"{name}.json") (expectations name m)
    IO.println s!"{dir / name}: .svg, -key*.svg, -poster.png, .json"

end PILeanTest.MotionChecks
