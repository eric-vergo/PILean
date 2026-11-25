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

/-- The golden motions, by file name. -/
def golden : Array (String × Motion) :=
  #[("motion-turn", turnMotion), ("motion-two-centres", twoCentresMotion)]

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
  r := r.push ("motion: a disk turned about its own centre is a note (the check cannot see it)",
    let d := Plane.Exact.disk ((0, 0) : Q) (1 : Rat)
    noErrors (twoKeys d d (Plane.Exact.turnAbout ((0, 0) : Q) (1 / 3))) &&
      hasNote (twoKeys d d (Plane.Exact.turnAbout ((0, 0) : Q) (1 / 3))) "cannot see")
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
      hasError { turnMotion with info := { title := "t" } } "no description" &&
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
      (match turnMotion.svg? with | .ok svg => svg == turnMotion.toSvg | .error _ => false) &&
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
  let root := twoCentresMotion.svgRoot
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
    ((elements "g" 256 turnMotion.svgRoot).filter (attrOf · "data-pilean-upright" != "")).size
      == 1)
  let broot := batchMotion.svgRoot
  r := r.push ("motion: points that appear in the same step share one opacity animation",
    animCount broot "opacity" == 2 && batchMotion.problems.isEmpty)
  -- morphs
  let grow := morphMotion true
  r := r.push ("motion: a disk whose radius changes is a morph of its path data",
    grow.problems.isEmpty && animCount grow.svgRoot "d" ≥ 1 &&
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
      (f - 0.5).abs < 1e-7 && (allPaths 64 (p.figureAt t)).any fun q =>
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
      animCount sampledMotion.svgRoot "d" == 1)
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

/-- The live group of a motion's SVG. -/
def liveGroup (m : Motion) : Node :=
  ((elements "g" 256 m.svgRoot).find? (attrOf · "class" == Animation.liveClass)).getD (.text "")

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
  let tl := Timeline.build m.animSteps m.pacing
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
  let tl := Timeline.build m.animSteps m.pacing
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
    let rot := (elements "animateTransform" 256 sampledTurn.svgRoot).find? fun a =>
      attrOf a "type" == "rotate" && (attrOf a "values").startsWith s!"0 {o};"
    match rot with
    | none => 1e9
    | some a =>
      (List.range 201).foldl (init := 0) fun acc i =>
        let x := i.toFloat / 200
        let t := Exact.toFloat s.start + x * Exact.toFloat s.dur
        let written := ((Smil.valueAt a t).bind (·[0]?)).getD 1e9
        max acc (written - (-90) * s.easing.eval x).abs

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
    let svg := m.toSvg
    r := r.push (s!"motion {name}: the SVG is inert, keeps the invariant and runs on one clock",
      Svg.isInert svg && Smil.invariantProblem? 256 m.svgRoot == none &&
        Smil.clockProblem? m.svgRoot == none && svg == m.toSvg)
  r := r.push ("motion: a turn in a sampled step follows the eased angle within 90/4 degrees",
    sampledTurn.problems.isEmpty && sampledTurn.samplesOf sampledTurn.keysOf 0 == 4 &&
      sampledError < 90 / 4)
  for (name, m) in golden do
    r := r.push (s!"motion {name}: at every rest the baker draws the key still, every element",
      (m.restProblems m.keysOf m.plan).isEmpty &&
        (match m.svg? with | .ok svg => svg == m.toSvg | .error _ => false))
    r := r.push (s!"motion {name}: the stills are the key figures, byte for byte",
      (List.range m.keys.size).all fun k =>
        (m.keyFigure k).toSvg == ((commonView m.keys)[k]!).toSvg)
    let a := m.toAnimation
    r := r.push (s!"motion {name}: the animation is one cycle, its poster the poster key's rest",
      (a.duration - Exact.toFloat m.timeline.cycle).abs < 1e-12 &&
        a.posterTime == some (Exact.toFloat (m.timeline.restTime m.poster)) &&
        a.width == (m.keyFigure 0).pixelSize.1 && a.height == (m.keyFigure 0).pixelSize.2)
  return r

/-- All checks. -/
def checks : Array (String × Bool) := ruleChecks ++ layoutChecks ++ outputChecks

/-! ### Files for the browser check -/

/-- A number as JSON. -/
def num (x : Float) : String := if x.isFinite then toString x else "0"

/-- A page point as JSON. -/
def pt (p : Point) : String := s!"[{num p.x}, {num p.y}]"

/-- What `tools/motion-browser-check.py` expects of the motion's SVG, as JSON: the cycle; at the
middle of each key's rest, every actor's anchor in the key's still; and for every turn, its
centre, the actor's anchor where the turn starts, its angle in SVG's degrees, and the times at a
quarter, a half and three quarters of the turn with the eased fraction of the turn done then. -/
def expectations (name : String) (m : Motion) : String :=
  let K := m.keysOf
  let p := m.planIn K K.env
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
    s!"\{\"key\": {k}, \"t\": {num (Exact.toFloat (p.timeline.restTime k))}, \
      \"actors\": [{", ".intercalate actors}]}"
  let segs := p.timeline.segments
  let turns := still.toList.flatMap fun L => match L.version.actor with
    | none => []
    | some id => L.links.toList.filterMap fun
      | .turn j c deg => do
        let i ← (List.range segs.size).find? fun i => (segs[i]?.map (·.kind)) == some (.move j)
        let s ← segs[i]?
        let start ← anchorOf (K.figure j) id
        let samples := [0.25, 0.5, 0.75].map fun (x : Float) =>
          let t := Exact.toFloat s.start + x * Exact.toFloat s.dur
          s!"\{\"t\": {num t}, \"f\": {num ((p.clock.splines.getD i .linear).eval x)}}"
        return s!"\{\"id\": \"{Canvas.safeToken id}\", \"step\": {j}, \"centre\": {pt c}, \
          \"start\": {pt start}, \"sweep\": {num deg}, \"samples\": [{", ".intercalate samples}]}"
      | .slide .. => none
  let ups := (p.layers.map (·.uprights.size)).foldl (· + ·) 0
  s!"\{\"name\": \"{name}\", \"svg\": \"{name}.svg\", \"poster_png\": \"{name}-poster.png\", \
    \"cycle\": {num (Exact.toFloat p.timeline.cycle)}, \"uprights\": {ups}, \
    \"rests\": [{", ".intercalate rests}], \"turns\": [{", ".intercalate turns}]}\n"

/-- Writes the golden motions into `dir` for `tools/motion-browser-check.py`: each motion's SVG,
the SVG of each key's still, the poster still's PNG and the expectations (`expectations`). -/
def writeBrowserFiles (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  for (name, m) in golden do
    IO.FS.writeFile (dir / s!"{name}.svg") m.toSvg
    for k in [0:m.keys.size] do
      IO.FS.writeFile (dir / s!"{name}-key{k}.svg") (m.keyFigure k).toSvg
    IO.FS.writeBinFile (dir / s!"{name}-poster.png") ((m.keyFigure m.poster).toPng.getD .empty)
    IO.FS.writeFile (dir / s!"{name}.json") (expectations name m)
    IO.println s!"{dir / name}: .svg, -key*.svg, -poster.png, .json"

end PILeanTest.MotionChecks
