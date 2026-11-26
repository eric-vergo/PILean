/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plane.Graph
import PILean.Anim.Smil

/-!
# Motions of plane figures

A `Motion` is a looping animation of a plane figure given by exact *key frames*: a list of
`Figure`s, key `k` the picture at rest `k`, and for each step between two consecutive keys what
moves (`MotionStep`, `Move`): an *actor* (a top-level item of the key figures that carries an id,
`Item.actor`, the same as `Item.withId`) turns about a centre by an exact fraction of a full turn,
slides along a vector, appears, vanishes or changes its shape (a morph). Between the keys the
browser turns or slides the drawn items (`PILean.Plane.MotionPlan` writes the SMIL animations and
draws the same motion as baked frames); the key frames themselves are drawn by the plane figures'
own pipeline.

This module holds the model and its checks.

* **One view.** The keys are drawn in one frame (`commonView`), so nothing rescales during the
  loop; a key with a frame of its own is a problem.
* **Kept label placements.** An automatic label (`Placement.auto`, `across`) of an actor is placed
  on the first key where the actor appears and keeps that placement on every later key
  (`Motion.resolved`), so that it rides the actor's moves; the key figures with these placements
  are the stills (`Motion.keyFigure`) and pass the layout checks on every key.
* **The arrival check.** It compares the actor in key `k`, carried by the declared turn or slide
  (applied in floating point to the page points that fix its drawing, `anchors`: a point, the ends
  of a segment, the centre of a circle, the vertices of a polygon, the ends of an arc, a label's
  point), with the actor in key `k + 1`: the same leaves in order, of the same kinds, looks,
  texts, placements and metadata (`leafKey`), radii and every anchor within `arrivalTolerance`
  (0.01 px). It does not determine the direction or the number of revolutions of a turn (for a
  turn by `1/5`, `6/5` and `-4/5` land too; a turn by a whole turn or more is an error unless the
  step sets `allowFullTurns`), says nothing about what the turn leaves alike (a disk centred on the
  turn's centre, a whole turn: a note says so), and does not tell a slide from a turn with the
  same end points; for a single point and an angle that is not a whole turn, the centre is
  determined. A polygon whose vertex list is the same after a symmetry turn is refused: the next
  key must list the turned vertices in the turned order. A move that misses its key is an error,
  and is not animated as that move.
* **The stills pin the animation.** At the middle of every key's rest, the whole baked drawing
  (every path and every text, in order) must be the key's still within the rest tolerance
  (`restProblems`, 0.05 px); this bounds what the per-step tolerance can add up to along a chain,
  and catches a wrong counter-rotation or stacking order.
* **Labels and markers stay upright.** Their point rides the turns; they are not turned
  themselves (the anchors of a label and of a point are their points, and their look is compared
  unchanged).
* **What changes without a move.** An item without an id that differs between two consecutive
  keys crossfades, with a note. An actor that differs without a declared move, leaves without
  `vanish`, comes without `appear`, or has a morph that cannot be interpolated is an error under
  `CheckLevel.fail` (the default; `Motion.svg?` then writes nothing) and a crossfade with a note
  under `warn`.

## Main definitions

* `Move`, `MotionStep`, `MotionStep.idle`, `Motion`, `Item.actor`, `Plane.Exact.turnAbout`,
  `Plane.Exact.slideFromTo`.
* `Motion.WellFormed` (decidable), `Motion.animSteps`, `MotionKeys`, `Motion.keysOf`,
  `Motion.resolved`, `Motion.keyFigure`.
* `MotionVersion`, `Motion.continuation`, `Motion.versions`: the layers of a motion (an actor for
  as long as its steps carry it, an item without an id for as long as the keys draw it alike).
* `mergeOrder`, `inOrder`: one drawing order for the layers of all keys.
* `anchors`, `leafKey`, `Move.pageAffine`, `arrival`, `Motion.stepProblems`, `Motion.keyProblems`
  (`Motion.problems`, with the rest check, `Motion.checkMessages` and `Motion.problemsFail` are
  in `PILean.Plane.MotionOutput`).
* `Motion.turnsOf`, `Motion.turnSum`, `Motion.keyAngle`.

## Main results

* `Motion.keyAngle_eq`: `Motion.keyAngle` (a function of the model, which the writer does not
  call) is minus 360 times the exact sum of an actor's turns before key `k`. The angle the writer
  turns each link by is `PILean.Plane.linkOf_turn`'s.
* `Motion.timeline_keys`: the timeline of a well-formed motion has as many keys as the motion.
-/

namespace PILean.Plane

open Canvas

/-! ### The model -/

/-- What an actor does in a step. -/
inductive Move where
  /-- A turn about `centre` (world coordinates) by `turns` of a full turn, counterclockwise in the
  figure's coordinates (`1/5` is 72°). -/
  | turn (centre : Point) (turns : Rat)
  /-- A slide along the world vector `v`. -/
  | slide (v : Point)
  /-- An appearance: the actor is in the next key and not in this one; it fades in. -/
  | appear
  /-- A disappearance: the actor is in this key and not in the next; it fades out. -/
  | vanish
  /-- A change of shape: the drawing of the actor changes between the two keys (a disk whose
  radius changes); the browser interpolates the path data, or the two drawings crossfade when
  they cannot be interpolated. -/
  | morph
  deriving Inhabited, Repr

/-- The move in words. -/
def Move.name : Move → String
  | .turn .. => "turn" | .slide _ => "slide" | .appear => "appearance"
  | .vanish => "disappearance" | .morph => "morph"

/-- The item as an actor of a motion: the item with the id `id` (`Item.withId`). -/
def Item.actor (id : String) (it : Item) : Item := it.withId id

/-- A step between two consecutive key frames: the moves of its actors, whether anything moves,
and its duration and easing when they are not the pacing's. -/
structure MotionStep where
  /-- The actors (by id) and their moves; an actor not named does not move. -/
  moves : Array (String × Move) := #[]
  /-- `idle` for a step in which nothing moves (it takes the pacing's `idle` time). -/
  kind : Anim.StepKind := .move
  /-- The duration in seconds; by default the pacing's, for the longest kind of move it has. -/
  duration : Option Rat := none
  /-- The easing; by default the pacing's (and none for an idle step). -/
  easing : Option Anim.Easing := none
  /-- Whether the step may turn an actor by a whole turn or more (`|turns| ≥ 1`); without it, such
  a turn is an error, because the arrival check cannot see whole turns. -/
  allowFullTurns : Bool := false
  deriving Inhabited

/-- A step in which nothing moves. -/
def MotionStep.idle : MotionStep := { kind := .idle }

/-- A motion of a plane figure through exact key frames (see the module docstring). -/
structure Motion where
  /-- The key frames: key `k` is the picture at rest `k`. -/
  keys : Array Figure
  /-- One caption per key (`"Step 3 of 5: …"`), the text alternative of the stills. -/
  captions : Array String := #[]
  /-- The steps, one fewer than the keys. -/
  steps : Array MotionStep := #[]
  /-- Figures between two keys for a morph: `between j q` is the picture at the fraction `q` of
  step `j`, if the author has it exactly; the morphing actors are read from it. -/
  between : Nat → Rat → Option Figure := fun _ _ => none
  /-- How many intervals a morph with `between` is sampled in. -/
  morphSamples : Nat := 16
  /-- The durations, easing and seam. -/
  pacing : Anim.Pacing := {}
  /-- The title and description of the whole picture. -/
  info : ShapeInfo := {}
  /-- How the problems of the motion (`Motion.problems`) apply when it is rendered: by default an
  error stops the rendering (`Motion.svg?` refuses to write the motion). -/
  checks : CheckLevel := .fail
  /-- The key shown as the still (under reduced motion, and as the poster). -/
  poster : Nat := 0
  deriving Inhabited

namespace Exact

variable {α : Type} [PILean.Exact.PlanePoint α]

/-- A turn about the exact point `c` by `turns` of a full turn, counterclockwise. -/
def turnAbout (c : α) (turns : Rat) : Move := .turn (PILean.Exact.PlanePoint.toPoint c) turns

/-- A slide that carries the exact point `p` to the exact point `q`. -/
def slideFromTo (p q : α) : Move :=
  .slide (PILean.Exact.PlanePoint.toPoint q - PILean.Exact.PlanePoint.toPoint p)

end Exact

/-! ### Well-formedness and timing -/

namespace Motion

variable (m : Motion)

/-- The motion has one more key than steps, a caption per key, and its poster among the keys. -/
def WellFormed : Prop :=
  m.keys.size = m.steps.size + 1 ∧ m.captions.size = m.keys.size ∧ m.poster < m.keys.size

/-- Whether a motion is well formed is decided by comparing its sizes. -/
instance : Decidable m.WellFormed := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The timing of a step: an idle step takes the pacing's `idle` time unless it gives its own, not
eased; a step that moves takes its own duration or the pacing's for the longest of its kinds of
move (turns, slides, fades; a morph as a slide; a step with no moves as a fade), eased with its
own easing or the pacing's. -/
def animStep (p : Anim.Pacing) (s : MotionStep) : Anim.Step :=
  match s.kind with
  | .idle => { kind := .idle, dur := s.duration.getD p.idle, easing := s.easing.getD .linear }
  | .move =>
    let durs := s.moves.map fun (_, mv) => match mv with
      | .turn .. => p.turn | .slide _ | .morph => p.slide | .appear | .vanish => p.fade
    { dur := s.duration.getD (if durs.isEmpty then p.fade else durs.foldl max 0),
      easing := s.easing.getD p.easing }

/-- The steps of the motion's timeline. -/
def animSteps : Array Anim.Step := m.steps.map (animStep m.pacing)

/-- The timeline of a well-formed motion has as many keys as the motion. -/
theorem timeline_keys (h : m.WellFormed) :
    (Anim.Timeline.build m.animSteps m.pacing).keys = m.keys.size := by
  simp [Anim.Timeline.build, animSteps, h.1]

/-! ### Turns -/

/-- The move of the actor `id` in step `j`, if it has one. -/
def moveOf (j : Nat) (id : String) : Option Move :=
  (m.steps[j]?.bind fun s => s.moves.find? (·.1 == id)).map (·.2)

/-- The turn of the actor `id` in each step, as an exact fraction of a full turn (`0` in the steps
where it does not turn). -/
def turnsOf (id : String) : Array Rat :=
  (Array.range m.steps.size).map fun j => match m.moveOf j id with
    | some (.turn _ q) => q
    | _ => 0

/-- The exact sum of the turns of the actor `id` before key `k`. -/
def turnSum (id : String) (k : Nat) : Rat := ((m.turnsOf id).toList.take k).foldr (· + ·) 0

/-- The angle in degrees of the chain of groups of the actor `id` at key `k`, as SVG's `rotate`
measures it (clockwise on the page, whose `y` points down): `Anim.Smil.turnAngles` of its turns
negated. -/
def keyAngle (id : String) (k : Nat) : Float := Anim.Smil.turnAngles ((m.turnsOf id).map (-·)) k

private theorem foldr_neg (l : List Rat) :
    (l.map (-·)).foldr (· + ·) 0 = -(l.foldr (· + ·) 0) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.foldr_cons, ih]; grind

/-- The angle of a turning actor's groups at key `k` is minus 360 times the exact sum of its
turns before key `k` (counterclockwise in the figure is clockwise in SVG's measure). -/
theorem keyAngle_eq (id : String) (k : Nat) :
    m.keyAngle id k = Exact.toFloat (-(360 * m.turnSum id k)) := by
  simp only [keyAngle, Anim.Smil.turnAngles, turnSum, Array.toList_map, ← List.map_take,
    foldr_neg]
  congr 1
  grind

end Motion

/-! ### Actors and the drawing of the keys -/

/-- The metadata of an item. -/
def Item.info : Item → ShapeInfo
  | .shape _ _ i | .group _ i => i

/-- The id of an actor: the item's id, if it has one. -/
def Item.actorId? (it : Item) : Option String :=
  if it.info.id.isEmpty then none else some it.info.id

/-- The top-level item of `fig` that is the actor `id`. -/
def Figure.actor? (fig : Figure) (id : String) : Option Item :=
  fig.items.find? (·.actorId? == some id)

/-- Whether `fig` has the actor `id`. -/
def Figure.hasActor (fig : Figure) (id : String) : Bool := (fig.actor? id).isSome

/-- The text mode of a figure's SVG. -/
def Figure.svgMode (fig : Figure) : TextMode :=
  .forSvg fig.style.text fig.style.fontFamily fig.textAsShapes

/-- An item drawn in an environment, as SVG text (to compare two drawings). -/
def itemText (e : Env) (mode : TextMode) (it : Item) : String :=
  String.join ((Shape.group (drawItem e it)).render mode |>.toList.map (Svg.render 0))

/-- The placements (side and offset) for the automatic labels of `orig`, in order: for each,
that of the label at the same position among the leaves of `first` (the item as placed on the
first key where it appears) when there is one, else that of `here` (the item as placed on its own
key). -/
def keptPicks (orig first here : Item) : List (Placement × Float) :=
  let fl := first.leaves
  let hl := here.leaves
  (orig.leaves.mapIdx fun i lf => (i, lf)).toList.filterMap fun (i, lf) =>
    if !lf.isAuto then none
    else
      let pick := fun (l? : Option Leaf) => l?.bind fun l => match l.geom with
        | .label _ _ q (some off) => some (q, off)
        | _ => none
      (pick fl[i]?).orElse fun _ => pick hl[i]?

/-- The first of the figures that has the actor `id`. -/
def firstKeyIn (figs : Array Figure) (id : String) : Option Nat :=
  (List.range figs.size).find? fun k => (figs.getD k default).hasActor id

/-- The item `it` of key `k`, with its automatic labels placed: as placed on its own key (`here`),
or, for an actor seen on an earlier key, as placed on the first key that has it (among the keys
in one view, `viewed`, and placed each on its own, `placed`). -/
def keepItemIn (viewed placed : Array Figure) (k : Nat) (it here : Item) : Item :=
  match it.actorId? with
  | none => here
  | some id =>
    match firstKeyIn viewed id with
    | some a =>
      if a < k then
        match (placed.getD a default).actor? id with
        | some first => (it.replaceAuto.run' (keptPicks it first here))
        | none => here
      else here
    | none => here

/-- The keys of a motion as drawn, computed once: in one view (`commonView`), with their automatic
labels placed each on its own (`placed`), and as drawn (`figs`): an actor's automatic labels
placed on the first key where it appears and kept on the later ones; the drawing environment and
the SVG text mode of key `0`. -/
structure MotionKeys where
  /-- The keys in one view. -/
  viewed : Array Figure
  /-- The keys in one view, their automatic labels placed each on its own. -/
  placed : Array Figure
  /-- The keys as drawn. -/
  figs : Array Figure
  /-- The drawing environment: key `0`'s frame and style. -/
  env : Env
  /-- The text mode of the SVG: key `0`'s. -/
  mode : TextMode

/-- Key `k` as drawn. -/
def MotionKeys.figure (K : MotionKeys) (k : Nat) : Figure := K.figs.getD k default

namespace Motion

variable (m : Motion)

/-- The keys of the motion as drawn (see `MotionKeys`). -/
def keysOf : MotionKeys :=
  let viewed := commonView m.keys
  let placed := viewed.map (·.autoPlaced)
  let figs := viewed.mapIdx fun k fig =>
    let here := placed.getD k fig
    let items := fig.items.mapIdx fun i it => keepItemIn viewed placed k it (here.items.getD i it)
    { here with items }
  let k0 := figs.getD 0 default
  { viewed, placed, figs, env := k0.env, mode := k0.svgMode }

/-- The key figures as drawn: in one view, their automatic labels placed, an actor's on the first
key where it appears and kept on the later ones. -/
def resolved : Array Figure := m.keysOf.figs

/-- Key `k` as a still: the figure `resolved` gives, drawn by the plane figures' pipeline
(`Figure.toSvg`, `Figure.toPng`). -/
def keyFigure (k : Nat) : Figure := m.resolved.getD k default

/-- The drawing environment of the motion: the frame and style of key `0`. -/
def env : Env := m.keysOf.env

/-- The text mode of the motion's SVG: key `0`'s. -/
def mode : TextMode := m.keysOf.mode

/-- The figure at the fraction `q` of step `j` for a morph (`between`), in the keys' view, with
its automatic labels placed as on the keys. -/
def betweenFigure (K : MotionKeys) (j : Nat) (q : Rat) : Option Figure :=
  (m.between j q).map fun f =>
    let k0 := K.figure 0
    let v : Figure :=
      { f with view := k0.view, height := k0.height, padding := k0.padding, width := k0.width }
    let here := v.autoPlaced
    let items := v.items.mapIdx fun i it =>
      keepItemIn K.viewed K.placed (j + 1) it (here.items.getD i it)
    { here with items }

/-- The figures a morph in step `j` passes through, when `between` gives all of them: key `j`,
the figures at `i / n` for `0 < i < n` (`n = morphSamples`), key `j + 1`. -/
def morphFigures (K : MotionKeys) (j : Nat) : Option (Array Figure) :=
  let n := m.morphSamples
  if n < 2 then none
  else do
    let inner ← (List.range (n - 1)).toArray.mapM fun i =>
      m.betweenFigure K j ((i + 1 : Nat) / n)
    return #[K.figure j] ++ inner ++ #[K.figure (j + 1)]

end Motion

/-! ### Anchors and honest arrival -/

/-- The page points that fix where an element is drawn: a point's or a label's point, the ends of
a segment (a line, a ray, an arrow), the centre of a circle or a disk, the centre and the ends of
an arc or a sector, the vertices of a polygon or a polyline, the centre and the ends of an angle
mark, a tick's point and a point along it, the centres of a region of disks. -/
def anchors (f : Frame) (st : Style) : Geom → Array Point
  | .point p | .label _ p _ _ => #[f.toScreen p]
  | .segment a b | .line a b | .ray a b | .arrow a b => #[f.toScreen a, f.toScreen b]
  | .circle c _ | .disk c _ => #[f.toScreen c]
  | .arc c r θ₀ θ₁ | .sector c r θ₀ θ₁ =>
    #[f.toScreen c, f.toScreen (c + polar r θ₀), f.toScreen (c + polar r θ₁)]
  | .polygon vs | .polyline vs => vs.map f.toScreen
  | .angleMark c θ₀ θ₁ radius =>
    let q := f.toScreen c
    let r := radius.getD st.plane.angleRadius
    let toward := fun (θ : Float) => q + r * (⟨θ.cos, -θ.sin⟩ : Point)
    #[q, toward θ₀, toward θ₁]
  | .tick p dir _ =>
    let q := f.toScreen p
    #[q, q + (8 : Float) * unitOf (f.toScreen (p + dir) - q)]
  | .disks _ c₁ _ c₂ _ => #[f.toScreen c₁, f.toScreen c₂]

/-- The lengths on the page that a move must keep: the radii of circles, disks, arcs, sectors and
regions of disks. -/
def measures (f : Frame) : Geom → Array Float
  | .circle _ r | .disk _ r | .arc _ r _ _ | .sector _ r _ _ => #[f.scale * r]
  | .disks _ _ r₁ _ r₂ => #[f.scale * r₁, f.scale * r₂]
  | _ => #[]

/-- Everything about an element that a turn or a slide keeps, as text: its kind, the number of its
vertices, the sweep of an arc, the text, placement and offset of a label, the length of a tick,
the operation of a region. -/
def geomKey : Geom → String
  | .point _ => "point"
  | .segment .. => "segment"
  | .line .. => "line"
  | .ray .. => "ray"
  | .arrow .. => "arrow"
  | .circle .. => "circle"
  | .disk .. => "disk"
  | .arc _ _ θ₀ θ₁ => s!"arc {fmtNum (θ₁ - θ₀) 9}"
  | .sector _ _ θ₀ θ₁ => s!"sector {fmtNum (θ₁ - θ₀) 9}"
  | .polygon vs => s!"polygon {vs.size}"
  | .polyline vs => s!"polyline {vs.size}"
  | .angleMark _ θ₀ θ₁ r => s!"angle mark {fmtNum (θ₁ - θ₀) 9} {reprStr r}"
  | .label s _ pl off => s!"label {reprStr s} {reprStr pl} {reprStr off}"
  | .tick _ _ len => s!"tick {reprStr len}"
  | .disks op .. => s!"disks {reprStr op}"

/-- Everything about a leaf that a turn or a slide keeps (`geomKey`, its look and metadata). -/
def leafKey (lf : Leaf) : String := s!"{geomKey lf.geom} {reprStr lf.look} {reprStr lf.info}"

/-- Whether an element is drawn upright whatever its actor's turns: a label or a point's marker
(its point rides the turns). -/
def Geom.upright : Geom → Bool
  | .label .. | .point _ => true
  | _ => false

/-- Whether an element is drawn to the edge of the page (a line or a ray), so that turning or
sliding its drawing does not give the drawing of the turned or slid element. -/
def Geom.clipped : Geom → Bool
  | .line .. | .ray .. => true
  | _ => false

/-- The rotation by `deg` degrees about the page point `c`, as SVG's `rotate(deg cx cy)`
(clockwise on the page). -/
def rotAbout (c : Point) (deg : Float) : Affine :=
  (Affine.translate c.x c.y).comp ((Affine.rotate (deg * pi / 180)).comp
    (Affine.translate (-c.x) (-c.y)))

/-- The angle in degrees on the page (SVG's measure) of a counterclockwise turn by `q` of a full
turn in the figure. -/
def pageDegrees (q : Rat) : Float := Exact.toFloat (-(360 * q))

/-- The whole of a move on the page through the frame `f`: a turn about the centre's page
position, a slide by the vector's page image; nothing for the others. -/
def Move.pageAffine (f : Frame) : Move → Affine
  | .turn c q => rotAbout (f.toScreen c) (pageDegrees q)
  | .slide v => Affine.translate (f.scale * v.x) (-(f.scale * v.y))
  | _ => Affine.id

/-- How far a drawing may land from the next key (pixels). -/
def arrivalTolerance : Float := 0.01

/-- Whether the drawing of item `a` carried by the page transform `t` lands on the drawing of
item `b`: `none` when it does, else what is wrong. The leaves must agree in everything a move
keeps (`leafKey`, `measures`), and every anchor of `a` carried by `t` must be within
`arrivalTolerance` of the anchor of `b`. -/
def arrival (f : Frame) (st : Style) (t : Affine) (a b : Item) : Option String := Id.run do
  let la := a.leaves
  let lb := b.leaves
  if la.size != lb.size then
    return some s!"its drawing has {la.size} elements in one key and {lb.size} in the next"
  let mut worst : Float := 0
  for (i, x, y) in (la.zip lb).mapIdx fun i (x, y) => (i, x, y) do
    if leafKey x != leafKey y then
      return some s!"its element {i} differs in more than its position"
    let ma := measures f x.geom
    let mb := measures f y.geom
    if ma.size != mb.size || (ma.zip mb).any fun (u, v) => !((u - v).abs ≤ arrivalTolerance) then
      return some s!"its element {i} changes its radius"
    let pa := anchors f st x.geom
    let pb := anchors f st y.geom
    if pa.size != pb.size then return some s!"its element {i} changes its number of points"
    for (p, q) in pa.zip pb do
      let d := (t.apply p).dist q
      if !(d ≤ worst) then worst := d
  if worst ≤ arrivalTolerance then return none
  return some s!"it lands {fmtNum worst 3} px from its drawing in the next key"

/-! ### Interpolation of drawings -/

/-- Whether two node trees are the same but for the path data of their `path` elements, which can
be interpolated (`interpolable`), at most `fuel` deep: a morph between them is an `animate` of
`d` on each path. -/
def onlyPathsDiffer : Nat → Svg.Node → Svg.Node → Bool
  | 0, _, _ => false
  | _, .text a, .text b => a == b
  | fuel + 1, .element n as cs, .element n' bs ds =>
    n == n' && as.size == bs.size &&
      (as.zip bs).all (fun ((k, v), (k', v')) =>
        k == k' && (v == v' || (k == "d" && n == "path" && interpolable #[v, v']))) &&
      cs.size == ds.size && (cs.zip ds).all fun (c, d) => onlyPathsDiffer fuel c d
  | _, _, _ => false

/-- The nodes of an item drawn in an environment. -/
def itemNodes (e : Env) (mode : TextMode) (it : Item) : Array Svg.Node :=
  (Shape.group (drawItem e it)).render mode

/-- Whether the drawings of items can be interpolated one into the next (`onlyPathsDiffer`), and
the items have the same structure (the same number of leaves). -/
def interpolableItems (e : Env) (mode : TextMode) (its : Array Item) : Bool :=
  match its[0]? with
  | none => false
  | some a =>
    let na := itemNodes e mode a
    its.all fun b =>
      let nb := itemNodes e mode b
      b.leaves.size == a.leaves.size && nb.size == na.size &&
        (na.zip nb).all fun (x, y) => onlyPathsDiffer 256 x y

/-! ### Layers -/

namespace Motion

variable (m : Motion)

/-- Whether step `j` declares a morph. -/
def morphsIn (j : Nat) : Bool :=
  (m.steps.getD j {}).moves.any fun (_, mv) => match mv with | .morph => true | _ => false

/-- The number of intervals step `j` is divided into: `morphSamples` for a morph with figures
between its keys (`morphFigures`), else one. -/
def samplesOf (K : MotionKeys) (j : Nat) : Nat :=
  if m.morphsIn j && (m.morphFigures K j).isSome then m.morphSamples else 1

end Motion

/-- A part of the motion drawn by one item: an actor, from the key where it appears for as long as
its steps carry it (see the module docstring), or an item without an id for as long as the keys
draw it alike. -/
structure MotionVersion where
  /-- The actor's id; `none` for an item without one. -/
  actor : Option String
  /-- The first key that shows it. -/
  first : Nat
  /-- The item at each key that shows it, from `first` on. -/
  items : Array Item
  /-- The turn, slide or morph of each step it takes part in (`none`: unchanged). -/
  moves : Array (Option Move) := #[]
  /-- The items a sampled morph passes through, by step (both keys included). -/
  samples : Array (Nat × Array Item) := #[]
  deriving Inhabited

namespace MotionVersion

variable (v : MotionVersion)

/-- The last key that shows it. -/
def last : Nat := v.first + v.items.size - 1

/-- Whether key `k` shows it. -/
def visible (k : Nat) : Bool := v.first ≤ k && k ≤ v.last

/-- Whether a move is a turn or a slide. -/
def isRigid : Option Move → Bool
  | some (.turn ..) | some (.slide _) => true
  | _ => false

/-- The key after its last morph (its first key when it has none): from there on its drawing is
fixed and only moved. -/
def fixedFrom : Nat :=
  match (v.moves.mapIdx fun i mv => (i, mv)).toList.reverse.find? fun (_, mv) =>
      match mv with | some .morph => true | _ => false with
  | some (i, _) => v.first + i + 1
  | none => v.first

/-- Its item at key `k`, at most `fixedFrom`. -/
def itemAtKey (k : Nat) : Item :=
  let k' := min (max k v.first) v.fixedFrom
  v.items.getD (k' - v.first) (v.items.getD 0 default)

end MotionVersion

namespace Motion

variable (m : Motion)

/-- The items a morph of the actor `id` in step `j` passes through, when `between` gives all of
them with the actor. -/
def morphItems (K : MotionKeys) (j : Nat) (id : String) : Option (Array Item) :=
  (m.morphFigures K j).bind (·.mapM (·.actor? id))

/-- Whether the layer `v` goes on to the item `it` of key `j + 1`, and with what: a turn or a slide
declared for its actor that carries its drawing onto `it` (`arrival`; one that does not starts a
new layer, and is an error of `stepProblems`); a morph declared for it, before any turn or slide,
that can be
interpolated (with its samples when the step is sampled); or nothing, when the two keys draw the
item alike. -/
def continuation (K : MotionKeys) (e : Env) (j : Nat) (v : MotionVersion) (it : Item) :
    Option (Option Move × Option (Array Item)) :=
  let prev := v.items.back?.getD it
  let lands := fun (mv : Move) => (arrival e.frame e.style (mv.pageAffine e.frame) prev it).isNone
  match v.actor.bind (m.moveOf j) with
  | some (.turn c q) => if lands (.turn c q) then some (some (.turn c q), none) else none
  | some (.slide w) => if lands (.slide w) then some (some (.slide w), none) else none
  | some .morph =>
    if v.moves.any MotionVersion.isRigid then none
    else
      let its := if m.samplesOf K j > 1 then v.actor.bind (m.morphItems K j)
        else some #[prev, it]
      match its with
      | some its =>
        if interpolableItems e K.mode its then
          some (some .morph, if its.size > 2 then some its else none)
        else none
      | none => none
  | _ => if itemText e K.mode prev == itemText e K.mode it then some (none, none) else none

/-- The layers of the motion in the environment `e`, and for each key the layers it shows, in its
drawing order (see the module docstring). -/
def versions (K : MotionKeys) (e : Env) : Array MotionVersion × Array (Array Nat) := Id.run do
  let keys := K.figs
  let mut vs : Array MotionVersion := #[]
  let mut perKey : Array (Array Nat) := #[]
  let mut prev : Array Nat := #[]
  for (k, fig) in keys.mapIdx fun k fig => (k, fig) do
    let mut order : Array Nat := #[]
    for it in fig.items do
      -- a layer shown on the key before, not yet continued on this key
      let candidates := prev.filter fun vi =>
        let v := vs.getD vi default
        v.last + 1 == k && v.actor == it.actorId? && !order.contains vi
      let cont := if k == 0 then none else candidates.findSome? fun vi =>
        (m.continuation K e (k - 1) (vs.getD vi default) it).map (vi, ·)
      match cont with
      | some (vi, mv, smp) =>
        vs := vs.modify vi fun v =>
          let samples := match smp with
            | some its => v.samples.push (k - 1, its)
            | none => v.samples
          { v with items := v.items.push it, moves := v.moves.push mv, samples }
        order := order.push vi
      | none =>
        vs := vs.push { actor := it.actorId?, first := k, items := #[it] }
        order := order.push (vs.size - 1)
    perKey := perKey.push order
    prev := order
  return (vs, perKey)

end Motion

/-- The layers of all keys in one drawing order: each key's layers in its order, a layer not seen
before placed after the one before it in its key (at the start for the first). A key whose order
disagrees with this one is reported by `Motion.keyProblems`. -/
def mergeOrder (perKey : Array (Array Nat)) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for seq in perKey do
    let mut cursor : Nat := 0
    for x in seq do
      match out.idxOf? x with
      | some i => cursor := i + 1
      | none =>
        out := out.insertIdxIfInBounds cursor x
        cursor := cursor + 1
  return out

/-- Whether the layers `seq` of a key come in the order `order` has them. -/
def inOrder (order seq : Array Nat) : Bool :=
  let pos := seq.filterMap (order.idxOf? ·)
  pos.size == seq.size && (pos.toList.zip pos.toList.tail).all fun (a, b) => a < b

/-! ### Problems -/

/-- How serious a problem of a motion is. -/
inductive MotionSeverity where
  /-- The motion is wrong: a build warns, or stops under `CheckLevel.fail`. -/
  | error
  /-- Something an author should know (a crossfade where nothing was declared); never stops a
  build. -/
  | note
  deriving BEq, Inhabited, Repr

/-- A problem of a motion. -/
structure MotionProblem where
  /-- How serious it is. -/
  severity : MotionSeverity
  /-- What is wrong, in words. -/
  message : String
  deriving Inhabited, Repr

namespace Motion

variable (m : Motion)

/-- The actors of a key that do not move in a step, drawn differently in its two keys. -/
private def changed (K : MotionKeys) (j : Nat) : Array String :=
  let a := K.figure j
  let b := K.figure (j + 1)
  (a.items.filterMap Item.actorId?).filter fun id =>
    match a.actor? id, b.actor? id with
    | some x, some y =>
      (m.moveOf j id).isNone && itemText K.env K.mode x != itemText K.env K.mode y
    | _, _ => false

/-- The drawings of the items without an id of key `j` that key `j + 1` does not have, and the
other way round (counted with their repetitions). -/
def staticChanges (K : MotionKeys) (j : Nat) : Nat × Nat :=
  let texts := fun (fig : Figure) =>
    (fig.items.filter (·.actorId?.isNone)).map (itemText K.env K.mode)
  let a := texts (K.figure j)
  let b := texts (K.figure (j + 1))
  let missing := fun (xs ys : Array String) => Id.run do
    let mut left := ys
    let mut n := 0
    for x in xs do
      match left.idxOf? x with
      | some i => left := left.eraseIdx! i
      | none => n := n + 1
    return n
  (missing a b, missing b a)

/-- The problems of one step (see the module docstring), `j` from key `j` to key `j + 1`, with the
layers of the motion `vs` (`versions`). -/
def stepProblems (K : MotionKeys) (vs : Array MotionVersion) (j : Nat) :
    Array MotionProblem := Id.run do
  let mut out : Array MotionProblem := #[]
  let err := fun (s : String) => ({ severity := .error, message := s } : MotionProblem)
  let note := fun (s : String) => ({ severity := .note, message := s } : MotionProblem)
  -- what crossfades for an actor: an error under `fail`, a note otherwise
  let actorFade := fun (s : String) =>
    ({ severity := if m.checks == .fail then .error else .note, message := s } : MotionProblem)
  let e := K.env
  let st := e.style
  let a := K.figure j
  let b := K.figure (j + 1)
  let s := m.steps.getD j {}
  let name := s!"step {j + 1} (key {j} to key {j + 1})"
  if s.kind == .idle && !s.moves.isEmpty then
    out := out.push (err s!"{name} is idle but declares moves")
  let mut seen : Array String := #[]
  for (id, _) in s.moves do
    if seen.contains id then out := out.push (err s!"{name}: {id} has more than one move")
    seen := seen.push id
  for (id, mv) in s.moves do
    let inA := a.actor? id
    let inB := b.actor? id
    match mv with
    | .appear =>
      if inA.isSome then out := out.push (err s!"{name}: {id} appears but is already in key {j}")
      if inB.isNone then out := out.push (err s!"{name}: {id} appears but is not in key {j + 1}")
    | .vanish =>
      if inA.isNone then out := out.push (err s!"{name}: {id} vanishes but is not in key {j}")
      if inB.isSome then
        out := out.push (err s!"{name}: {id} vanishes but is still in key {j + 1}")
    | .morph =>
      match inA, inB with
      | some _, some _ =>
        if !vs.any fun v => v.actor == some id && v.visible j && v.visible (j + 1) then
          out := out.push (actorFade s!"{name}: the morph of {id} cannot be interpolated (its \
            drawings differ in more than their path data, a figure between its keys lacks it, or \
            it comes after a turn or a slide); it would be crossfaded")
      | _, _ => out := out.push (err s!"{name}: {id} morphs but is not in both keys")
    | .turn c _ | .slide c =>
      match inA, inB with
      | some x, some y =>
        if !c.isFinite then
          out := out.push (err s!"{name}: the {mv.name} of {id} has a number that is not finite")
        else if x.leaves.any (·.geom.clipped) then
          out := out.push (err s!"{name}: {id} has a line or a ray, which is drawn to the edge of \
            the page and cannot {mv.name}; draw a segment")
        else
          match arrival e.frame st (mv.pageAffine e.frame) x y with
          | some why =>
            out := out.push (err s!"{name}: the {mv.name} of {id} does not carry key {j} onto \
              key {j + 1}: {why}")
          | none =>
            if (arrival e.frame st Affine.id x y).isNone then
              out := out.push (note s!"{name}: {id} is drawn alike before and after its \
                {mv.name}, so the arrival check cannot see the {mv.name}")
        if let .turn _ q := mv then
          if (q ≥ 1 || q ≤ -1) && !s.allowFullTurns then
            out := out.push (err s!"{name}: the turn of {id} is a whole turn or more, which the \
              arrival check cannot see; set allowFullTurns on the step if it is meant")
      | none, _ => out := out.push (err s!"{name}: {id} has a {mv.name} but is not in key {j}")
      | _, none =>
        out := out.push (err s!"{name}: {id} has a {mv.name} but is not in key {j + 1}")
  for id in m.changed K j do
    out := out.push (actorFade s!"{name}: {id} changes without a declared move; it would be \
      crossfaded")
  for id in a.items.filterMap Item.actorId? do
    if !b.hasActor id && (m.moveOf j id).isNone then
      out := out.push (actorFade s!"{name}: {id} leaves without a declared disappearance; it \
        would fade out")
  for id in b.items.filterMap Item.actorId? do
    if !a.hasActor id && (m.moveOf j id).isNone then
      out := out.push (actorFade s!"{name}: {id} comes without a declared appearance; it would \
        fade in")
  let (gone, come) := staticChanges K j
  if gone + come > 0 then
    out := out.push (note s!"{name}: {gone} items without an id fade out and {come} fade in")
  return out

/-- The problems of the motion that its keys and steps show (`Motion.problems` adds the checks of
its layout against the stills): that it is not well formed (`WellFormed`); keys drawn in
different frames; actor ids that are not unique in a key; the layout problems of every key as
drawn (`resolved`, `Figure.problems`); a key that draws its layers in another order than the
motion (`mergeOrder`); an empty title or description (the picture has `role="img"`); and the
problems of each step (`stepProblems`). -/
def keyProblems : Array MotionProblem := Id.run do
  let err := fun (s : String) => ({ severity := .error, message := s } : MotionProblem)
  if !decide m.WellFormed then
    let mut out := #[]
    if m.keys.size != m.steps.size + 1 then
      out := out.push (err s!"the motion has {m.keys.size} keys and {m.steps.size} steps; it \
        needs one key more than steps")
    if m.captions.size != m.keys.size then
      out := out.push (err s!"the motion has {m.captions.size} captions for {m.keys.size} keys")
    if !(m.poster < m.keys.size) then
      out := out.push (err s!"the poster is key {m.poster}, which the motion does not have")
    return out
  let mut out : Array MotionProblem := #[]
  let K := m.keysOf
  let f0 := K.env.frame
  for k in [0:m.keys.size] do
    let fig := K.figure k
    if fig.frame != f0 then
      out := out.push (err s!"key {k} is drawn in another frame than key 0 (a view of its own)")
    let mut seen : Array String := #[]
    for id in fig.items.filterMap Item.actorId? do
      if seen.contains id then out := out.push (err s!"key {k} has two actors with the id {id}")
      seen := seen.push id
    for p in fig.problems do
      out := out.push (err s!"key {k}: {p.message}")
  let strict := fun (s : String) =>
    ({ severity := if m.checks == .fail then .error else .note, message := s } : MotionProblem)
  if m.info.title.isEmpty then
    out := out.push (strict "the motion has no title (its picture has role=\"img\")")
  if m.info.description.isEmpty then
    out := out.push (strict "the motion has no description (its picture has role=\"img\")")
  let (vs, perKey) := m.versions K K.env
  let order := mergeOrder perKey
  for (k, seq) in perKey.mapIdx fun k seq => (k, seq) do
    if !inOrder order seq then
      out := out.push (err s!"key {k} draws its items in another order (one above another) than \
        the earlier keys; the motion cannot show both orders")
  for j in [0:m.steps.size] do
    out := out ++ m.stepProblems K vs j
  return out

end Motion

end PILean.Plane
