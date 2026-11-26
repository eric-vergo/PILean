/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plane.Motion

/-!
# Motions of plane figures: the plan, the animated SVG and the baked frames

A `Motion` (`PILean.Plane.Motion`) is laid out once as a `MotionPlan`: the drawable *layers* of
the motion in drawing order, each with its chain of turns and slides and its opacity, every
animated number given at each boundary of one timeline. Two consumers read the plan, and agree:

* `MotionPlan.toNodesUnchecked`: the moving picture of the animated SVG (`Motion.svg?`). The
  base geometry of every layer is
  drawn once by the plane figures' drawing path (`drawGeom`) and moved by SMIL animations
  (`PILean.Anim.Smil`): each turn is the `animateTransform` of type `rotate` of a group of its own,
  the earliest turn innermost (so that every centre is a point of the page), each slide one of type
  `translate`; a label or a point's marker sits inside a counter-rotation about its anchor by
  minus the whole angle so far, so that its net motion is a translation; fades animate `opacity`
  and morphs `d`. Nothing else is animated, and no static `transform` is written. Every
  animation element is built by `MotionPlan.anim`, so it has the plan's timing (`anim_eq`).
* `MotionPlan.figureAtUnchecked`: the same motion as baked
  drawings on the vector canvas, for raster outputs and tests: at a time, every layer's shapes
  turned and slid by the transform its chain has then (labels and markers translated only),
  at its opacity. The values are the plan's: the numbers the SVG writes (rounded as it writes
  them) at the key times it writes, interpolated as SMIL interpolates them (`MotionClock.value`).

The stills are the key figures (`Motion.keyFigure`), drawn by the plane figures' pipeline; no
still is derived from the animation.

**Layers.** An actor keeps one layer from the key where it appears for as long as each step
carries it there by a declared turn or slide, by a morph that can be interpolated, or leaves it
unchanged; otherwise a new layer begins and the two crossfade. An item without an id is a layer
for as long as consecutive keys draw it identically. The layers are drawn in the order of the
keys (the first key's order, with each later layer placed after the one before it in its key).
Consecutive layers shown on the same keys share one opacity animation, and within it consecutive
layers that move identically in every step share one chain of groups (a rigid body is one chain).

**Morphs** are interpolated in the page's coordinates, so a morph must come before any turn or
slide in its layer (a later one starts a new layer, which crossfades). A morph with figures
between its keys (`Motion.between`) is sampled at `morphSamples` steps of equal time, during
which every animation of the picture runs at constant speed.

**The internal form for several motions on one clock.** Every animated value is a function of
a `MotionPhase` (a key, or a fraction of a step), evaluated at the boundaries of the timeline; the
plan
is computed in a drawing environment (`Motion.planIn`), so a picture of several panels can lay
each motion out in a frame of its own (its origin shifted) on a timeline they share.

## Main definitions

* `MotionPhase`, `MotionClock`, `MotionLink`, `MotionLayer`, `MotionUpright`,
  `MotionPlan`, `Motion.planIn`, `Motion.plan`.
* `Motion.segments`, `Motion.timelineOf`, `Motion.phasesOf`, `Motion.timeline`.
* `MotionPlan.toNodesUnchecked`, `MotionPlan.figureAtUnchecked`, `MotionPlan.markersAt`.

The motion's checked outputs (`Motion.report`, `Motion.svg?`, `Motion.animation?`) and its checks
against the stills and between writer and baker (`Motion.problems`) are in
`PILean.Plane.MotionOutput`; the names that end in `Unchecked` write whatever the problems say.
-/

namespace PILean.Plane

open Canvas Anim Svg

/-! ### Phases and the timeline -/

/-- A moment of a motion: key `key` when `frac = 0`, otherwise the fraction `frac` of the step from
key `key` to key `key + 1`. -/
structure MotionPhase where
  /-- The key, or the step's first key. -/
  key : Nat
  /-- The fraction of the step done, in `[0, 1)`. -/
  frac : Rat
  deriving Inhabited, Repr, DecidableEq

/-- The phase at the fraction `q` of step `j` (key `j + 1` for `q ≥ 1`). -/
def MotionPhase.ofStep (j : Nat) (q : Rat) : MotionPhase :=
  if q ≥ 1 then ⟨j + 1, 0⟩ else ⟨j, q⟩

/-- The fraction of step `j` done at the phase: `0` before the step, `1` after it. -/
def MotionPhase.progress (φ : MotionPhase) (j : Nat) : Rat :=
  if φ.key < j then 0 else if φ.key > j then 1 else φ.frac

/-- `x` rounded to `d` decimals as the SVG writer writes it (`fmtNum`), read back. -/
def quant (d : Nat) (x : Float) : Float := (Raster.parseNumber? (fmtNum x d)).getD x

/-- A page point rounded to 4 decimals. -/
def quantPoint (p : Point) : Point := ⟨quant 4 p.x, quant 4 p.y⟩

/-- The fraction of a step's time at which its easing `e` has done the fraction `y` of the step:
the `x ∈ [0, 1]` with `e.eval x = y`, found by 64 halvings (`Easing.eval` does not decrease), as a
rational to nine decimals. -/
def easedTime (e : Easing) (y : Float) : Rat :=
  let x := Id.run do
    let mut lo : Float := 0
    let mut hi : Float := 1
    for _ in [0:64] do
      let mid := (lo + hi) / 2
      if e.eval mid < y then lo := mid else hi := mid
    return (lo + hi) / 2
  ((x * 1000000000).round.toInt64.toInt : Rat) / 1000000000

namespace Motion

variable (m : Motion)

/-- The segments of the motion's timeline with the phases at their start and end: those of
`Timeline.build` on `animSteps`, a sampled morph's move divided into `samplesOf` segments, the
`i`-th ending where the step's easing has done `(i + 1) / n` of the step (`easedTime`). The
values at those boundaries are the exact fractions `i / n` of the step and the segments are not
eased, so every animation of the step follows its eased motion piecewise linearly, within `1 / n`
of the step's change. -/
def segments (K : MotionKeys) : Array (Segment × MotionPhase × MotionPhase) :=
  let base := Timeline.build m.animSteps m.pacing
  let last := base.keys - 1
  base.segments.flatMap fun s => match s.kind with
    | .rest k => #[(s, ⟨k, 0⟩, ⟨k, 0⟩)]
    | .seamIn => #[(s, ⟨0, 0⟩, ⟨0, 0⟩)]
    | .seamOut => #[(s, ⟨last, 0⟩, ⟨last, 0⟩)]
    | .move j =>
      let n := m.samplesOf K j
      if n ≤ 1 then #[(s, ⟨j, 0⟩, ⟨j + 1, 0⟩)]
      else
        let τ := fun (i : Nat) => if i == 0 then (0 : Rat) else if i ≥ n then 1
          else easedTime s.easing (Exact.toFloat ((i : Rat) / n))
        (Array.range n).map fun (i : Nat) =>
          let q : Rat := i
          let start := s.start + s.dur * τ i
          let dur := s.dur * (τ (i + 1) - τ i)
          let seg : Segment := { s with start, dur, easing := .linear }
          (seg, MotionPhase.ofStep j (q / n), MotionPhase.ofStep j ((q + 1) / n))

/-- The timeline of segments `segs` (see `segments`). -/
def timelineOf (segs : Array (Segment × MotionPhase × MotionPhase)) : Timeline :=
  { Timeline.build m.animSteps m.pacing with segments := segs.map (·.1) }

/-- The phase at each boundary of the timeline of segments `segs`: at the start of the first
segment, then at the end of each. -/
def phasesOf (segs : Array (Segment × MotionPhase × MotionPhase)) : Array MotionPhase :=
  match segs[0]? with
  | none => #[]
  | some (_, p, _) => #[p] ++ segs.map (·.2.2)

/-- The timeline of the motion (see `segments`). -/
def timeline : Timeline := m.timelineOf (m.segments m.keysOf)

end Motion

/-- The timing of the animations as written: the key times and the cycle read back from their
text, and each interval's easing with its control values as written. -/
structure MotionClock where
  /-- The key times, as fractions of the cycle. -/
  times : Array Float
  /-- The easing of each interval. -/
  splines : Array Easing
  /-- The cycle, in seconds. -/
  dur : Float
  deriving Inhabited

namespace MotionClock

/-- The clock of the animations written on the timeline `tl`. -/
def ofTimeline (tl : Timeline) (o : Smil.Options := {}) : MotionClock where
  times := (Smil.times tl o).map fun r =>
    (Raster.parseNumber? (Smil.timeText r)).getD (Exact.toFloat r)
  splines := tl.segments.map fun s =>
    let (a, b, c, d) := s.easing.controls
    .spline (quant 4 a) (quant 4 b) (quant 4 c) (quant 4 d)
  dur := quant 6 (Exact.toFloat tl.cycle)

/-- The interval of key times at the time `t` (seconds, repeated every cycle) and the eased
progress through it, as SMIL computes them for `calcMode="spline"`. -/
def locate (c : MotionClock) (t : Float) : Nat × Float :=
  let u := t / c.dur - (t / c.dur).floor
  let m := c.times.size
  let last := ((List.range m).filter fun i => c.times.getD i 2 ≤ u).getLast?.getD 0
  let i := min last (m - 2)
  let lo := c.times.getD i 0
  let span := c.times.getD (i + 1) 1 - lo
  let x := if span > 0 then (u - lo) / span else 1
  (i, (c.splines.getD i .linear).eval x)

/-- The value at the time `t` of an animation with the values `vals` at the boundaries: the two
values of its interval interpolated number by number with the eased progress. -/
def value (c : MotionClock) (vals : Array (Array Float)) (t : Float) : Array Float :=
  let (i, f) := c.locate t
  let a := vals.getD i #[]
  let b := vals.getD (i + 1) a
  (a.zip b).map fun (p, q) => p + (q - p) * f

end MotionClock

/-! ### Layers -/

/-- A turn or a slide of a chain, on the page: a turn in step `step` about the page point `c` by
`deg` degrees (SVG's measure), or a slide in step `step` by the page vector `d`. -/
inductive MotionLink where
  /-- A turn. -/
  | turn (step : Nat) (c : Point) (deg : Float)
  /-- A slide. -/
  | slide (step : Nat) (d : Point)
  deriving BEq, Inhabited, Repr

namespace MotionLink

/-- The step of the link. -/
def step : MotionLink → Nat
  | .turn j .. | .slide j _ => j

/-- Whether the link is a turn. -/
def isTurn : MotionLink → Bool
  | .turn .. => true
  | .slide .. => false

/-- The value of the link's animation at a phase: `θ cx cy` for a turn, `dx dy` for a slide, as
written. -/
def values (φ : MotionPhase) : MotionLink → Array Float
  | .turn j c deg => #[quant 6 (deg * Exact.toFloat (φ.progress j)), c.x, c.y]
  | .slide j d =>
    let p := Exact.toFloat (φ.progress j)
    #[quant 4 (d.x * p), quant 4 (d.y * p)]

/-- The transform of a value of the link's animation. -/
def affine (l : MotionLink) (v : Array Float) : Affine :=
  match l with
  | .turn .. => rotAbout ⟨v.getD 1 0, v.getD 2 0⟩ (v.getD 0 0)
  | .slide .. => Affine.translate (v.getD 0 0) (v.getD 1 0)

/-- The text of a value of the link's animation. -/
def text (l : MotionLink) (v : Array Float) : String :=
  match l with
  | .turn .. => s!"{fmtNum (v.getD 0 0) 6} {fmtNum (v.getD 1 0) 4} {fmtNum (v.getD 2 0) 4}"
  | .slide .. => s!"{fmtNum (v.getD 0 0) 4} {fmtNum (v.getD 1 0) 4}"

/-- The type of the link's `animateTransform`. -/
def type : MotionLink → String
  | .turn .. => "rotate"
  | .slide .. => "translate"

end MotionLink

/-- The link on the page, through the frame `f`, of a move in step `j`: a turn about the page
point of its centre (rounded as written) by `pageDegrees` of its fraction of a turn, a slide by
the page image of its vector (rounded as written); none for the other moves. -/
def linkOf (f : Frame) (j : Nat) : Option Move → Option MotionLink
  | some (.turn c q) => some (.turn j (quantPoint (f.toScreen c)) (pageDegrees q))
  | some (.slide w) => some (.slide j ⟨quant 4 (f.scale * w.x), quant 4 (-(f.scale * w.y))⟩)
  | _ => none

/-- The link of a move in step `j` is in step `j`. -/
theorem linkOf_step {f : Frame} {j : Nat} {mv : Option Move} {l : MotionLink}
    (h : linkOf f j mv = some l) : l.step = j := by
  unfold linkOf at h
  split at h <;> (try simp at h) <;> (subst h; rfl)

/-- The angle the writer turns by for a turn by `q` of a full turn is `pageDegrees q`, which is
`Exact.toFloat (-(360 * q))`. -/
theorem linkOf_turn (f : Frame) (j : Nat) (c : Point) (q : Rat) :
    linkOf f j (some (.turn c q)) =
      some (.turn j (quantPoint (f.toScreen c)) (Exact.toFloat (-(360 * q)))) := rfl

namespace MotionVersion

variable (v : MotionVersion)

/-- Its opacity at a phase, as written: `1` on the keys that show it, `0` on the others, changing
linearly in the steps between. -/
def opacityAt (φ : MotionPhase) : Float :=
  let a : Float := if v.visible φ.key then 1 else 0
  let b : Float := if v.visible (φ.key + 1) then 1 else 0
  quant 4 (a + (b - a) * Exact.toFloat φ.frac)

/-- The item that gives its drawing at a phase, before any turn or slide: a sample of a sampled
morph, else `itemAtKey`. -/
def geomAt (φ : MotionPhase) : Item :=
  if φ.frac == 0 then v.itemAtKey φ.key
  else match v.samples.find? (·.1 == φ.key) with
    | some (_, its) =>
      let n := its.size - 1
      its.getD (φ.frac * n).floor.toNat (v.itemAtKey φ.key)
    | none => v.itemAtKey φ.key

/-- Its chain of turns and slides on the page through the frame `f`, in order of time: the link
(`linkOf`) of each of its moves. -/
def links (f : Frame) : Array MotionLink :=
  ((List.range v.moves.size).filterMap fun i =>
    linkOf f (v.first + i) (v.moves[i]?.getD none)).toArray

/-- The links of a layer are in strictly increasing order of their steps (so `chainNodes` puts
the earliest innermost). -/
theorem steps_links (f : Frame) : ((v.links f).toList.map MotionLink.step).Pairwise (· < ·) := by
  simp only [links, List.toList_toArray]
  rw [List.pairwise_map]
  refine List.Pairwise.filterMap (R := (· < ·)) _ ?_ List.pairwise_lt_range
  intro a b hab x hx y hy
  rw [linkOf_step hx, linkOf_step hy]
  omega

/-- A link of a layer is the link of one of its moves, and every move that is a turn or a slide
gives one. -/
theorem mem_links (f : Frame) (l : MotionLink) :
    l ∈ v.links f ↔
      ∃ i < v.moves.size, linkOf f (v.first + i) (v.moves[i]?.getD none) = some l := by
  simp [links]

end MotionVersion

/-- Labels and markers of a turning layer held upright by one counter-rotation: their leaves
(consecutive siblings in the item, with one anchor: a point's marker and its label), the anchor
(the page point they turn back about) and the angle of the counter-rotation at each boundary. -/
structure MotionUpright where
  /-- The positions of the leaves among the layer's leaves. -/
  leaves : Array Nat
  /-- The anchor, rounded as written. -/
  anchor : Point
  /-- The values `θ cx cy` of the counter-rotation at each boundary. -/
  values : Array (Array Float)
  deriving Inhabited

/-- A layer laid out on the timeline: its version, chain, the values of every animation at each
boundary, its upright leaves and (for a morph) its drawing at each boundary. -/
structure MotionLayer where
  /-- The version it draws. -/
  version : MotionVersion
  /-- Its chain, in order of time. -/
  links : Array MotionLink
  /-- The values of each link's animation at each boundary. -/
  linkValues : Array (Array (Array Float))
  /-- Its opacity at each boundary, unless it is shown on every key. -/
  opacity : Option (Array Float)
  /-- Its upright leaves (when it turns), in the order of their leaves. -/
  uprights : Array MotionUpright
  /-- The item that gives its drawing at each boundary, when it morphs. -/
  geoms : Option (Array Item)
  /-- The page point that stands for an actor: the first anchor of its first leaf, rounded. -/
  anchor : Option Point
  /-- A prefix for the ids in its drawing, for an actor's later layers (so that ids stay
  unique). -/
  idPrefix : String
  deriving Inhabited

/-- A motion laid out (see the module docstring). -/
structure MotionPlan where
  /-- The drawing environment. -/
  env : Env
  /-- The text mode of the SVG. -/
  mode : TextMode
  /-- The timeline. -/
  timeline : Timeline
  /-- The phase at each boundary. -/
  phases : Array MotionPhase
  /-- The timing as written. -/
  clock : MotionClock
  /-- The layers. -/
  layers : Array MotionLayer
  /-- The layers in drawing order: runs shown on the same keys, each of runs that share a chain. -/
  runs : Array (Array (Array Nat))
  /-- The opacity of the whole moving picture at each boundary under a crossfade seam. -/
  seam : Option (Array Float)
  /-- The background. -/
  background : Shape
  /-- The number of keys. -/
  keys : Nat

/-- Consecutive elements of `xs` with equal `key`, as runs. -/
def runsBy {α β : Type} [BEq β] (key : α → β) (xs : Array α) : Array (Array α) := Id.run do
  let mut out : Array (Array α) := #[]
  for x in xs do
    match out.back? with
    | some run =>
      if run.back?.map key == some (key x) then out := out.pop.push (run.push x)
      else out := out.push #[x]
    | none => out := out.push #[x]
  return out

/-- One child of a group, for `siblingRuns`: a leaf (its position) or the runs of a group. -/
inductive SiblingPart where
  /-- A leaf. -/
  | leaf (k : Nat)
  /-- The runs of a group. -/
  | runs (rs : Array (Array Nat))

/-- The runs of consecutive leaves that are children of one group (a shape item alone is one
run), by position among the item's leaves. -/
def siblingRuns : Item → StateM Nat (Array (Array Nat))
  | .shape .. => do
    let k ← getModify (· + 1)
    pure #[#[k]]
  | .group xs _ => do
    let parts ← xs.attach.mapM fun ⟨x, _⟩ => do
      match x with
      | .shape .. => pure (SiblingPart.leaf (← getModify (· + 1)))
      | .group .. => pure (SiblingPart.runs (← siblingRuns x))
    let mut out : Array (Array Nat) := #[]
    let mut cur : Array Nat := #[]
    for part in parts do
      match part with
      | .leaf k => cur := cur.push k
      | .runs rs =>
        if !cur.isEmpty then out := out.push cur
        cur := #[]
        out := out ++ rs
    if !cur.isEmpty then out := out.push cur
    pure out

namespace Motion

variable (m : Motion)

/-- The motion laid out in the environment `e` (its frame and style), its keys as drawn `K`. -/
def planIn (K : MotionKeys) (e : Env) : MotionPlan := Id.run do
  let segs := m.segments K
  let tl := m.timelineOf segs
  let phases := phasesOf segs
  let st := e.style
  let (vs, perKey) := m.versions K e
  let order := mergeOrder perKey
  let keyCount := m.keys.size
  let mut layers : Array MotionLayer := #[]
  let mut seen : Array String := #[]
  for (vi, v) in vs.mapIdx fun vi v => (vi, v) do
    -- a layer whose recorded incidences change between its keys is drawn without them
    let changes := v.items.any (·.recordsText != (v.items.getD 0 default).recordsText)
    let v := if !changes then v else
      { v with items := v.items.map Item.baseForm,
               samples := v.samples.map fun (j, its) => (j, its.map Item.baseForm) }
    let links := v.links e.frame
    let linkValues := links.map fun l => phases.map (l.values ·)
    let turning := links.any MotionLink.isTurn
    let base := v.items.getD 0 default
    -- the key at which the first turn starts: the drawing there is in the layer's own coordinates
    let turnKey := (links.find? MotionLink.isTurn).map (fun | .turn j .. => j | .slide j _ => j)
    let atTurn := v.itemAtKey (turnKey.getD v.first)
    let leaves := atTurn.leaves
    let anchorOf := fun (i : Nat) => (leaves[i]?).bind fun lf =>
      if lf.geom.upright then some (quantPoint ((anchors e.frame st lf.geom).getD 0 ⟨0, 0⟩))
      else none
    -- consecutive upright siblings with one anchor share one counter-rotation
    let groups := ((siblingRuns base).run' 0).flatMap fun run =>
      (runsBy anchorOf run).filter fun g => (anchorOf (g.getD 0 0)).isSome
    let uprights := if !turning then #[] else groups.map fun g =>
      let a := (anchorOf (g.getD 0 0)).getD ⟨0, 0⟩
      { leaves := g, anchor := a, values := (Array.range phases.size).map fun b =>
          let total := (links.zip linkValues).foldl (init := 0) fun acc (l, vals) =>
            if l.isTurn then acc + ((vals.getD b #[]).getD 0 0) else acc
          #[quant 6 (-total), a.x, a.y] }
    let always := v.first == 0 && v.last + 1 == keyCount
    let morphs := v.moves.any fun | some .morph => true | _ => false
    let anchor := v.actor.bind fun _ =>
      (base.leaves[0]?).map fun lf => quantPoint ((anchors e.frame st lf.geom).getD 0 ⟨0, 0⟩)
    let idPrefix := match v.actor with
      | some id => if seen.contains id then s!"v{vi}-" else ""
      | none => ""
    if let some id := v.actor then seen := seen.push id
    let opacity := if always then none else some (phases.map v.opacityAt)
    let geoms := if morphs then some (phases.map v.geomAt) else none
    layers := layers.push
      { version := v, links, linkValues, uprights, anchor, idPrefix, opacity, geoms }
  let visKey := fun (i : Nat) =>
    let v := (layers.getD i default).version
    if v.first == 0 && v.last + 1 == keyCount then (0, 0) else (v.first + 1, v.last + 1)
  let runs := (runsBy visKey order).map fun run =>
    runsBy (fun i => (layers.getD i default).links) run
  let seam := if tl.segments.any (fun s => s.kind == .seamIn || s.kind == .seamOut) then
    some (Smil.seamLevels tl) else none
  let plan : MotionPlan :=
    { env := e, mode := K.mode, timeline := tl, phases, clock := MotionClock.ofTimeline tl,
      layers, runs, seam, background := (K.figure 0).background, keys := keyCount }
  return plan

/-- The motion laid out in its own environment (`Motion.env`). -/
def plan : MotionPlan := let K := m.keysOf; m.planIn K K.env

end Motion

/-! ### Walking a layer's item -/

/-- The item's leaves turned into `α`s by `leaf` (given each leaf's position among the item's
leaves, `Item.leaves`), with `wrap` putting the metadata of each item around its own. -/
def walkItem {α : Type} (leaf : Nat → Leaf → Array α)
    (wrap : ShapeInfo → Array α → Array α) : Item → StateM Nat (Array α)
  | .shape g l i => do
    let k ← getModify (· + 1)
    pure (wrap i (leaf k ⟨g, l, i⟩))
  | .group xs i => do
    let parts ← xs.attach.mapM fun ⟨x, _⟩ => walkItem leaf wrap x
    pure (wrap i parts.flatten)

/-- The leaf at position `i` of an item, if it has one. -/
def leafOf (it : Item) (i : Nat) : Option Leaf := it.leaves[i]?

/-! ### The SVG writer -/

/-- The node with the attributes `extra` added. -/
def addAttrs (extra : Array (String × String)) : Node → Node
  | .element n as cs => .element n (as ++ extra) cs
  | t => t

/-- The metadata of an item around its nodes, as `Shape.tagged` writes it. -/
def wrapInfo (i : ShapeInfo) (nodes : Array Node) : Array Node :=
  if i.isEmpty then nodes
  else
    let (attrs, kids) := i.svgParts
    #[el "g" attrs (kids ++ nodes)]

/-- A point as the text of a `data-` attribute. -/
def pointText (p : Point) : String := s!"{fmtNum p.x 4} {fmtNum p.y 4}"

namespace MotionPlan

variable (p : MotionPlan)

/-- The animation element of values `vals` at the boundaries. -/
def anim (tag : String) (head : Array (String × String)) (vals : Array String) : Option Node :=
  Smil.emit (Smil.track tag head p.timeline vals {})

/-- The tree `base` with an `animate` of `d` (built by `anim`) in every `path` whose data differs
among `alts` (the same tree at each boundary), at most `fuel` deep. -/
def addMorphs : Nat → Node → Array Node → Node
  | 0, n, _ => n
  | _, .text s, _ => .text s
  | fuel + 1, .element name attrs cs, alts =>
    let anim : Option Node :=
      if name != "path" then none
      else
        let ds := alts.map fun | .element _ as _ => (Smil.attr? as "d").getD "" | _ => ""
        if ds.all (· == ds.getD 0 "") then none
        else p.anim "animate" #[("attributeName", "d")] ds
    let kids := cs.mapIdx fun j c =>
      addMorphs fuel c (alts.map fun | .element _ _ ds => ds.getD j (.text "") | t => t)
    .element name attrs (anim.toArray ++ kids)

/-- The rotation `animateTransform` of the values at the boundaries. -/
def rotateAnim (vals : Array (Array Float)) : Option Node :=
  p.anim "animateTransform" #[("attributeName", "transform"), ("type", "rotate")]
    (vals.map fun v => s!"{fmtNum (v.getD 0 0) 6} {fmtNum (v.getD 1 0) 4} {fmtNum (v.getD 2 0) 4}")

/-- The nodes of a leaf of a layer: its drawing, with an `animate` of `d` on each changing path
when the layer morphs. -/
def leafNodes (L : MotionLayer) (i : Nat) (lf : Leaf) : Array Node :=
  let draw := fun (x : Leaf) => (Shape.group (drawGeom p.env x.look x.geom)).render p.mode
  let base := draw lf
  let nodes := match L.geoms with
    | none => base
    | some gs =>
      let alts := gs.map fun g => draw ((leafOf g i).getD lf)
      base.mapIdx fun j n => p.addMorphs 256 n (alts.map (·.getD j (.text "")))
  nodes

/-- The counter-rotation of upright leaves around their nodes. -/
def uprightNodes (u : MotionUpright) (nodes : Array Node) : Array Node :=
  match p.rotateAnim u.values with
  | some a => #[Smil.group a #[el "g" #[("data-pilean-upright", pointText u.anchor)] nodes]]
  | none => nodes

/-- The position among a layer's uprights of the one that holds leaf `i`. -/
def _root_.PILean.Plane.uprightOf (L : MotionLayer) (i : Nat) : Option Nat :=
  L.uprights.findIdx? (·.leaves.contains i)

/-- The nodes of a group's children, those of one upright together inside its counter-rotation
(`uprightNodes`). -/
def closeUprights (L : MotionLayer) (parts : Array (Option Nat × Array Node)) : Array Node :=
  (runsBy (·.1) parts).flatMap fun run =>
    let nodes := run.flatMap (·.2)
    match (run.getD 0 (none, #[])).1 with
    | some u => p.uprightNodes (L.uprights.getD u default) nodes
    | none => nodes

/-- The nodes of an item of a layer below its top: each leaf's drawing in its metadata, marked
with its upright; a group's children with their uprights closed (`closeUprights`), in its
metadata. -/
def writeItem (L : MotionLayer) : Item → StateM Nat (Array (Option Nat × Array Node))
  | .shape g l i => do
    let k ← getModify (· + 1)
    pure #[(uprightOf L k, wrapInfo i (p.leafNodes L k ⟨g, l, i⟩))]
  | .group xs i => do
    let parts ← xs.attach.mapM fun ⟨x, _⟩ => writeItem L x
    pure #[(none, wrapInfo i (p.closeUprights L parts.flatten))]

/-- The node of a layer: its item's drawing (`writeItem`); an actor's carries `data-pilean-actor`
(its id) and `data-pilean-anchor` (the page point that stands for it). -/
def layerNode (L : MotionLayer) : Array Node :=
  let base := L.version.items.getD 0 default
  let nodes := match base with
    | .shape g l i =>
      -- a top-level leaf keeps its metadata outermost, to carry the actor's attributes
      let ns := p.leafNodes L 0 ⟨g, l, i⟩
      wrapInfo i (match uprightOf L 0 with
        | some u => p.uprightNodes (L.uprights.getD u default) ns
        | none => ns)
    | .group .. => ((p.writeItem L base).run' 0).flatMap (·.2)
  let nodes := match L.version.actor, L.anchor with
    | some id, some a =>
      nodes.map (addAttrs #[("data-pilean-actor", safeToken id), ("data-pilean-anchor",
        pointText a)])
    | _, _ => nodes
  if L.idPrefix.isEmpty then nodes else nodes.map (prefixIds L.idPrefix 256)

/-- Nodes inside the chain of `links` (with their values), the earliest innermost. -/
def chainNodes (links : Array MotionLink) (values : Array (Array (Array Float)))
    (children : Array Node) : Array Node :=
  (links.zip values).foldl (init := children) fun inner (l, vals) =>
    match p.anim "animateTransform" #[("attributeName", "transform"), ("type", l.type)]
        (vals.map l.text) with
    | some a => #[Smil.group a inner]
    | none => inner

/-- Every animation element `anim` builds is its name, its own attributes, its values, then
`Smil.smilTiming` of the plan's timeline: its timing depends on nothing else. `toNodesUnchecked`
builds every animation element it writes through `anim` (the turns and slides of the chains, the
counter-rotations, the opacities, the morphs' path data and the seam), so all of them run on one
clock; that every element comes from `anim` is how the writer is written, not a theorem. -/
theorem anim_eq {tag : String} {head : Array (String × String)} {vals : Array String} {n : Node}
    (h : p.anim tag head vals = some n) :
    n = el tag (head ++ #[("values", ";".intercalate vals.toList)] ++
      Smil.smilTiming p.timeline) := by
  unfold anim Smil.emit at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl

/-- A chain with no links is its children. -/
theorem chainNodes_empty (children : Array Node) : p.chainNodes #[] #[] children = children := by
  simp [chainNodes]

/-- The link added last to a chain is its outermost group: the chain of `links.push l` is the
group of `l`'s animation around the chain of `links` (the earliest link innermost, as turns about
page points require). -/
theorem chainNodes_push (links : Array MotionLink) (values : Array (Array (Array Float)))
    (children : Array Node) (l : MotionLink) (vals : Array (Array Float))
    (h : links.size = values.size) :
    p.chainNodes (links.push l) (values.push vals) children =
      match p.anim "animateTransform" #[("attributeName", "transform"), ("type", l.type)]
          (vals.map l.text) with
      | some a => #[Smil.group a (p.chainNodes links values children)]
      | none => p.chainNodes links values children := by
  simp only [chainNodes, Array.push_eq_append, Array.zip_append h]
  simp

/-- The nodes of the moving picture: every run of layers shown on the same keys in one opacity
animation, inside it every run of layers that share a chain in one chain. -/
def contentNodes : Array Node :=
  p.runs.flatMap fun run =>
    let inner := run.flatMap fun sub =>
      let first := p.layers.getD (sub.getD 0 0) default
      p.chainNodes first.links first.linkValues (sub.flatMap fun i =>
        p.layerNode (p.layers.getD i default))
    let first := p.layers.getD ((run.getD 0 #[]).getD 0 0) default
    match first.opacity.bind fun o => p.anim "animate" #[("attributeName", "opacity")]
        (o.map (fmtNum · 4)) with
    | some a => #[Smil.group a inner]
    | none => inner

/-- The moving picture: the content, inside the seam's fades when there are some. -/
def toNodesUnchecked : Array Node :=
  let content := p.contentNodes
  match p.seam.bind fun s => p.anim "animate" #[("attributeName", "opacity")]
      (s.map (fmtNum · 4)) with
  | some a => #[Smil.group a content]
  | none => content

/-! ### The baker -/

/-- The transform of a chain at the time `t`: each link's at its value then, the earliest
applied first. -/
def chainAt (L : MotionLayer) (t : Float) : Affine :=
  (L.links.zip L.linkValues).foldl (init := Affine.id) fun acc (l, vals) =>
    (l.affine (p.clock.value vals t)).comp acc

/-- The opacity of a layer at the time `t`. -/
def opacityAt (L : MotionLayer) (t : Float) : Float :=
  match L.opacity with
  | some o => (p.clock.value (o.map (#[·])) t).getD 0 1
  | none => 1

/-- The opacity of the whole moving picture at the time `t`. -/
def seamAt (t : Float) : Float :=
  match p.seam with
  | some s => (p.clock.value (s.map (#[·])) t).getD 0 1
  | none => 1

/-- `a` and `b` interpolated with `f`, when their commands agree. -/
def lerpPath (a b : Path) (f : Float) : Option Path :=
  if a.cmds.size != b.cmds.size then none
  else
    (a.cmds.zip b.cmds |>.mapM fun (pr : PathCmd × PathCmd) => match pr with
      | (.move x, .move y) => some (PathCmd.move (x.lerp y f))
      | (.line x, .line y) => some (.line (x.lerp y f))
      | (.quad c x, .quad d y) => some (.quad (c.lerp d f) (x.lerp y f))
      | (.cubic c₁ c₂ x, .cubic d₁ d₂ y) =>
        some (.cubic (c₁.lerp d₁ f) (c₂.lerp d₂ f) (x.lerp y f))
      | (.close, .close) => some .close
      | _ => none).map (⟨·⟩)

/-- Two drawings of the same structure interpolated with `f` (paths point by point; texts must be
the same), at most `fuel` deep. -/
def lerpShape : Nat → Shape → Shape → Float → Option Shape
  | 0, _, _, _ => none
  | _, .path a fill line op, .path b _ _ _, f => (lerpPath a b f).map (.path · fill line op)
  | _, .text s at₁ size ink anchor w rot, .text s' at₂ _ _ _ _ _, f =>
    if s == s' then some (.text s (at₁.lerp at₂ f) size ink anchor w rot) else none
  | fuel + 1, .group cs t op clip, .group ds _ _ _, f =>
    if cs.size != ds.size then none
    else ((cs.zip ds).mapM fun (c, d) => lerpShape fuel c d f).map (.group · t op clip)
  | fuel + 1, .tagged i c, .tagged _ d, f => (lerpShape fuel c d f).map (.tagged i ·)
  | _, _, _, _ => none

/-- The shapes of a leaf of a layer at the time `t`: its drawing (interpolated between the two
boundaries of a morph), turned and slid by its chain, or for an upright leaf of a turning layer
translated by where the chain carries its anchor. -/
def leafShapes (L : MotionLayer) (t : Float) (i : Nat) (lf : Leaf) : Array Shape :=
  let draw := fun (x : Leaf) => drawGeom p.env x.look x.geom
  let shapes := match L.geoms with
    | none => draw lf
    | some gs =>
      let (b, f) := p.clock.locate t
      let a := draw ((leafOf (gs.getD b default) i).getD lf)
      let c := draw ((leafOf (gs.getD (b + 1) default) i).getD lf)
      if a.size != c.size then a
      else ((a.zip c).mapM fun (x, y) => lerpShape 256 x y f).getD a
  let M := p.chainAt L t
  let T := match L.uprights.find? (·.leaves.contains i) with
    | some u =>
      let q := M.apply u.anchor
      Affine.translate (q.x - u.anchor.x) (q.y - u.anchor.y)
    | none => M
  #[.group shapes T]

/-- A layer at the time `t`, on the canvas. -/
def layerShape (L : MotionLayer) (t : Float) : Array Shape :=
  let base := L.version.items.getD 0 default
  (walkItem (p.leafShapes L t) (fun i xs => if i.isEmpty then xs else #[.tagged i (.group xs)])
    base).run' 0

/-- The motion at the time `t` (seconds from its start, repeated every cycle) as a drawing: the
background, then the runs of layers at their opacities, each layer turned and slid as its chain
has it then (see the module docstring). -/
def figureAtUnchecked (t : Float) : Shape :=
  let content := p.runs.flatMap fun run =>
    let first := p.layers.getD ((run.getD 0 #[]).getD 0 0) default
    let inner := run.flatMap fun sub => sub.flatMap fun i =>
      p.layerShape (p.layers.getD i default) t
    if first.opacity.isSome then #[.group inner Affine.id (p.opacityAt first t)] else inner
  .group #[p.background, .group content Affine.id (p.seamAt t)]

/-- The page points that stand for the actors and the upright leaves at the time `t`, in the
order of the SVG document, each with what it stands for (`actor` and the id, or `upright`), its
opacity then and the transform its drawing is under (an actor's chain; for an upright, the
translation that carries its anchor where the chain carries it). -/
def markersAt (t : Float) : Array (String × Point × Float × Affine) :=
  p.runs.flatMap fun run =>
    let first := p.layers.getD ((run.getD 0 #[]).getD 0 0) default
    let o := p.seamAt t * p.opacityAt first t
    run.flatMap fun sub => sub.flatMap fun i =>
      let L := p.layers.getD i default
      let M := p.chainAt L t
      let own := match L.version.actor, L.anchor with
        | some id, some a => #[(s!"actor {safeToken id}", M.apply a, o, M)]
        | _, _ => #[]
      own ++ L.uprights.map fun u =>
        let q := M.apply u.anchor
        ("upright", q, o, Affine.translate (q.x - u.anchor.x) (q.y - u.anchor.y))

end MotionPlan

end PILean.Plane
