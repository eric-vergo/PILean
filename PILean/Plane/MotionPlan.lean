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

* `MotionPlan.toNodes`, `Motion.toSvg`: the animated SVG. The base geometry of every layer is
  drawn once by the plane figures' drawing path (`drawGeom`) and moved by SMIL animations
  (`PILean.Anim.Smil`): each turn is the `animateTransform` of type `rotate` of a group of its own,
  the earliest turn innermost (so that every centre is a point of the page), each slide one of type
  `translate`; a label or a point's marker sits inside a counter-rotation about its anchor by
  minus the whole angle so far, so that its net motion is a translation; fades animate `opacity`
  and morphs `d`. Nothing else is animated, and no static `transform` is written.
* `MotionPlan.figureAt`, `Motion.figureAt`, `Motion.toAnimation`: the same motion as baked
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
* `MotionPlan.toNodes`, `Motion.svgRoot`, `Motion.toSvg`, `MotionPlan.figureAt`, `Motion.figureAt`,
  `MotionPlan.markersAt`, `Motion.toAnimation`.
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

namespace Motion

variable (m : Motion)

/-- The segments of the motion's timeline with the phases at their start and end: those of
`Timeline.build` on `animSteps`, a sampled morph's move divided into `samplesOf` segments of equal
time, not eased. -/
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
      else (Array.range n).map fun (i : Nat) =>
        let q : Rat := i
        let seg : Segment :=
          { s with start := s.start + s.dur * q / n, dur := s.dur / n, easing := .linear }
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

/-- Its chain of turns and slides on the page through the frame `f`, in order of time. -/
def links (f : Frame) : Array MotionLink :=
  (v.moves.mapIdx fun i mv => (v.first + i, mv)).filterMap fun (j, mv) => match mv with
    | some (.turn c q) => some (.turn j (quantPoint (f.toScreen c)) (pageDegrees q))
    | some (.slide w) => some (.slide j ⟨quant 4 (f.scale * w.x), quant 4 (-(f.scale * w.y))⟩)
    | _ => none

end MotionVersion

/-- The layers of all keys in one drawing order: each key's layers in its order, a layer not seen
before placed after the one before it in its key (at the start for the first). -/
def mergeOrder (perKey : Array (Array Nat)) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for seq in perKey do
    let mut cursor : Nat := 0
    for x in seq do
      match out.idxOf? x with
      | some i => cursor := i + 1
      | none =>
        out := (out.toList.take cursor ++ [x] ++ out.toList.drop cursor).toArray
        cursor := cursor + 1
  return out

/-- A label or a marker of a turning layer, held upright: its leaf, its anchor (the page point it
turns back about) and the angle of its counter-rotation at each boundary. -/
structure MotionUpright where
  /-- The position of the leaf among the layer's leaves. -/
  leaf : Nat
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
  /-- Its upright leaves (when it turns). -/
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
  for vi in [0:vs.size] do
    let v := vs[vi]!
    let links := v.links e.frame
    let linkValues := links.map fun l => phases.map (l.values ·)
    let turning := links.any MotionLink.isTurn
    let base := v.items.getD 0 default
    -- the key at which the first turn starts: the drawing there is in the layer's own coordinates
    let turnKey := (links.find? MotionLink.isTurn).map (fun | .turn j .. => j | .slide j _ => j)
    let atTurn := v.itemAtKey (turnKey.getD v.first)
    let uprights := if !turning then #[] else
      (atTurn.leaves.mapIdx fun i lf => (i, lf)).filterMap fun (i, lf) =>
        if !lf.geom.upright then none else
          let a := quantPoint ((anchors e.frame st lf.geom).getD 0 ⟨0, 0⟩)
          some { leaf := i, anchor := a, values := (Array.range phases.size).map fun b =>
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

/-- The tree `base` with an `animate` of `d` in every `path` whose data differs among `alts` (the
same tree at each boundary), at most `fuel` deep. -/
def addMorphs (tl : Timeline) : Nat → Node → Array Node → Node
  | 0, n, _ => n
  | _, .text s, _ => .text s
  | fuel + 1, .element name attrs cs, alts =>
    let anim : Option Node :=
      if name != "path" then none
      else
        let ds := alts.map fun | .element _ as _ => (Smil.attr? as "d").getD "" | _ => ""
        if ds.all (· == ds.getD 0 "") then none
        else Smil.emit (Smil.track "animate" #[("attributeName", "d")] tl ds {})
    let kids := cs.mapIdx fun j c =>
      addMorphs tl fuel c (alts.map fun | .element _ _ ds => ds.getD j (.text "") | t => t)
    .element name attrs (anim.toArray ++ kids)

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

/-- The rotation `animateTransform` of the values at the boundaries. -/
def rotateAnim (vals : Array (Array Float)) : Option Node :=
  p.anim "animateTransform" #[("attributeName", "transform"), ("type", "rotate")]
    (vals.map fun v => s!"{fmtNum (v.getD 0 0) 6} {fmtNum (v.getD 1 0) 4} {fmtNum (v.getD 2 0) 4}")

/-- The nodes of a leaf of a layer: its drawing, with an `animate` of `d` on each changing path
when the layer morphs, held upright by a counter-rotation when it is an upright leaf of a turning
layer. -/
def leafNodes (L : MotionLayer) (i : Nat) (lf : Leaf) : Array Node :=
  let draw := fun (x : Leaf) => (Shape.group (drawGeom p.env x.look x.geom)).render p.mode
  let base := draw lf
  let nodes := match L.geoms with
    | none => base
    | some gs =>
      let alts := gs.map fun g => draw ((leafOf g i).getD lf)
      base.mapIdx fun j n => addMorphs p.timeline 256 n (alts.map (·.getD j (.text "")))
  match L.uprights.find? (·.leaf == i) with
  | some u =>
    match p.rotateAnim u.values with
    | some a => #[Smil.group a #[el "g" #[("data-pilean-upright", pointText u.anchor)] nodes]]
    | none => nodes
  | none => nodes

/-- The node of a layer: its item's drawing (`leafNodes`, `wrapInfo`); an actor's carries
`data-pilean-actor` (its id) and `data-pilean-anchor` (the page point that stands for it). -/
def layerNode (L : MotionLayer) : Array Node :=
  let base := L.version.items.getD 0 default
  let nodes := (walkItem (p.leafNodes L) wrapInfo base).run' 0
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
def toNodes : Array Node :=
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
  let T := match L.uprights.find? (·.leaf == i) with
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
def figureAt (t : Float) : Shape :=
  let content := p.runs.flatMap fun run =>
    let first := p.layers.getD ((run.getD 0 #[]).getD 0 0) default
    let inner := run.flatMap fun sub => sub.flatMap fun i =>
      p.layerShape (p.layers.getD i default) t
    if first.opacity.isSome then #[.group inner Affine.id (p.opacityAt first t)] else inner
  .group #[p.background, .group content Affine.id (p.seamAt t)]

/-- The page points that stand for the actors and the upright leaves at the time `t`, in the
order of the SVG document, each with what it stands for (`actor` and the id, or `upright`) and
its opacity then. -/
def markersAt (t : Float) : Array (String × Point × Float) :=
  p.runs.flatMap fun run =>
    let first := p.layers.getD ((run.getD 0 #[]).getD 0 0) default
    let o := p.seamAt t * p.opacityAt first t
    run.flatMap fun sub => sub.flatMap fun i =>
      let L := p.layers.getD i default
      let M := p.chainAt L t
      let own := match L.version.actor, L.anchor with
        | some id, some a => #[(s!"actor {safeToken id}", M.apply a, o)]
        | _, _ => #[]
      own ++ L.uprights.map fun u => ("upright", M.apply u.anchor, o)

end MotionPlan

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

/-- The motion as an animated SVG document (`svgRoot`). -/
def toSvg : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++ Svg.render 0 m.svgRoot ++ "\n"

/-- The motion at the time `t` (seconds) as a drawing (`MotionPlan.figureAt`). -/
def figureAt (t : Float) : Shape := m.plan.figureAt t

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
