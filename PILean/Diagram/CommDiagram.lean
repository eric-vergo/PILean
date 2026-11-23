/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Diagram.Basic

/-!
# Commutative diagrams

A `CommDiagram` is a list of objects (their labels, at exact positions) and a list of arrows
(`CDArrow`: a source, a target, a label, a style, a bend), with optional 2-cells between arrows
and the *commutation claims* `paths`: pairs of paths of arrows from one object that are claimed to
have the same composite. It is drawn as a `Diagram` whose marks are

* the objects, `vertex i`: the label of object `i` centred at its position;
* the arrows, `arrow k i j` for arrow `k` from object `i` to object `j`: the body (a `Shape.path`,
  straight, bent as a quadratic Bézier curve, or a loop as a cubic one, sampled at exact rational
  points and cut where it enters the boxes of the two labels), its tip, the marks of its style
  (a second tip for an epimorphism, a tail tip for a monomorphism, a hook for an inclusion, a bar
  for `↦`, a double line for an equality, a dashed line), and its label beside the middle of the
  body, on its left (or on its right when `swap`);
* the 2-cells, `twoCell k`: a double arrow from the middle of one arrow to the middle of another,
  with its label.

Parallel straight arrows between the same two objects are drawn side by side (`CDLayout.shift`).

The predicate `CommDiagram.Faithful` accounts for every mark: the drawn arrow bodies are exactly
the data's arrows with their sources and targets, in order (`Diagram.arrows`), the texts of the
arrows exactly their labels, and the marks of the objects, of the arrows and of the 2-cells are,
class by class and in order, exactly the builder's at the layout's positions, with no mark of any
other part.

That the diagram *commutes* is a statement about the object, not about the picture. For maps
between finite sets given by their tables (`FinMaps`) it is the decidable `FinMaps.Commutes`: the
maps fit the arrows (`FinMaps.WellTyped`) and the two paths of every claim compose to the same
map. The package `pilean-mathlib` states it for morphisms of a category.

## Main definitions

* `ArrowStyle`, `CDArrow`, `TwoCell`, `CommDiagram`, `CDLayout`, `CommDiagram.layout`
* `CommDiagram.draw`, `CommDiagram.figure`, `CommDiagram.Faithful`, `CommDiagram.Valid`
* `CommDiagram.pathEnd`: the object a path of arrows leads to
* `FinMaps`, `FinMaps.WellTyped`, `FinMaps.apply`, `FinMaps.Commutes`

## Main results

* `CommDiagram.draw_faithful`, `CommDiagram.builder_faithful`: the diagram is faithful.
* `CommDiagram.arrows_draw`: the drawn arrows are `(k, src k, tgt k)`, in order.
-/

namespace PILean.Diagram

/-- How an arrow of a diagram is drawn: the conventions of commutative diagrams. -/
inductive ArrowStyle where
  /-- `→`, a morphism. -/
  | plain
  /-- `↣`, a monomorphism: a second tip at the tail. -/
  | mono
  /-- `↠`, an epimorphism: two tips. -/
  | epi
  /-- `→` with `≅` written beside it, an isomorphism. -/
  | iso
  /-- `↪`, an inclusion: a hook at the tail. -/
  | inclusion
  /-- A dashed arrow, a morphism said to exist (an induced one, say). -/
  | dashed
  /-- `=`, an equality: a double line without a tip. -/
  | equality
  /-- `↦`, an element sent to its image: a bar at the tail. -/
  | mapsTo
  /-- A line without a tip (an edge of a Cayley graph for an involution, say). -/
  | line
  deriving DecidableEq, Repr, Inhabited

/-- An arrow of a diagram. -/
structure CDArrow where
  /-- The source object. -/
  src : Nat
  /-- The target object. -/
  tgt : Nat
  /-- The label, written beside the arrow (none when empty). -/
  label : String := ""
  /-- The style. -/
  style : ArrowStyle := .plain
  /-- The bend: `0` for a straight arrow, otherwise a curve to the left (positive) or to the
  right (negative) of the direction from source to target, whose middle is `bend / 8` of the
  arrow's length away from the straight line. For a loop, its size and side (up for a bend that
  is not negative, down otherwise). -/
  bend : Int := 0
  /-- Whether the label is written on the right of the arrow instead of its left. -/
  swap : Bool := false
  /-- The colour of the arrow's lines. -/
  ink : Ink := .ink
  deriving DecidableEq, Repr, Inhabited

/-- A 2-cell: a double arrow from the middle of arrow `src` to the middle of arrow `tgt`. -/
structure TwoCell where
  /-- The arrow it starts from. -/
  src : Nat
  /-- The arrow it ends at. -/
  tgt : Nat
  /-- The label. -/
  label : String := ""
  deriving DecidableEq, Repr, Inhabited

/-- A diagram of objects and arrows, with its commutation claims. -/
structure CommDiagram where
  /-- The labels of the objects `0, …, n - 1`. -/
  objects : Array String
  /-- The positions of the objects (`y` up; one unit between neighbours on a grid). -/
  pos : Array QPoint
  /-- The arrows, numbered from 0 in order. -/
  arrows : List CDArrow
  /-- The 2-cells. -/
  twoCells : List TwoCell := []
  /-- The commutation claims: `(i, p, q)` claims that the paths of arrows `p` and `q` (arrow
  numbers, in the order they are followed) both start at object `i`, end at the same object,
  and have the same composite. -/
  paths : List (Nat × List Nat × List Nat) := []
  deriving Inhabited

/-- The exact positions and sizes a diagram is drawn with. -/
structure CDLayout where
  /-- The centre of object `i`. -/
  pos : Nat → QPoint
  /-- Half the width and half the height of the box of object `i`'s label: arrows stop at it. -/
  half : Nat → QPoint
  /-- How far arrow `k` is moved across its direction (for parallel arrows), in units of the
  direction's largest coordinate. -/
  shift : Nat → Rat

/-! ### Exact plane geometry -/

/-- The sum of two points. -/
def qadd (p q : QPoint) : QPoint := (p.1 + q.1, p.2 + q.2)

/-- The difference of two points. -/
def qsub (p q : QPoint) : QPoint := (p.1 - q.1, p.2 - q.2)

/-- A point scaled. -/
def qscale (t : Rat) (p : QPoint) : QPoint := (t * p.1, t * p.2)

/-- The vector turned a quarter turn counterclockwise. -/
def qperp (v : QPoint) : QPoint := (-v.2, v.1)

/-- The absolute value of a rational. -/
def qabs (q : Rat) : Rat := if q < 0 then -q else q

/-- The largest absolute coordinate of a vector (its maximum norm). -/
def qnorm (v : QPoint) : Rat := max (qabs v.1) (qabs v.2)

/-- The vector divided by its maximum norm (the vector `(1, 0)` for zero): a direction with
rational coordinates, of maximum norm `1`. -/
def qdir (v : QPoint) : QPoint := if qnorm v = 0 then (1, 0) else qscale (1 / qnorm v) v

/-- The point `p + t v`. -/
def qalong (p v : QPoint) (t : Rat) : QPoint := qadd p (qscale t v)

/-- The largest `t` for which `t v` stays in the box of half sizes `h` around the origin (`0`
for the zero vector). -/
def exitParam (h v : QPoint) : Rat :=
  let a := if v.1 = 0 then none else some (h.1 / qabs v.1)
  let b := if v.2 = 0 then none else some (h.2 / qabs v.2)
  match a, b with
  | some x, some y => min x y
  | some x, none => x
  | none, some y => y
  | none, none => 0

/-- Whether `p` lies outside the box of half sizes `h` around `c`, by more than `g`. -/
def outsideBox (c h : QPoint) (g : Rat) (p : QPoint) : Bool :=
  decide (qabs (p.1 - c.1) > h.1 + g) || decide (qabs (p.2 - c.2) > h.2 + g)

/-- The point of the quadratic Bézier curve with ends `a`, `b` and control `c` at `t`. -/
def quadPoint (a c b : QPoint) (t : Rat) : QPoint :=
  qadd (qadd (qscale ((1 - t) * (1 - t)) a) (qscale (2 * t * (1 - t)) c)) (qscale (t * t) b)

/-- The point of the cubic Bézier curve with ends `a`, `d` and controls `b`, `c` at `t`. -/
def cubicPoint (a b c d : QPoint) (t : Rat) : QPoint :=
  let s := 1 - t
  qadd (qadd (qscale (s * s * s) a) (qscale (3 * s * s * t) b))
    (qadd (qscale (3 * s * t * t) c) (qscale (t * t * t) d))

/-- The number of pieces a curved arrow is sampled with. -/
def curvePieces : Nat := 24

/-- The side of a point a label stands on to be in the direction `n` from it: one of the eight
compass sides, by the signs of `n`'s coordinates and their ratio. -/
def sideToward (n : QPoint) : Side :=
  let x := n.1
  let y := n.2
  if qabs y > 2 * qabs x then (if y > 0 then .above else .below)
  else if qabs x > 2 * qabs y then (if x > 0 then .right else .left)
  else if y > 0 then (if x > 0 then .aboveRight else .aboveLeft)
  else if x > 0 then .belowRight else .belowLeft

/-- The gap between an arrow and the boxes of its objects. -/
def arrowEndGap : Rat := 1 / 20

/-- The world length of an arrow's tip (the segment its arrowhead is drawn on). -/
def tipLength : Rat := 1 / 10

/-- The rational points of a half circle, `(cos φ, sin φ)` for `φ` from `0` to `π` in seven
steps: the hook of an inclusion. -/
def halfCirclePoints : List QPoint :=
  [(1, 0), (4 / 5, 3 / 5), (3 / 5, 4 / 5), (0, 1), (-3 / 5, 4 / 5), (-4 / 5, 3 / 5), (-1, 0)]

namespace CommDiagram

/-- The most objects `figure` draws. -/
def maxObjects : Nat := 200

/-- The most arrows `figure` draws. -/
def maxArrows : Nat := 1000

/-- The most 2-cells `figure` draws. -/
def maxTwoCells : Nat := 200

/-- The number of objects. -/
def n (D : CommDiagram) : Nat := D.objects.size

/-- The label of object `i`. -/
def objectLabel (D : CommDiagram) (i : Nat) : String := D.objects.getD i ""

/-- The data is well formed: a position for every object, every arrow between objects, every
2-cell between arrows, every claim's start an object and its arrows arrows. -/
def Valid (D : CommDiagram) : Bool :=
  D.pos.size == D.n && D.arrows.all (fun a => a.src < D.n && a.tgt < D.n) &&
    D.twoCells.all (fun c => c.src < D.arrows.length && c.tgt < D.arrows.length) &&
    D.paths.all fun (i, p, q) => i < D.n && (p ++ q).all (· < D.arrows.length)

/-- The arrows as `(k, src, tgt)`, in order. -/
def arrowTriples (D : CommDiagram) : List (Nat × Nat × Nat) :=
  D.arrows.zipIdx.map fun (a, k) => (k, a.src, a.tgt)

/-- The object a path of arrows leads to from object `i`, when each arrow starts where the
previous one ends (`none` otherwise). The empty path leads from `i` to `i`. -/
def pathEnd (D : CommDiagram) : List Nat → Nat → Option Nat
  | [], i => some i
  | k :: p, i => match D.arrows[k]? with
    | some a => if a.src = i then D.pathEnd p a.tgt else none
    | none => none

/-! ### Layout -/

/-- The half sizes of the box of a label: `7/200` of a unit per character and `3/50` more
across, `1/10` up and down (the size of 15-pixel text when a unit is about 120 pixels). -/
def labelHalf (s : String) : QPoint := ((7 : Rat) / 200 * s.length + 3 / 50, 1 / 10)

/-- How far each straight arrow is moved across its direction so that parallel arrows (straight
arrows between the same two objects, either way) stand side by side, `1/8` apart: the `m`
arrows of a pair are moved by `(m - 1 - 2 j) / 16` for `j = 0, …, m - 1` to the left of the
direction from the lower-numbered object to the other (so the first is the leftmost, and its
label, on its left, is outside). -/
def shifts (D : CommDiagram) (k : Nat) : Rat :=
  match D.arrows[k]? with
  | none => 0
  | some a =>
    if a.bend ≠ 0 || a.src = a.tgt then 0 else
    let same := fun (b : CDArrow) => b.bend = 0 &&
      ((b.src = a.src && b.tgt = a.tgt) || (b.src = a.tgt && b.tgt = a.src))
    let group := (D.arrows.zipIdx.filter fun (b, _) => same b).map (·.2)
    let m := group.length
    let j := group.idxOf k
    let off : Rat := ((m : Rat) - 1 - (2 * j : Nat)) / 16
    if a.src ≤ a.tgt then off else -off

/-- The layout of `figure`: the objects at `pos`, boxes from their labels' lengths, parallel
arrows side by side. -/
def layout (D : CommDiagram) : CDLayout where
  pos i := D.pos.getD i (0, 0)
  half i := labelHalf (D.objectLabel i)
  shift k := D.shifts k

/-! ### The marks -/

/-- The exact points of the body of an arrow from `s` to `t` (centres of boxes of half sizes `hs`
and `ht`), moved by `off` across its direction and bent by `bend`: a straight segment cut at the
boxes, a quadratic curve sampled at `curvePieces + 1` points and cut where it nears the boxes,
or, from a point to itself, a loop. -/
def bodyPoints (s t hs ht : QPoint) (off : Rat) (bend : Int) : List QPoint :=
  if s = t then
    let up : Rat := if bend < 0 then -1 else 1
    let size : Rat := 1 + qabs (bend : Rat) / 2
    let h := qscale (up * (hs.2 + 2 / 5 * size)) (0, 1)
    let w : QPoint := (1 / 4 * size, 0)
    let b := qadd (qadd s h) (qscale (-1) w)
    let c := qadd (qadd s h) w
    let ps := (List.range (curvePieces + 1)).map fun (k : Nat) =>
      cubicPoint s b c s ((k : Rat) / curvePieces)
    ps.filter (outsideBox s hs arrowEndGap)
  else
    let v := qsub t s
    let L := qnorm v
    if bend = 0 then
      let o := qscale off (qperp (qdir v))
      let s' := qadd s o
      let t' := qadd t o
      let ts := exitParam hs v + arrowEndGap / L
      let te := 1 - exitParam ht v - arrowEndGap / L
      if ts < te then [qalong s' v ts, qalong s' v te] else [s', t']
    else
      let c := qadd (qscale (1 / 2) (qadd s t)) (qscale ((bend : Rat) / 4) (qperp v))
      let ps := (List.range (curvePieces + 1)).map fun (k : Nat) =>
        quadPoint s c t ((k : Rat) / curvePieces)
      let kept := ps.filter fun p => outsideBox s hs arrowEndGap p && outsideBox t ht arrowEndGap p
      if kept.length < 2 then [s, t] else kept

/-- The point of a polyline `ps` a fraction `1/2` along its list of points (the middle point, or
the midpoint of the two middle points). -/
def middleOf (ps : List QPoint) : QPoint :=
  let m := ps.length
  if m % 2 = 1 then ps.getD (m / 2) (0, 0)
  else qscale (1 / 2) (qadd (ps.getD (m / 2 - 1) (0, 0)) (ps.getD (m / 2) (0, 0)))

/-- The direction (of maximum norm 1) along which a path ends: from its last but one point to its
last. -/
def endDir (ps : List QPoint) : QPoint :=
  qdir (qsub (ps.getLastD (0, 0)) (ps.getD (ps.length - 2) (0, 0)))

/-- The direction along which a path starts. -/
def startDir (ps : List QPoint) : QPoint :=
  qdir (qsub (ps.getD 1 (0, 0)) (ps.headD (0, 0)))

/-- The stroke of an arrow's body for its style. -/
def bodyStroke : ArrowStyle → Stroke
  | .dashed => .dashed
  | .equality => .double (1 / 25)
  | _ => .solid

/-- The shapes of an arrow other than its body and texts, for its style: its tip (none for an
equality or a line), a second tip for an epimorphism, a tip at the tail for a monomorphism, a
hook for an inclusion, a bar for `↦`. -/
def tipShapes (style : ArrowStyle) (ps : List QPoint) : List Shape :=
  let e := ps.getLastD (0, 0)
  let s := ps.headD (0, 0)
  let u := endDir ps
  let w := startDir ps
  let tip := Shape.arrow (qalong e u (-tipLength)) e
  match style with
  | .equality | .line => []
  | .epi => [tip, Shape.arrow (qalong e u (-2 * tipLength)) (qalong e u (-tipLength))]
  | .mono => [tip, Shape.arrow s (qalong s w tipLength)]
  | .inclusion =>
    let r : Rat := 1 / 20
    let n := qperp w
    let c := qalong s n r
    [tip, Shape.polyline (halfCirclePoints.map fun p =>
      qadd c (qadd (qscale (-r * p.1) n) (qscale (-r * p.2) w)))]
  | .mapsTo => [tip, Shape.segment (qalong s (qperp w) (1 / 16)) (qalong s (qperp w) (-1 / 16))]
  | _ => [tip]

/-- The direction from source to target the label sides are measured against (up for a loop). -/
def arrowDir (L : CDLayout) (a : CDArrow) : QPoint :=
  if L.pos a.src = L.pos a.tgt then (1, 0) else qsub (L.pos a.tgt) (L.pos a.src)

/-- The side of the body arrow `a`'s label is written on: its left, or its right when `swap`;
above (below) a loop. -/
def labelSide (L : CDLayout) (a : CDArrow) : Side :=
  let v := arrowDir L a
  let n := if a.swap then qperp (qscale (-1) v) else qperp v
  if L.pos a.src = L.pos a.tgt then (if a.bend < 0 then .below else .above) else sideToward n

/-- The other side (for the `≅` of an isomorphism). -/
def otherSide (L : CDLayout) (a : CDArrow) : Side :=
  labelSide L { a with swap := !a.swap, bend := if L.pos a.src = L.pos a.tgt then -1 - a.bend
    else a.bend }

/-- The texts of an arrow: its label (when not empty) and, for an isomorphism, `≅` on the other
side, both at the middle of the body. -/
def arrowTextShapes (L : CDLayout) (a : CDArrow) (ps : List QPoint) : List Shape :=
  let m := middleOf ps
  (if a.label.isEmpty then [] else [Shape.text a.label m (labelSide L a)]) ++
    (if a.style = .iso then [Shape.text "≅" m (otherSide L a)] else [])

/-- The body points of arrow `k`. -/
def arrowPoints (L : CDLayout) (k : Nat) (a : CDArrow) : List QPoint :=
  bodyPoints (L.pos a.src) (L.pos a.tgt) (L.half a.src) (L.half a.tgt) (L.shift k) a.bend

/-- The marks of arrow `k`: its body (a path in its stroke), then its tips, all in the arrow's
ink, then its texts in the ink, all of the part `arrow k src tgt`. -/
def arrowMarksOf (L : CDLayout) (k : Nat) (a : CDArrow) : List Mark :=
  let ps := arrowPoints L k a
  let part := Part.arrow k a.src a.tgt
  { part, shape := .path ps (bodyStroke a.style), ink := a.ink } ::
    ((tipShapes a.style ps).map fun s => { part, shape := s, ink := a.ink }) ++
    (arrowTextShapes L a ps).map fun s => { part, shape := s }

/-- The marks of the objects: the label of object `i` centred at its position. -/
def objectMarks (D : CommDiagram) (L : CDLayout) : List Mark :=
  (List.range D.n).map fun i => { part := .vertex i, shape := .text (D.objectLabel i) (L.pos i) .center }

/-- The marks of all the arrows, arrow by arrow. -/
def arrowMarks (D : CommDiagram) (L : CDLayout) : List Mark :=
  D.arrows.zipIdx.flatMap fun (a, k) => arrowMarksOf L k a

/-- The middle of arrow `k`'s body. -/
def arrowMiddle (D : CommDiagram) (L : CDLayout) (k : Nat) : QPoint :=
  match D.arrows[k]? with
  | some a => middleOf (arrowPoints L k a)
  | none => (0, 0)

/-- The marks of 2-cell `k` from arrow `c.src` to arrow `c.tgt`: a double line over the middle
two-fifths of the way between the arrows' middles, its tip, and its label on its left. -/
def twoCellMarksOf (D : CommDiagram) (L : CDLayout) (k : Nat) (c : TwoCell) : List Mark :=
  let a := D.arrowMiddle L c.src
  let b := D.arrowMiddle L c.tgt
  let v := qsub b a
  let p := qalong a v (3 / 10)
  let q := qalong a v (7 / 10)
  let part := Part.twoCell k
  [{ part, shape := .path [p, q] (.double (1 / 25)) },
    { part, shape := .arrow (qalong q (qdir v) (-tipLength)) q }] ++
    (if c.label.isEmpty then [] else
      [{ part, shape := .text c.label (qscale (1 / 2) (qadd p q)) (sideToward (qperp v)) }])

/-- The marks of all the 2-cells. -/
def twoCellMarks (D : CommDiagram) (L : CDLayout) : List Mark :=
  D.twoCells.zipIdx.flatMap fun (c, k) => D.twoCellMarksOf L k c

/-- The diagram at the layout `L`: the arrows, the 2-cells, then the objects on top; arrows are
drawn to their exact ends (no gap). -/
def draw (D : CommDiagram) (L : CDLayout) : Diagram where
  marks := D.arrowMarks L ++ D.twoCellMarks L ++ D.objectMarks L
  arrowGap := 0

/-- The texts written for the arrows: `(k, s)` for each text `s` of arrow `k`. -/
def arrowTexts (D : CommDiagram) (L : CDLayout) : List (Nat × String) :=
  D.arrows.zipIdx.flatMap fun (a, k) =>
    (arrowTextShapes L a (arrowPoints L k a)).filterMap fun s => match s with
      | .text t _ _ => some (k, t)
      | _ => none

end CommDiagram

/-- Whether a part is an object (`vertex`). -/
def Part.isVertex : Part → Bool
  | .vertex _ => true
  | _ => false

/-- Whether a part is an arrow. -/
def Part.isArrow : Part → Bool
  | .arrow .. => true
  | _ => false

/-- Whether a part is a 2-cell. -/
def Part.isTwoCell : Part → Bool
  | .twoCell _ => true
  | _ => false

/-- The texts the diagram writes for arrows: `(k, s)` for each text `s` of a mark of the part
`arrow k i j`, in order. -/
def Diagram.arrowTexts (d : Diagram) : List (Nat × String) :=
  d.marks.filterMap fun m => match m.part, m.shape with
    | .arrow k _ _, .text s _ _ => some (k, s)
    | _, _ => none

namespace CommDiagram

/-- The diagram draws `D` faithfully at the layout `L`:

* its arrows (`Diagram.arrows`, one body each) are exactly `(k, src, tgt)` for the data's arrows
  `k`, in order;
* the texts of its arrows are exactly their labels (and the `≅` of isomorphisms), in order;
* its marks of objects are exactly the labels of the objects `0, …, n - 1` at their positions;
* its marks of arrows are exactly, arrow by arrow, the body, the tips of the arrow's style and
  its texts at `L`'s positions (`arrowMarks`);
* its marks of 2-cells are exactly the builder's (`twoCellMarks`);
* it has no mark of any other part (no decoration, no vertex dot, nothing else). -/
def Faithful (D : CommDiagram) (L : CDLayout) (d : Diagram) : Prop :=
  d.arrows = D.arrowTriples ∧ d.arrowTexts = D.arrowTexts L ∧
    d.marksWhere Part.isVertex = D.objectMarks L ∧ d.marksWhere Part.isArrow = D.arrowMarks L ∧
    d.marksWhere Part.isTwoCell = D.twoCellMarks L ∧
    d.marks.all (fun m => m.part.isVertex || m.part.isArrow || m.part.isTwoCell) = true

instance (D : CommDiagram) (L : CDLayout) (d : Diagram) : Decidable (D.Faithful L d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- `filterMap` with functions that agree on the list. -/
theorem filterMap_congr_mem {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons, h a (by simp),
      filterMap_congr_mem fun x hx => h x (List.mem_cons_of_mem a hx)]

/-- `flatMap` with functions that agree on the list. -/
theorem flatMap_congr_mem {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.flatMap_cons, h a (by simp),
      flatMap_congr_mem fun x hx => h x (List.mem_cons_of_mem a hx)]

/-- Every mark of arrow `k` is of its part. -/
theorem part_of_mem_arrowMarksOf {L : CDLayout} {k : Nat} {a : CDArrow} {m : Mark}
    (h : m ∈ arrowMarksOf L k a) : m.part = .arrow k a.src a.tgt := by
  simp only [arrowMarksOf, List.cons_append, List.mem_cons, List.mem_append, List.mem_map] at h
  rcases h with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl

/-- Every mark of the arrows is of an arrow's part. -/
theorem isArrow_of_mem_arrowMarks {D : CommDiagram} {L : CDLayout} {m : Mark}
    (h : m ∈ D.arrowMarks L) : m.part.isArrow = true := by
  simp only [arrowMarks, List.mem_flatMap] at h
  obtain ⟨⟨a, k⟩, -, hm⟩ := h
  rw [part_of_mem_arrowMarksOf hm]
  rfl

/-- Every mark of the 2-cells is of a 2-cell's part. -/
theorem isTwoCell_of_mem_twoCellMarks {D : CommDiagram} {L : CDLayout} {m : Mark}
    (h : m ∈ D.twoCellMarks L) : m.part.isTwoCell = true := by
  simp only [twoCellMarks, twoCellMarksOf, List.mem_flatMap] at h
  obtain ⟨⟨c, k⟩, -, hm⟩ := h
  simp only [List.cons_append, List.mem_cons, List.mem_append] at hm
  split at hm <;> simp at hm <;> rcases hm with rfl | rfl | rfl <;> rfl

/-- Every mark of the objects is of an object's part. -/
theorem isVertex_of_mem_objectMarks {D : CommDiagram} {L : CDLayout} {m : Mark}
    (h : m ∈ D.objectMarks L) : m.part.isVertex = true := by
  simp only [objectMarks, List.mem_map] at h
  obtain ⟨i, -, rfl⟩ := h
  rfl

/-- No tip of an arrow is a path or a text. -/
theorem tipShapes_cases (st : ArrowStyle) (ps : List QPoint) (s : Shape)
    (h : s ∈ tipShapes st ps) : (∀ qs t, s ≠ .path qs t) ∧ ∀ t p sd, s ≠ .text t p sd := by
  unfold tipShapes at h
  split at h <;> simp at h <;> (try rcases h with rfl | rfl) <;> (try subst h) <;> simp

/-- The texts of an arrow are texts. -/
theorem arrowTextShapes_text (L : CDLayout) (a : CDArrow) (ps : List QPoint) (s : Shape)
    (h : s ∈ arrowTextShapes L a ps) : ∃ t p sd, s = .text t p sd := by
  unfold arrowTextShapes at h
  simp only [List.mem_append] at h
  rcases h with h | h <;> split at h <;> simp at h <;> exact ⟨_, _, _, h⟩

/-- The arrows read back from the marks of one arrow: its own, once. -/
theorem arrows_arrowMarksOf (L : CDLayout) (k : Nat) (a : CDArrow) :
    (arrowMarksOf L k a).filterMap (fun m => match m.part, m.shape with
      | .arrow k i j, .path _ _ => some (k, i, j)
      | _, _ => none) = [(k, a.src, a.tgt)] := by
  simp only [arrowMarksOf, List.cons_append, List.filterMap_cons, List.filterMap_append,
    List.filterMap_map, List.cons.injEq, true_and]
  rw [List.filterMap_eq_nil_iff.2, List.filterMap_eq_nil_iff.2]
  · rfl
  · intro s hs
    obtain ⟨t, p, sd, rfl⟩ := arrowTextShapes_text L a _ s hs
    rfl
  · intro s hs
    have := (tipShapes_cases _ _ s hs).1
    cases s <;> simp_all

/-- The texts read back from the marks of one arrow: its texts. -/
theorem arrowTexts_arrowMarksOf (L : CDLayout) (k : Nat) (a : CDArrow) :
    (arrowMarksOf L k a).filterMap (fun m => match m.part, m.shape with
      | .arrow k _ _, .text s _ _ => some (k, s)
      | _, _ => none) =
      (arrowTextShapes L a (arrowPoints L k a)).filterMap fun s => match s with
        | .text t _ _ => some (k, t)
        | _ => none := by
  simp only [arrowMarksOf, List.cons_append, List.filterMap_cons, List.filterMap_append,
    List.filterMap_map]
  rw [List.filterMap_eq_nil_iff.2]
  · simp only [List.nil_append]
    apply filterMap_congr_mem
    intro s hs
    obtain ⟨t, p, sd, rfl⟩ := arrowTextShapes_text L a _ s hs
    rfl
  · intro s hs
    have := (tipShapes_cases _ _ s hs).2
    cases s <;> simp_all

/-- The drawn arrows are the data's arrows: `(k, src, tgt)` for arrow `k`, in order. -/
theorem arrows_draw (D : CommDiagram) (L : CDLayout) : (D.draw L).arrows = D.arrowTriples := by
  simp only [Diagram.arrows, draw, List.filterMap_append, arrowMarks, List.filterMap_flatMap,
    arrowTriples]
  rw [flatMap_congr_mem (fun x _ => arrows_arrowMarksOf L x.2 x.1),
    List.filterMap_eq_nil_iff.2 (fun m hm => ?_), List.filterMap_eq_nil_iff.2 (fun m hm => ?_)]
  · generalize D.arrows.zipIdx = l
    induction l with
    | nil => rfl
    | cons x l ih => simp_all [List.flatMap_cons]
  · have := isVertex_of_mem_objectMarks hm
    split <;> simp_all [Part.isVertex]
  · have := isTwoCell_of_mem_twoCellMarks hm
    split <;> simp_all [Part.isTwoCell]

/-- The diagram of `D` is faithful at every layout. -/
theorem draw_faithful (D : CommDiagram) (L : CDLayout) : D.Faithful L (D.draw L) := by
  have hA : ∀ m ∈ D.arrowMarks L, m.part.isArrow = true := fun m hm =>
    isArrow_of_mem_arrowMarks hm
  have hT : ∀ m ∈ D.twoCellMarks L, m.part.isTwoCell = true := fun m hm =>
    isTwoCell_of_mem_twoCellMarks hm
  have hV : ∀ m ∈ D.objectMarks L, m.part.isVertex = true := fun m hm =>
    isVertex_of_mem_objectMarks hm
  have nA : ∀ m : Mark, m.part.isArrow = true → m.part.isVertex = false ∧
      m.part.isTwoCell = false := by
    intro m h; cases hp : m.part <;> simp_all [Part.isArrow, Part.isVertex, Part.isTwoCell]
  have nT : ∀ m : Mark, m.part.isTwoCell = true → m.part.isVertex = false ∧
      m.part.isArrow = false := by
    intro m h; cases hp : m.part <;> simp_all [Part.isArrow, Part.isVertex, Part.isTwoCell]
  have nV : ∀ m : Mark, m.part.isVertex = true → m.part.isArrow = false ∧
      m.part.isTwoCell = false := by
    intro m h; cases hp : m.part <;> simp_all [Part.isArrow, Part.isVertex, Part.isTwoCell]
  refine ⟨arrows_draw D L, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Diagram.arrowTexts, draw, List.filterMap_append, arrowMarks,
      List.filterMap_flatMap, CommDiagram.arrowTexts]
    rw [flatMap_congr_mem fun x _ => arrowTexts_arrowMarksOf L x.2 x.1,
      List.filterMap_eq_nil_iff.2 (fun m hm => ?_), List.filterMap_eq_nil_iff.2 (fun m hm => ?_)]
    · simp
    · have := isVertex_of_mem_objectMarks hm
      split <;> simp_all [Part.isVertex]
    · have := isTwoCell_of_mem_twoCellMarks hm
      split <;> simp_all [Part.isTwoCell]
  · simp only [Diagram.marksWhere, draw, List.filter_append]
    rw [List.filter_eq_nil_iff.2 fun m hm => by simp [(nA m (hA m hm)).1],
      List.filter_eq_nil_iff.2 fun m hm => by simp [(nT m (hT m hm)).1],
      List.filter_eq_self.2 fun m hm => hV m hm]
    simp
  · simp only [Diagram.marksWhere, draw, List.filter_append]
    rw [List.filter_eq_self.2 fun m hm => hA m hm,
      List.filter_eq_nil_iff.2 fun m hm => by simp [(nT m (hT m hm)).2],
      List.filter_eq_nil_iff.2 fun m hm => by simp [(nV m (hV m hm)).1]]
    simp
  · simp only [Diagram.marksWhere, draw, List.filter_append]
    rw [List.filter_eq_nil_iff.2 fun m hm => by simp [(nA m (hA m hm)).2],
      List.filter_eq_self.2 fun m hm => hT m hm,
      List.filter_eq_nil_iff.2 fun m hm => by simp [(nV m (hV m hm)).2]]
    simp
  · simp only [draw, List.all_append, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true]
    exact ⟨⟨fun m hm => .inl (.inr (hA m hm)), fun m hm => .inr (hT m hm)⟩,
      fun m hm => .inl (.inl (hV m hm))⟩

/-- The diagram at its layout, or a note when the data is not well formed (`Valid`) or beyond the
caps. Its width gives about 120 pixels to a unit of the objects' horizontal span. -/
def figure (D : CommDiagram) : Diagram :=
  Diagram.capped (D.objects.size ≤ maxObjects && D.arrows.length ≤ maxArrows &&
      D.twoCells.length ≤ maxTwoCells && D.Valid)
    s!"a diagram of {D.objects.size} objects and {D.arrows.length} arrows that is not well \
      formed or too large to draw" fun _ =>
    let xs := D.pos.toList.map (·.1)
    let span := xs.foldl max 0 - xs.foldl min 0
    { D.draw D.layout with width := min 720 (max 160 (120 * Exact.toFloat span + 90)) }

/-- Well-formed data within the caps is drawn faithfully by `figure`. -/
theorem builder_faithful (D : CommDiagram) (h : (D.objects.size ≤ maxObjects &&
    D.arrows.length ≤ maxArrows && D.twoCells.length ≤ maxTwoCells && D.Valid) = true) :
    D.Faithful D.layout D.figure := by
  unfold figure
  rw [Diagram.capped_of h]
  exact D.draw_faithful _

end CommDiagram

/-! ### Maps between finite sets -/

/-- Maps between finite sets realising a diagram: object `i` is the set `{0, …, card[i] - 1}`
and arrow `k` the map whose table is `fn[k]` (the value at `x` is `fn[k][x]`). -/
structure FinMaps where
  /-- The sizes of the objects. -/
  card : Array Nat
  /-- The tables of the arrows. -/
  fn : Array (Array Nat)
  deriving Inhabited

namespace FinMaps

/-- The size of object `i`. -/
def size (R : FinMaps) (i : Nat) : Nat := R.card.getD i 0

/-- The maps fit the diagram: one table per arrow, the table of arrow `k` has one value for each
element of its source, each value an element of its target. -/
def WellTyped (R : FinMaps) (D : CommDiagram) : Bool :=
  R.fn.size == D.arrows.length && R.card.size == D.n &&
    D.arrows.zipIdx.all fun (a, k) =>
      let f := R.fn.getD k #[]
      f.size == R.size a.src && f.all (· < R.size a.tgt)

/-- The composite of a path of arrows at `x`: the maps applied in the path's order. -/
def apply (R : FinMaps) (p : List Nat) (x : Nat) : Nat :=
  p.foldl (fun y k => (R.fn.getD k #[]).getD y 0) x

/-- The maps make the diagram commute: they fit it, and for every claim `(i, p, q)` both paths
lead from `i` to the same object and agree at every element of object `i`. -/
def Commutes (R : FinMaps) (D : CommDiagram) : Bool :=
  R.WellTyped D && D.paths.all fun (i, p, q) =>
    (D.pathEnd p i).isSome && D.pathEnd p i == D.pathEnd q i &&
      (List.range (R.size i)).all fun x => R.apply p x == R.apply q x

end FinMaps

end PILean.Diagram
