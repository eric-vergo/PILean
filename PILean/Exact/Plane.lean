/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Exact
import PILean.Plane

/-!
# Exact points of plane figures

A plane figure can be built from exact values (rationals, algebraic numbers in some exact
representation) and converted to `Float` at the last step. The interface is two classes:

* `Exact.RealValue α`: a value of `α` denotes a real number, and `ball a k` is a rational ball
  (`RatBall`: a centre and a radius) that contains it, of radius at most `2⁻ᵏ`.
* `Exact.PlanePoint α`: a value of `α` denotes a point of the plane, or a complex number, and
  `re a k`, `im a k` are such balls for its two coordinates (real and imaginary parts).

The core library has no real numbers, so "contains" is what an instance *declares*: its author
states (and, for an algebraic representation, can check exactly: the tests check that the
balls of `√5` and of `ℤ[ζ₅]` contain them by squaring rationals) that the value lies in the ball.
The laws that can be stated without real numbers, a radius between `0` and `2⁻ᵏ`, are the
classes `LawfulRealValue` and `LawfulPlanePoint`; the instances here are exact (radius `0`) and
lawful.

Floating point begins at `RealValue.toFloat` and `PlanePoint.toPoint`: the centre of the ball at
`drawPrecision` (64 bits), converted by `Exact.toFloat`. The ball's radius, at most `2⁻⁶⁴`, is
below the resolution of a `Float` near any coordinate of magnitude `2⁻¹⁰` or more.

A representation that needs a context (the ring `ℤ[ζₙ]` with its tables, say, with elements as
arrays of integer coefficients) gives its instance on a type that carries the context, or on a
type indexed by it (`def Cyc (F : CycField) := Array Int`, with an instance for every `F`).

## Main definitions

* `RatBall`, `sqrtBall`, `isqrt`.
* `RealValue`, `PlanePoint`, `LawfulRealValue`, `LawfulPlanePoint`, `drawPrecision`.
* `RealValue.toFloat`, `PlanePoint.toPoint`.
* Instances for `Rat`, `Int`, `Rat × Rat` and `Int × Int`.
* The builders `Plane.Exact.point`, `segment`, `line`, `ray`, `arrow`, `circle`, `disk`, `arc`,
  `sector`, `polygon`, `polyline`, `angleMark`, `label`.
* `Plane.Exact.IsPoint`, `IsDisk`, `IsSegment`, `IsRegion`: which item of a figure is which exact
  object, in which colour, with which title and which recorded incidences, for specifications.

## Main results

* `PlanePoint.toPoint_ratPair`, `PlanePoint.re_ratPair`, `PlanePoint.im_ratPair`: a rational
  point is its own ball (radius 0) and is drawn at its coordinates converted by `Exact.toFloat`.
* `Plane.drawGeom_point`, `Plane.drawItem_point`, `Plane.drawGeom_segment`,
  `Plane.Env.marker_centred`, `Plane.Exact.pointNearDisk_eq`: a point is drawn
  as a marker centred at the frame's image of it, a segment as the polyline between the images of
  its ends.
* `Plane.Exact.point_draw`, `Plane.Exact.point_draw_default`, `Plane.Exact.segment_draw`,
  `Plane.Exact.points_draw`: the same for
  exact points: what is drawn is at `Frame.toScreen (PlanePoint.toPoint p)`.
* `Plane.Exact.IsPoint.draw`: an item that is an exact point is drawn as a marker in its tone at
  the frame's image of the point's conversion.
* `Plane.Exact.figure_points_draw`: a figure whose items are exact points draws, after its
  background, exactly one marker at the frame's image of each point, in order;
  `Plane.Exact.DrawsExactPoints` and `drawsExactPoints` package it as a figure's specification.

What is proved stops at `Frame.toScreen` of the converted point: the conversion, the frame's
fitting and the rasteriser are floating point and tested, as for plots (`docs/PROOFS.md`).
-/

namespace PILean

namespace Exact

/-- The rational ball `[centre - radius, centre + radius]`. -/
structure RatBall where
  /-- The centre. -/
  centre : Rat
  /-- The radius (not negative in a ball an instance returns). -/
  radius : Rat := 0
  deriving BEq, Inhabited, Repr

namespace RatBall

/-- The lower end. -/
def lo (b : RatBall) : Rat := b.centre - b.radius

/-- The upper end. -/
def hi (b : RatBall) : Rat := b.centre + b.radius

/-- The ball of the closed interval `[lo, hi]`. -/
def ofBounds (lo hi : Rat) : RatBall := ⟨(lo + hi) / 2, (hi - lo) / 2⟩

/-- Whether the rational `q` lies in the ball. -/
def contains (b : RatBall) (q : Rat) : Bool := decide (b.lo ≤ q) && decide (q ≤ b.hi)

/-- The ball of a sum. -/
def add (a b : RatBall) : RatBall := ⟨a.centre + b.centre, a.radius + b.radius⟩

/-- The ball of a product by a rational. -/
def smul (q : Rat) (b : RatBall) : RatBall :=
  ⟨q * b.centre, (if q < 0 then -q else q) * b.radius⟩

/-- The ball of a negation. -/
def neg (b : RatBall) : RatBall := ⟨-b.centre, b.radius⟩

/-- The absolute value of a rational. -/
def absQ (q : Rat) : Rat := if q < 0 then -q else q

/-- The ball of a product: `|a| ρ + |b| σ + σ ρ` around `a b` for balls `(a, σ)`, `(b, ρ)`. -/
def mul (a b : RatBall) : RatBall :=
  ⟨a.centre * b.centre, absQ a.centre * b.radius + absQ b.centre * a.radius + a.radius * b.radius⟩

/-- The ball of a difference. -/
def sub (a b : RatBall) : RatBall := a.add b.neg

end RatBall

/-- `⌊√n⌋`: Newton's iteration from a power of two above `√n`, then corrected by single steps
until `s² ≤ n < (s + 1)²` (each loop bounded by the bit length of `n`). -/
def isqrt (n : Nat) : Nat := Id.run do
  if n < 2 then return n
  let bits := n.log2 + 1
  let mut x := 2 ^ ((bits + 1) / 2)
  for _ in [0:bits + 2] do
    let y := (x + n / x) / 2
    if y ≥ x then break
    x := y
  for _ in [0:bits + 2] do
    if x * x > n then x := x - 1 else break
  for _ in [0:bits + 2] do
    if (x + 1) * (x + 1) ≤ n then x := x + 1 else break
  return x

/-- A rational ball of radius at most `2⁻⁽ᵏ⁺¹⁾` around `√q` for `q ≥ 0` (`√0` for a negative
`q`): with `q = n / d` in lowest terms and `s = ⌊√(n d 4ᵏ)⌋`, `√q = √(n d) / d` lies in
`[s / (2ᵏ d), (s + 1) / (2ᵏ d)]`. Whether a ball holds `√q` can be checked exactly: its lower end
squared is at most `q` and its upper end squared at least `q` (`sqrtCertified`). -/
def sqrtBall (q : Rat) (k : Nat) : RatBall :=
  if q ≤ 0 then ⟨0, 0⟩
  else
    let s := isqrt (q.num.toNat * q.den * 4 ^ k)
    RatBall.ofBounds ((s : Rat) / (2 ^ k * q.den)) (((s + 1 : Nat) : Rat) / (2 ^ k * q.den))

/-- Whether the ball certifiably holds `√q`: its lower end is not negative, its square is at most
`q`, and the upper end's square is at least `q`. -/
def sqrtCertified (q : Rat) (b : RatBall) : Bool :=
  decide (0 ≤ b.lo) && decide (b.lo * b.lo ≤ q) && decide (q ≤ b.hi * b.hi)

/-- The precision at which exact values are converted for drawing: balls of radius at most
`2⁻⁶⁴`. -/
def drawPrecision : Nat := 64

/-- Values that denote real numbers, with rational enclosures: `ball a k` holds the value of
`a` and, in a lawful instance, has a radius between `0` and `2⁻ᵏ`. -/
class RealValue (α : Type) where
  /-- A ball holding the value, of radius at most `2⁻ᵏ`. -/
  ball : α → Nat → RatBall

/-- Values that denote points of the plane (complex numbers), with rational enclosures of their
coordinates: `re a k` and `im a k` hold the abscissa (real part) and the ordinate (imaginary
part) and, in a lawful instance, have radii between `0` and `2⁻ᵏ`. -/
class PlanePoint (α : Type) where
  /-- A ball holding the abscissa (real part), of radius at most `2⁻ᵏ`. -/
  re : α → Nat → RatBall
  /-- A ball holding the ordinate (imaginary part), of radius at most `2⁻ᵏ`. -/
  im : α → Nat → RatBall

/-- The laws of a `RealValue` that can be stated without real numbers: every radius is between
`0` and `2⁻ᵏ` (stated as `radius · 2ᵏ ≤ 1`). -/
class LawfulRealValue (α : Type) [RealValue α] : Prop where
  /-- No radius is negative. -/
  radius_nonneg : ∀ (a : α) (k : Nat), 0 ≤ (RealValue.ball a k).radius
  /-- The radius at precision `k` is at most `2⁻ᵏ`. -/
  radius_le : ∀ (a : α) (k : Nat), (RealValue.ball a k).radius * 2 ^ k ≤ 1

/-- The laws of a `PlanePoint` that can be stated without real numbers: every radius is between
`0` and `2⁻ᵏ`. -/
class LawfulPlanePoint (α : Type) [PlanePoint α] : Prop where
  /-- No radius of an abscissa is negative. -/
  re_nonneg : ∀ (a : α) (k : Nat), 0 ≤ (PlanePoint.re a k).radius
  /-- No radius of an ordinate is negative. -/
  im_nonneg : ∀ (a : α) (k : Nat), 0 ≤ (PlanePoint.im a k).radius
  /-- The radius of an abscissa at precision `k` is at most `2⁻ᵏ`. -/
  re_le : ∀ (a : α) (k : Nat), (PlanePoint.re a k).radius * 2 ^ k ≤ 1
  /-- The radius of an ordinate at precision `k` is at most `2⁻ᵏ`. -/
  im_le : ∀ (a : α) (k : Nat), (PlanePoint.im a k).radius * 2 ^ k ≤ 1

/-- The value as a `Float`: the centre of its ball at `drawPrecision`, converted. This is where
floating point begins. -/
def RealValue.toFloat {α : Type} [RealValue α] (a : α) : Float :=
  Exact.toFloat (RealValue.ball a drawPrecision).centre

/-- The point as a `Float` point: the centres of its balls at `drawPrecision`, converted. This
is where floating point begins. -/
def PlanePoint.toPoint {α : Type} [PlanePoint α] (p : α) : Point :=
  ⟨Exact.toFloat (PlanePoint.re p drawPrecision).centre,
    Exact.toFloat (PlanePoint.im p drawPrecision).centre⟩

/-- A rational is its own ball. -/
instance : RealValue Rat where
  ball q _ := ⟨q, 0⟩

/-- An integer is its own ball. -/
instance : RealValue Int where
  ball n _ := ⟨n, 0⟩

/-- A pair of rationals is the point with these coordinates, its own ball. -/
instance : PlanePoint (Rat × Rat) where
  re p _ := ⟨p.1, 0⟩
  im p _ := ⟨p.2, 0⟩

/-- A pair of integers is the point with these coordinates, its own ball. -/
instance : PlanePoint (Int × Int) where
  re p _ := ⟨p.1, 0⟩
  im p _ := ⟨p.2, 0⟩

/-- The balls of rationals have radius `0`. -/
instance : LawfulRealValue Rat where
  radius_nonneg _ _ := Rat.le_refl
  radius_le _ k := by show (0 : Rat) * 2 ^ k ≤ 1; simp; decide

/-- The balls of integers have radius `0`. -/
instance : LawfulRealValue Int where
  radius_nonneg _ _ := Rat.le_refl
  radius_le _ k := by show (0 : Rat) * 2 ^ k ≤ 1; simp; decide

/-- The balls of rational points have radius `0`. -/
instance : LawfulPlanePoint (Rat × Rat) where
  re_nonneg _ _ := Rat.le_refl
  im_nonneg _ _ := Rat.le_refl
  re_le _ k := by show (0 : Rat) * 2 ^ k ≤ 1; simp; decide
  im_le _ k := by show (0 : Rat) * 2 ^ k ≤ 1; simp; decide

/-- The balls of integer points have radius `0`. -/
instance : LawfulPlanePoint (Int × Int) where
  re_nonneg _ _ := Rat.le_refl
  im_nonneg _ _ := Rat.le_refl
  re_le _ k := by show (0 : Rat) * 2 ^ k ≤ 1; simp; decide
  im_le _ k := by show (0 : Rat) * 2 ^ k ≤ 1; simp; decide

/-- The abscissa ball of a rational point is the abscissa itself, at every precision. -/
theorem PlanePoint.re_ratPair (x y : Rat) (k : Nat) : PlanePoint.re (x, y) k = ⟨x, 0⟩ := rfl

/-- The ordinate ball of a rational point is the ordinate itself, at every precision. -/
theorem PlanePoint.im_ratPair (x y : Rat) (k : Nat) : PlanePoint.im (x, y) k = ⟨y, 0⟩ := rfl

/-- A rational point is drawn at its coordinates converted by `Exact.toFloat`. -/
theorem PlanePoint.toPoint_ratPair (x y : Rat) :
    PlanePoint.toPoint (x, y) = ⟨Exact.toFloat x, Exact.toFloat y⟩ := rfl

/-- An integer point is drawn at its coordinates converted by `Exact.toFloat`. -/
theorem PlanePoint.toPoint_intPair (x y : Int) :
    PlanePoint.toPoint (x, y) = ⟨Exact.toFloat x, Exact.toFloat y⟩ := rfl

/-- A rational is drawn as its conversion by `Exact.toFloat`. -/
theorem RealValue.toFloat_rat (q : Rat) : RealValue.toFloat q = Exact.toFloat q := rfl

/-- Where the point `p` stands relative to the closed disk with centre `c` and radius `r`, decided
from balls of `|p - c|² - r²` at the precisions 16, 32, 64, … up to `maxPrecision`: `outside` once
the ball lies above 0, `inside` once it lies below, `on` when it is exactly 0 (a ball of radius 0
around 0, as for rational data); `none` when no precision tried separates it from 0 (a point on
the boundary of an irrational disk, or one too near it). -/
def diskIncidence? {α γ β : Type} [PlanePoint α] [PlanePoint γ] [RealValue β] (p : α) (c : γ)
    (r : β) (maxPrecision : Nat := 512) : Option Plane.Incidence := Id.run do
  let mut k := 16
  for _ in [0:12] do
    if k > maxPrecision then break
    let dx := (PlanePoint.re p k).sub (PlanePoint.re c k)
    let dy := (PlanePoint.im p k).sub (PlanePoint.im c k)
    let rb := RealValue.ball r k
    let v := ((dx.mul dx).add (dy.mul dy)).sub (rb.mul rb)
    if v.radius == 0 && v.centre == 0 then return some .on
    if v.lo > 0 then return some .outside
    if v.hi < 0 then return some .inside
    k := 2 * k
  return none

end Exact

namespace Plane

open Canvas Exact

/-! ### What the drawing does with a point and a segment -/

/-- Every shape of a marker is the outline of its marker shape (`markerPath`: a circle, a square, a
diamond or a cross) centred at the marker's position. -/
theorem Env.marker_centred (e : Env) (l : Look) (q : Point) :
    ∀ s ∈ e.marker l q, ∃ (r : Float) (f : Option Fill) (ln : Option Line),
      s = .path (markerPath l.marker q r) f ln 1 := by
  intro s hs
  unfold Env.marker at hs
  split at hs
  · simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> split <;> exact ⟨_, _, _, rfl⟩
  · simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs; split <;> exact ⟨_, _, _, rfl⟩

/-- A point is drawn as the marker at the frame's image of it. -/
theorem drawGeom_point (e : Env) (l : Look) (p : Point) :
    drawGeom e l (.point p) = e.marker l (e.frame.toScreen p) := rfl

/-- A segment without an arrowhead is drawn as one stroked polyline from the frame's image of
one end to the image of the other. -/
theorem drawGeom_segment (e : Env) (l : Look) (a b : Point) (h : l.arrowHead = false) :
    drawGeom e l (.segment a b) =
      #[e.strokePath l (Path.polyline #[e.frame.toScreen a, e.frame.toScreen b])] := by
  simp [drawGeom, h]

/-- A point item in any look is drawn as the marker at the frame's image of the point, inside a
group carrying its metadata when it has some. -/
theorem drawItem_point (e : Env) (p : Point) (l : Look) (i : ShapeInfo) :
    drawItem e (.shape (.point p) l i) =
      if i.isEmpty then e.marker l (e.frame.toScreen p)
      else #[.tagged i (.group (e.marker l (e.frame.toScreen p)))] := by
  simp [drawItem, drawGeom]

/-- An item without metadata is drawn as its element. -/
theorem drawItem_shape (e : Env) (g : Geom) (l : Look) :
    drawItem e (.shape g l {}) = drawGeom e l g := by
  simp [drawItem, ShapeInfo.isEmpty]

/-! ### Builders from exact values -/

namespace Exact

variable {α β : Type} [PlanePoint α] [RealValue β]

/-- The exact point `p`. -/
def point (p : α) : Item := Plane.point (PlanePoint.toPoint p)

/-- The segment between exact points. -/
def segment (a b : α) : Item := Plane.segment (PlanePoint.toPoint a) (PlanePoint.toPoint b)

/-- The line through exact points, clipped to the frame. -/
def line (a b : α) : Item := Plane.line (PlanePoint.toPoint a) (PlanePoint.toPoint b)

/-- The ray from an exact point through another, clipped to the frame. -/
def ray (a b : α) : Item := Plane.ray (PlanePoint.toPoint a) (PlanePoint.toPoint b)

/-- The arrow between exact points. -/
def arrow (a b : α) : Item := Plane.arrow (PlanePoint.toPoint a) (PlanePoint.toPoint b)

/-- The circle with an exact centre and an exact radius. -/
def circle (c : α) (r : β) : Item := Plane.circle (PlanePoint.toPoint c) (RealValue.toFloat r)

/-- The closed disk with an exact centre and an exact radius. -/
def disk (c : α) (r : β) : Item := Plane.disk (PlanePoint.toPoint c) (RealValue.toFloat r)

/-- An arc with an exact centre and an exact radius, between angles in radians. -/
def arc (c : α) (r : β) (θ₀ θ₁ : Float) : Item :=
  Plane.arc (PlanePoint.toPoint c) (RealValue.toFloat r) θ₀ θ₁

/-- A sector with an exact centre and an exact radius, between angles in radians. -/
def sector (c : α) (r : β) (θ₀ θ₁ : Float) : Item :=
  Plane.sector (PlanePoint.toPoint c) (RealValue.toFloat r) θ₀ θ₁

/-- The polygon with exact vertices. -/
def polygon (vs : List α) : Item := Plane.polygon (vs.map PlanePoint.toPoint).toArray

/-- The polyline through exact points. -/
def polyline (vs : List α) : Item := Plane.polyline (vs.map PlanePoint.toPoint).toArray

/-- An angle mark at an exact point. -/
def angleMark (c : α) (θ₀ θ₁ : Float) (radius : Option Float := none) : Item :=
  Plane.angleMark (PlanePoint.toPoint c) θ₀ θ₁ radius

/-- A label at an exact point. -/
def label (s : String) (p : α) (place : Placement := .center) (offset : Option Float := none) :
    Item :=
  Plane.label s (PlanePoint.toPoint p) place offset

/-- The exact point `p` with where it stands relative to the closed disk `(c, r)` recorded
(`Item.incident`, named `what`), when `Exact.diskIncidence?` decides it; otherwise the point
alone, which the layout checks report if it is drawn too near the disk's boundary to be seen. -/
def pointNearDisk {γ : Type} [PlanePoint γ] (p : α) (c : γ) (r : β) (what : String) : Item :=
  match diskIncidence? p c r with
  | some rel => (point p).incident rel what
  | none => point p

/-- `pointNearDisk` is a point item at the conversion of the exact point, whatever it records. -/
theorem pointNearDisk_eq {γ : Type} [PlanePoint γ] (p : α) (c : γ) (r : β) (what : String) :
    ∃ (l : Look) (i : ShapeInfo),
      pointNearDisk p c r what = .shape (.point (PlanePoint.toPoint p)) l i := by
  unfold pointNearDisk
  split
  · simp [point, Plane.point, Item.incident, Item.mapLook, Item.mapInfo]
  · exact ⟨{}, {}, rfl⟩

/-- The intersection of two closed disks with exact centres and radii (a lens when their circles
cross), bounded by arcs of the circles. -/
def lens (c₁ c₂ : α) (r₁ r₂ : β) : Item :=
  Plane.lens (PlanePoint.toPoint c₁) (RealValue.toFloat r₁) (PlanePoint.toPoint c₂)
    (RealValue.toFloat r₂)

/-- The union of two closed disks with exact centres and radii. -/
def diskUnion (c₁ c₂ : α) (r₁ r₂ : β) : Item :=
  Plane.diskUnion (PlanePoint.toPoint c₁) (RealValue.toFloat r₁) (PlanePoint.toPoint c₂)
    (RealValue.toFloat r₂)

/-- The first closed disk without the second, with exact centres and radii. -/
def diskDifference (c₁ c₂ : α) (r₁ r₂ : β) : Item :=
  Plane.diskDifference (PlanePoint.toPoint c₁) (RealValue.toFloat r₁) (PlanePoint.toPoint c₂)
    (RealValue.toFloat r₂)

/-- A tick mark at the exact point `p` across the segment from `a` to `b`. -/
def tickAt (p a b : α) (length : Option Float := none) : Item :=
  Plane.tick (PlanePoint.toPoint p) (PlanePoint.toPoint b - PlanePoint.toPoint a) length

/-- A label beside the segment between exact points, at its middle, on the clear side. -/
def labelBeside (s : String) (a b : α) (offset : Option Float := none) : Item :=
  Plane.labelBeside s (PlanePoint.toPoint a) (PlanePoint.toPoint b) offset

/-- An exact point is the point item at its conversion. -/
theorem point_eq (p : α) : point p = .shape (.point (PlanePoint.toPoint p)) := rfl

/-- An exact segment is the segment item between the conversions of its ends. -/
theorem segment_eq (a b : α) :
    segment a b = .shape (.segment (PlanePoint.toPoint a) (PlanePoint.toPoint b)) := rfl

/-- An exact point, in any look, is drawn as the marker at the frame's image of its
conversion. -/
theorem point_draw (e : Env) (l : Look) (p : α) :
    drawItem e ((point p).mapLook fun _ => l) =
      e.marker l (e.frame.toScreen (PlanePoint.toPoint p)) := by
  simp [point, Plane.point, Item.mapLook, drawItem, ShapeInfo.isEmpty, drawGeom]

/-- An exact point in its default look is drawn as the default marker at the frame's image of
its conversion. -/
theorem point_draw_default (e : Env) (p : α) :
    drawItem e (point p) = e.marker {} (e.frame.toScreen (PlanePoint.toPoint p)) := by
  simp [point, Plane.point, drawItem, ShapeInfo.isEmpty, drawGeom]

/-- An exact segment, in a look without an arrowhead, is drawn as the polyline between the
frame's images of the conversions of its ends. -/
theorem segment_draw (e : Env) (l : Look) (a b : α) (h : l.arrowHead = false) :
    drawItem e ((segment a b).mapLook fun _ => l) =
      #[e.strokePath l (Path.polyline
        #[e.frame.toScreen (PlanePoint.toPoint a), e.frame.toScreen (PlanePoint.toPoint b)])] := by
  simp [segment, Plane.segment, Item.mapLook, drawItem, ShapeInfo.isEmpty, drawGeom, h]

/-- Exact points in their default look are drawn, in order, as one marker at the frame's image
of each point's conversion. -/
theorem points_draw (e : Env) (ps : List α) :
    (ps.map point).toArray.flatMap (drawItem e) =
      (ps.map fun p => e.marker {} (e.frame.toScreen (PlanePoint.toPoint p))).toArray.flatten := by
  have one := point_draw_default (α := α) e
  apply Array.ext'
  simp only [Array.toList_flatMap, Array.toList_flatten, List.map_map]
  induction ps with
  | nil => rfl
  | cons p ps ih => simp_all

/-- A figure whose items are exact points in their default look draws, after its background,
exactly one marker at the frame's image of each point's conversion, in order. -/
theorem figure_points_draw (fig : Figure) (ps : List α)
    (h : fig.items = (ps.map point).toArray) :
    fig.draw = .tagged fig.info (.group (#[fig.background] ++
      (ps.map fun p => fig.env.marker {}
        (fig.env.frame.toScreen (PlanePoint.toPoint p))).toArray.flatten)) := by
  rw [Figure.draw_eq, h, points_draw]

/-! ### What an item is, in exact terms

A figure's specification says which item is which exact object, in which colour, with which
title and which recorded incidences, so that a theorem about the exact numbers (that a point is
on a circle, say) is a theorem about the item that draws them. For an item built with the
builders below and the modifiers, `simp` with the predicate, the builders and the modifiers used
(and `Item.mapLook`, `Item.mapInfo`) proves it. -/

/-- The item is the exact point `p` in the tone `t` with exactly the incidences `rels` recorded
(`Item.incident`): a point item at the conversion of `p`. -/
def IsPoint (it : Item) (p : α) (t : Tone) (rels : Array (Incidence × String)) : Prop :=
  ∃ (l : Look) (i : ShapeInfo), it = .shape (.point (PlanePoint.toPoint p)) l i ∧ l.tone = t ∧
    l.incidences = rels

/-- The item is the closed disk with the exact centre `c` and radius `r`, in the tone `t`, with
the title `title` (the name incidences refer to it by). -/
def IsDisk (it : Item) (c : α) (r : β) (t : Tone) (title : String) : Prop :=
  ∃ (l : Look) (i : ShapeInfo),
    it = .shape (.disk (PlanePoint.toPoint c) (RealValue.toFloat r)) l i ∧ l.tone = t ∧
      i.title = title

/-- The item is the segment between the exact points `a` and `b`, in the tone `t`, with the title
`title`. -/
def IsSegment (it : Item) (a b : α) (t : Tone) (title : String) : Prop :=
  ∃ (l : Look) (i : ShapeInfo),
    it = .shape (.segment (PlanePoint.toPoint a) (PlanePoint.toPoint b)) l i ∧ l.tone = t ∧
      i.title = title

/-- The item is the region `op` of the closed disks `(c₁, r₁)` and `(c₂, r₂)` with exact centres
and radii (a lens for `.intersection`), in the tone `t`, with the title `title`. -/
def IsRegion (it : Item) (op : RegionOp) (c₁ c₂ : α) (r₁ r₂ : β) (t : Tone) (title : String) :
    Prop :=
  ∃ (l : Look) (i : ShapeInfo),
    it = .shape (.disks op (PlanePoint.toPoint c₁) (RealValue.toFloat r₁) (PlanePoint.toPoint c₂)
      (RealValue.toFloat r₂)) l i ∧ l.tone = t ∧ i.title = title

/-- An item that is the exact point `p` in the tone `t` is drawn as a marker in that tone at the
frame's image of the conversion of `p` (inside a group with its metadata when it has some). -/
theorem IsPoint.draw {it : Item} {p : α} {t : Tone} {rels : Array (Incidence × String)}
    (h : IsPoint it p t rels) (e : Env) :
    ∃ (l : Look) (i : ShapeInfo), l.tone = t ∧ drawItem e it =
      if i.isEmpty then e.marker l (e.frame.toScreen (PlanePoint.toPoint p))
      else #[.tagged i (.group (e.marker l (e.frame.toScreen (PlanePoint.toPoint p))))] := by
  obtain ⟨l, i, rfl, ht, _⟩ := h
  exact ⟨l, i, ht, drawItem_point e _ l i⟩

/-- The hypotheses can be met: the point `(1, 2)` in accent 0, recorded on the element titled
`"c"`, is such an item. -/
example : IsPoint ((point ((1, 2) : Int × Int)).accent 0 |>.incident .on "c") ((1, 2) : Int × Int)
    (.accent 0) #[(.on, "c")] := by
  simp [IsPoint, point, Plane.point, Item.incident, Item.accent, Item.tone, Item.mapLook,
    Item.mapInfo]

/-- The specification of a figure of exact points, ready to link with `figure_proves`: its items
are exactly the points `ps` in their default look, and its drawing is its background followed by
one marker at the frame's image of each point's conversion, in order. The statement names the
figure, so `theorem fig_spec : DrawsExactPoints fig ps := drawsExactPoints rfl` and
`figure_proves fig fig_spec` link it. -/
def DrawsExactPoints (fig : Figure) (ps : List α) : Prop :=
  fig.items = (ps.map point).toArray ∧
    fig.draw = .tagged fig.info (.group (#[fig.background] ++
      (ps.map fun p => fig.env.marker {}
        (fig.env.frame.toScreen (PlanePoint.toPoint p))).toArray.flatten))

/-- A figure whose items are the exact points `ps` satisfies `DrawsExactPoints`. -/
theorem drawsExactPoints {fig : Figure} {ps : List α} (h : fig.items = (ps.map point).toArray) :
    DrawsExactPoints fig ps :=
  ⟨h, figure_points_draw fig ps h⟩

/-- The hypotheses can be met: the integer points `(0, 0)` and `(1, 2)` are drawn at the
frame's images of `(0, 0)` and `(1, 2)`. -/
example (fig : Figure) (h : fig.items = #[point ((0, 0) : Int × Int), point ((1, 2) : Int × Int)]) :
    fig.draw = .tagged fig.info (.group (#[fig.background] ++
      #[fig.env.marker {}
          (fig.env.frame.toScreen ⟨Exact.toFloat (0 : Int), Exact.toFloat (0 : Int)⟩),
        fig.env.marker {}
          (fig.env.frame.toScreen ⟨Exact.toFloat (1 : Int), Exact.toFloat (2 : Int)⟩)
        ].flatten)) :=
  figure_points_draw (α := Int × Int) fig [(0, 0), (1, 2)] h

end Exact

end Plane

end PILean
