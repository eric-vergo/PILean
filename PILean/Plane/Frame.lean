/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plane.Basic

/-!
# The frame of a plane figure

A `Frame` maps world coordinates (`y` up) to the page (`y` down) with one scale for both axes, so
circles stay round and angles true: `toScreen p = (ox + s x, oy - s y)`. `Frame.fit` finds the
largest scale at which a set of *reaches* fits a page of a given width (and, optionally, height)
inside a padding. A reach is a world point together with how far, in pixels, what is drawn at it
extends around its image: a marker's radius, half a stroke, a label's box. Pixel extents do not
grow with the scale, so a label at the edge of a figure gets the room it needs at every scale.

For a scale `s` the reaches fit across exactly when `max (pad - s xᵢ - lᵢ) ≤ min (W - pad - s xⱼ
- rⱼ)` (`lᵢ`, `rᵢ` the left and right extents), that is when `s (xⱼ - xᵢ) ≤ W - 2 pad + lᵢ - rⱼ`
for every pair. When the extents fit at scale 0 (every right-hand side is at least 0: no label is
wider than the page), the scales that fit form an interval from 0, and `fit` finds its end by
bisection (60 halvings); it then centres the drawing in the room left and, without a given
height, makes the page as tall as the reaches need, rounded up to a whole pixel. Extents that do
not fit at scale 0 are shrunk until they do (`squeezeReaches`), so a label wider than the page
does not collapse the scale.

`clipLine` cuts the line or ray through two points to a box (Liang and Barsky's parametric
clipping), which is how lines and rays are drawn to the edge of the frame.

## Main definitions

* `Frame`, `Frame.toScreen`, `Frame.toWorld`, `Frame.view`.
* `Reach`, `Frame.fit`.
* `clipLine`.
-/

namespace PILean.Plane

/-- A map from world coordinates (`y` up) to a page of `width × height` pixels (`y` down):
`toScreen p = (ox + scale · x, oy - scale · y)`. -/
structure Frame where
  /-- Pixels per world unit, the same along both axes. -/
  scale : Float := 1
  /-- The page abscissa of the world origin. -/
  ox : Float := 0
  /-- The page ordinate of the world origin. -/
  oy : Float := 0
  /-- The width of the page in pixels. -/
  width : Float := 0
  /-- The height of the page in pixels. -/
  height : Float := 0
  deriving Inhabited, Repr, BEq

namespace Frame

/-- The page position of a world point. -/
def toScreen (f : Frame) (p : Point) : Point := ⟨f.ox + f.scale * p.x, f.oy - f.scale * p.y⟩

/-- The world point at a page position (the inverse of `toScreen` for a positive scale). -/
def toWorld (f : Frame) (q : Point) : Point := ⟨(q.x - f.ox) / f.scale, (f.oy - q.y) / f.scale⟩

/-- The world box the page shows: `x0 ≤ x ≤ x1`, `y0 ≤ y ≤ y1` (here `y0` is the lowest
ordinate). -/
def view (f : Frame) : Box :=
  let a := f.toWorld ⟨0, f.height⟩
  let b := f.toWorld ⟨f.width, 0⟩
  ⟨a.x, a.y, b.x, b.y⟩

end Frame

/-- A world point and how far, in pixels, what is drawn at it extends around its page position:
`off` is the box of offsets (`x0 ≤ 0 ≤ x1` for a symmetric extent; `y` down). -/
structure Reach where
  /-- The world point. -/
  at_ : Point
  /-- The offsets in pixels around its page position. -/
  off : Box := ⟨0, 0, 0, 0⟩
  deriving Inhabited, Repr

/-- A world point with a symmetric extent of `e` pixels. -/
def Reach.around (p : Point) (e : Float) : Reach := ⟨p, ⟨-e, -e, e, e⟩⟩

/-- Whether a reach has finite coordinates and offsets. -/
def Reach.finite (r : Reach) : Bool :=
  r.at_.x.isFinite && r.at_.y.isFinite && r.off.x0.isFinite && r.off.y0.isFinite &&
    r.off.x1.isFinite && r.off.y1.isFinite

/-- The interval of page positions of the origin along one axis at which every reach fits
between `pad` and `size - pad`, at scale `s`: `(lo, hi)`, empty when `lo > hi`. `coord` gives a
reach's world coordinate along the axis, `sign` is `1` across and `-1` down (the page's `y`
grows downwards), `lowOff` and `highOff` its offsets. -/
def originRange (rs : Array Reach) (s size pad sign : Float)
    (coord lowOff highOff : Reach → Float) :
    Float × Float :=
  rs.foldl (init := (-1e300, 1e300)) fun (lo, hi) r =>
    let c := sign * s * coord r
    (max lo (pad - c - lowOff r), min hi (size - pad - c - highOff r))

/-- The largest scale in `(0, sMax]` at which `ok` holds, by bisection (60 halvings), for an `ok`
that holds for every scale below one where it holds; `0` if it holds for none tried. -/
def largestScale (ok : Float → Bool) (sMax : Float) : Float := Id.run do
  if ok sMax then return sMax
  let mut lo := 0
  let mut hi := sMax
  for _ in [0:60] do
    let mid := (lo + hi) / 2
    if ok mid then lo := mid else hi := mid
  return lo

/-- The reaches with their extents along each axis shrunk, about each reach's point, by the one
factor that makes the widest span of extents (the largest right extent less the smallest left
one, and the same down) fit the room the page leaves (`width - 2 pad`, and `height - 2 pad` when
the height is given); the reaches themselves when their extents fit. -/
def squeezeReaches (rs : Array Reach) (width : Float) (height : Option Float) (pad : Float) :
    Array Reach :=
  let factor := fun (room lo hi : Float) =>
    if hi - lo > room && room > 0 then room / (hi - lo) else 1
  let fx := factor (width - 2 * pad) (rs.foldl (fun m r => min m r.off.x0) 0)
    (rs.foldl (fun m r => max m r.off.x1) 0)
  let fy := match height with
    | some h => factor (h - 2 * pad) (rs.foldl (fun m r => min m r.off.y0) 0)
        (rs.foldl (fun m r => max m r.off.y1) 0)
    | none => 1
  if fx == 1 && fy == 1 then rs
  else rs.map fun r =>
    { r with off := ⟨fx * r.off.x0, fy * r.off.y0, fx * r.off.x1, fy * r.off.y1⟩ }

/-- The frame at which the reaches fit a page `width` pixels wide (and `height` high, if given)
inside `pad` pixels on every side, at the largest scale (see the module docstring); `fallback`
is the world box used when there are no finite reaches. When the extents alone do not fit the
page (a label wider than the page), they are shrunk first (`squeezeReaches`), so that the world
points still fill the page; what reaches beyond it is then reported by the layout checks. -/
def Frame.fit (reaches : Array Reach) (width : Float) (height : Option Float) (pad : Float)
    (fallback : Box := ⟨-1, -1, 1, 1⟩) : Frame := Id.run do
  let rs0 := reaches.filter (·.finite)
  let rs := if rs0.isEmpty then
      #[Reach.around ⟨fallback.x0, fallback.y0⟩ 0, Reach.around ⟨fallback.x1, fallback.y1⟩ 0]
    else squeezeReaches rs0 width height pad
  let xs := rs.map (·.at_.x)
  let ys := rs.map (·.at_.y)
  let span := fun (vs : Array Float) =>
    (vs.foldl max (-1e300)) - (vs.foldl min 1e300)
  let maxOff := rs.foldl (fun m r =>
    max m (max (max r.off.x0.abs r.off.x1.abs) (max r.off.y0.abs r.off.y1.abs))) 0
  let fitsAcross := fun (s : Float) =>
    let (lo, hi) := originRange rs s width pad 1 (·.at_.x) (·.off.x0) (·.off.x1)
    lo ≤ hi
  let fitsDown := fun (h : Float) (s : Float) =>
    let (lo, hi) := originRange rs s h pad (-1) (·.at_.y) (·.off.y0) (·.off.y1)
    lo ≤ hi
  let bound := fun (room range : Float) =>
    if range > 0 then (room + 2 * maxOff) / range else 1e9
  let sx := largestScale fitsAcross (bound width (span xs))
  let s := match height with
    | some h => min sx (largestScale (fitsDown h) (bound h (span ys)))
    | none =>
      if span xs > 0 then sx
      else if span ys > 0 then (width - 2 * pad) / span ys
      else 1
  let s := if s > 0 && s < 1e8 then s else 1
  let (lx, hx) := originRange rs s width pad 1 (·.at_.x) (·.off.x0) (·.off.x1)
  let ox := if lx ≤ hx then (lx + hx) / 2 else lx
  match height with
  | some h =>
    let (ly, hy) := originRange rs s h pad (-1) (·.at_.y) (·.off.y0) (·.off.y1)
    let oy := if ly ≤ hy then (ly + hy) / 2 else ly
    return { scale := s, ox, oy, width, height := h }
  | none =>
    -- the origin as high as the reaches allow, then the page as tall as they need
    let top := rs.foldl (fun m r => max m (pad + s * r.at_.y - r.off.y0)) (-1e300)
    let bottom := rs.foldl (fun m r => max m (top - s * r.at_.y + r.off.y1)) (-1e300)
    let need := bottom + pad
    let h := need.ceil
    return { scale := s, ox, oy := top + (h - need) / 2, width, height := h }

/-- The part of the line through `a` and `b` (a ray from `a` when `ray`) inside the box, or
`none` when it misses it or `a = b` (Liang and Barsky). -/
def clipLine (a b : Point) (box : Box) (ray : Bool := false) : Option (Point × Point) := Id.run do
  let d := b - a
  if d.x == 0 && d.y == 0 then return none
  let mut t0 : Float := if ray then 0 else -1e300
  let mut t1 : Float := 1e300
  -- each side: `p t ≤ q`
  for (p, q) in [(-d.x, a.x - box.x0), (d.x, box.x1 - a.x), (-d.y, a.y - box.y0),
      (d.y, box.y1 - a.y)] do
    if p == 0 then
      if q < 0 then return none
    else
      let t := q / p
      if p < 0 then t0 := max t0 t else t1 := min t1 t
  if t0 > t1 || t0.isNaN || t1.isNaN then return none
  return some (a + t0 * d, a + t1 * d)

end PILean.Plane
