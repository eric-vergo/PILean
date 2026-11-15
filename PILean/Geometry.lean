/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# Plane geometry

Points, affine transforms and axis-aligned boxes in `Float` coordinates. The coordinate system is
the one of SVG and of raster images: `x` grows to the right, `y` downwards, one unit a pixel
(or a user unit) at the identity transform.

## Main definitions

* `Point`, with `+`, `-` and scaling.
* `Affine`: the transform `x' = a x + c y + e`, `y' = b x + d y + f` (SVG's `matrix(a b c d e f)`);
  `Affine.comp`, `Affine.apply`, `Affine.inverse?`, `Affine.translate`, `Affine.scale`,
  `Affine.rotate`.
* `Box`: an axis-aligned box; `Box.union`, `Box.add`, `Box.width`, `Box.height`, `Box.inset`,
  `Box.contains`.
-/

namespace PILean

/-- A point (or vector) of the plane. -/
structure Point where
  /-- The abscissa. -/
  x : Float
  /-- The ordinate (downwards). -/
  y : Float
  deriving BEq, Inhabited, Repr

namespace Point

instance : Add Point := ⟨fun p q => ⟨p.x + q.x, p.y + q.y⟩⟩
instance : Sub Point := ⟨fun p q => ⟨p.x - q.x, p.y - q.y⟩⟩
instance : HMul Float Point Point := ⟨fun k p => ⟨k * p.x, k * p.y⟩⟩

/-- The midpoint of two points. -/
def mid (p q : Point) : Point := ⟨(p.x + q.x) / 2, (p.y + q.y) / 2⟩

/-- The point `t` of the way from `p` to `q`. -/
def lerp (p q : Point) (t : Float) : Point := ⟨p.x + t * (q.x - p.x), p.y + t * (q.y - p.y)⟩

/-- The Euclidean length of the vector. -/
def norm (p : Point) : Float := (p.x * p.x + p.y * p.y).sqrt

/-- The distance between two points. -/
def dist (p q : Point) : Float := (p - q).norm

end Point

/-- An affine transform: `x' = a x + c y + e`, `y' = b x + d y + f`, as SVG's
`matrix(a b c d e f)`. -/
structure Affine where
  /-- Scale of `x` into `x'`. -/
  a : Float := 1
  /-- Shear of `x` into `y'`. -/
  b : Float := 0
  /-- Shear of `y` into `x'`. -/
  c : Float := 0
  /-- Scale of `y` into `y'`. -/
  d : Float := 1
  /-- Translation of `x'`. -/
  e : Float := 0
  /-- Translation of `y'`. -/
  f : Float := 0
  deriving BEq, Inhabited, Repr

namespace Affine

/-- The identity. -/
def id : Affine := {}

/-- The image of a point. -/
def apply (m : Affine) (p : Point) : Point :=
  ⟨m.a * p.x + m.c * p.y + m.e, m.b * p.x + m.d * p.y + m.f⟩

/-- The image of a vector (the translation left out). -/
def applyVector (m : Affine) (v : Point) : Point := ⟨m.a * v.x + m.c * v.y, m.b * v.x + m.d * v.y⟩

/-- `m.comp n` applies `n`, then `m`. -/
def comp (m n : Affine) : Affine where
  a := m.a * n.a + m.c * n.b
  b := m.b * n.a + m.d * n.b
  c := m.a * n.c + m.c * n.d
  d := m.b * n.c + m.d * n.d
  e := m.a * n.e + m.c * n.f + m.e
  f := m.b * n.e + m.d * n.f + m.f

/-- The translation by `(dx, dy)`. -/
def translate (dx dy : Float) : Affine := { e := dx, f := dy }

/-- The scaling by `sx` and `sy` about the origin. -/
def scale (sx sy : Float) : Affine := { a := sx, d := sy }

/-- The rotation by `θ` radians about the origin (clockwise on screen, as SVG's `rotate`, since
`y` points down). -/
def rotate (θ : Float) : Affine :=
  { a := θ.cos, b := θ.sin, c := -θ.sin, d := θ.cos }

/-- The determinant of the linear part. -/
def det (m : Affine) : Float := m.a * m.d - m.b * m.c

/-- The inverse, or `none` when the transform is singular (or not finite). -/
def inverse? (m : Affine) : Option Affine :=
  let k := m.det
  if k == 0 || k.isNaN || k.isInf then none
  else some {
    a := m.d / k, b := -m.b / k, c := -m.c / k, d := m.a / k,
    e := (m.c * m.f - m.d * m.e) / k, f := (m.b * m.e - m.a * m.f) / k }

/-- The largest factor by which the transform stretches a length (the larger singular value of
the linear part): flattening tolerances in device units divide by it. -/
def maxScale (m : Affine) : Float :=
  let s := (m.a * m.a + m.b * m.b + m.c * m.c + m.d * m.d) / 2
  let t := (((m.a * m.a + m.b * m.b - m.c * m.c - m.d * m.d) / 2) ^ 2 +
    (m.a * m.c + m.b * m.d) ^ 2).sqrt
  (s + t).sqrt

end Affine

/-- An axis-aligned box `[x0, x1] × [y0, y1]`. -/
structure Box where
  /-- The left edge. -/
  x0 : Float
  /-- The top edge. -/
  y0 : Float
  /-- The right edge. -/
  x1 : Float
  /-- The bottom edge. -/
  y1 : Float
  deriving BEq, Inhabited, Repr

namespace Box

/-- The box of one point. -/
def ofPoint (p : Point) : Box := ⟨p.x, p.y, p.x, p.y⟩

/-- The box with its top-left corner at `(x, y)` and the given size. -/
def ofSize (x y w h : Float) : Box := ⟨x, y, x + w, y + h⟩

/-- The width. -/
def width (b : Box) : Float := b.x1 - b.x0

/-- The height. -/
def height (b : Box) : Float := b.y1 - b.y0

/-- The smallest box containing both. -/
def union (a b : Box) : Box := ⟨min a.x0 b.x0, min a.y0 b.y0, max a.x1 b.x1, max a.y1 b.y1⟩

/-- The smallest box containing the box and the point. -/
def add (b : Box) (p : Point) : Box := b.union (ofPoint p)

/-- The box shrunk by `l`, `t`, `r`, `bo` on its four sides. -/
def inset (b : Box) (l t r bo : Float) : Box := ⟨b.x0 + l, b.y0 + t, b.x1 - r, b.y1 - bo⟩

/-- Whether the point lies in the box, edges included. -/
def contains (b : Box) (p : Point) : Bool :=
  b.x0 ≤ p.x && p.x ≤ b.x1 && b.y0 ≤ p.y && p.y ≤ b.y1

/-- The smallest box containing every point, `none` for none. -/
def ofPoints (ps : Array Point) : Option Box :=
  ps.foldl (init := none) fun acc p => some (match acc with | none => ofPoint p | some b => b.add p)

end Box

end PILean
