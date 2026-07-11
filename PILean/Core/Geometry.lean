/-!
# Geometry

Points and rectangles. Coordinates are `Int` throughout the public API so
that positions outside an image are representable (drawing clips rather than
fails). `Rect` is **half-open**: it contains pixels with
`left ≤ x < right` and `top ≤ y < bottom`. This one convention is used
everywhere in PILean (crop, paste, drawing); PIL's endpoint-inclusive
`draw.rectangle` quirk is deliberately not reproduced.
-/

namespace PILean

/-- A pixel position. The origin is the top-left corner; `x` grows rightward
and `y` grows downward. -/
structure Point where
  x : Int
  y : Int
  deriving Repr, DecidableEq, Inhabited

/-- An axis-aligned rectangle, half-open on both axes: it contains pixels
with `left ≤ x < right` and `top ≤ y < bottom`. Empty when `right ≤ left`
or `bottom ≤ top`. -/
structure Rect where
  left : Int
  top : Int
  right : Int
  bottom : Int
  deriving Repr, DecidableEq, Inhabited

namespace Rect

/-- The rectangle with top-left corner `origin` and the given size. -/
def ofSize (origin : Point) (width height : Nat) : Rect :=
  ⟨origin.x, origin.y, origin.x + width, origin.y + height⟩

/-- Width in pixels (0 if empty). -/
def width (r : Rect) : Nat := (r.right - r.left).toNat

/-- Height in pixels (0 if empty). -/
def height (r : Rect) : Nat := (r.bottom - r.top).toNat

/-- Does the rectangle contain no pixels? -/
def isEmpty (r : Rect) : Bool := r.right ≤ r.left || r.bottom ≤ r.top

/-- Intersection of two rectangles (possibly empty). -/
def intersect (r s : Rect) : Rect :=
  ⟨max r.left s.left, max r.top s.top, min r.right s.right, min r.bottom s.bottom⟩

/-- Does the rectangle contain the point? (Half-open on both axes.) -/
def contains (r : Rect) (p : Point) : Bool :=
  r.left ≤ p.x && p.x < r.right && r.top ≤ p.y && p.y < r.bottom

end Rect

end PILean
