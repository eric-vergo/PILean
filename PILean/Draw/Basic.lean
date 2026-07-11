import PILean.Core.Image

/-!
# Drawing primitives

Plain functions `Image → Image` — no draw-context object. Chaining
(`img |> Draw.line .. |> Draw.rect ..`) passes the image linearly through
each call, so every primitive hits the in-place `set!` fast path.

All primitives are **total** and **clip silently** (they build on
`Image.putPixel`'s out-of-bounds no-op). Filled shapes (`rect`, `ellipse`,
`polygon`) first intersect their geometry with the image bounds and only
ever loop over that clipped range, so drawing far off-canvas (even at
coordinates like `±10000`) costs work proportional to the image, not to the
requested geometry.

WP5 implements: an all-octant integer Bresenham line (with width via
stamped squares), row-span rectangle fill/outline, an ellipse via an exact
integer point-membership test (algebraically equivalent to solving each
scanline of the midpoint walk, but avoids the octant bookkeeping), scanline
polygon fill via an even-odd point-in-polygon test, and an iterative
(non-recursive) flood fill.
-/

namespace PILean.Draw

open PILean

/-- Set a single pixel (clipped). -/
def point (img : Image) (p : Point) (color : Color) : Image :=
  img.putPixel p.x p.y color

/-- All-octant integer Bresenham points from `(x0,y0)` to `(x1,y1)`,
inclusive of both endpoints. Handles horizontal, vertical, diagonal, and
zero-length (`x0 = x1 ∧ y0 = y1`, a single point) segments uniformly. The
iteration count is bounded above by `dx + |dy| + 1` so the loop always
terminates even if (by a bug) the walk never reaches the endpoint. -/
private def bresenhamPoints (x0 y0 x1 y1 : Int) : Array Point := Id.run do
  let dx : Int := (x1 - x0).natAbs
  let dy : Int := -(y1 - y0).natAbs
  let sx : Int := if x0 < x1 then 1 else -1
  let sy : Int := if y0 < y1 then 1 else -1
  let mut err : Int := dx + dy
  let mut x := x0
  let mut y := y0
  let mut pts : Array Point := #[]
  let bound := (dx - dy).toNat + 1
  for _ in [0:bound + 1] do
    pts := pts.push ⟨x, y⟩
    if x == x1 && y == y1 then
      break
    let e2 := 2 * err
    if e2 ≥ dy then
      err := err + dy
      x := x + sx
    if e2 ≤ dx then
      err := err + dx
      y := y + sy
  return pts

/-- Draw a line segment from `a` to `b` (clipped), via an all-octant integer
Bresenham walk. `width = 1` (the default) plots single pixels. For
`width > 1` a filled `width × width` square is stamped centered on each
plotted point (offset toward the top-left by `width / 2` when `width` is
even, so the square is `⌈width/2⌉` past center on one side and `⌊width/2⌋`
on the other). This gives thick lines flat, square-cornered joints and
caps — **not** PIL's round caps/joints; it is capability parity (you can
draw a thick line), not pixel-for-pixel quirk parity. -/
def line (img : Image) (a b : Point) (color : Color) (width : Nat := 1) : Image := Id.run do
  let pts := bresenhamPoints a.x a.y b.x b.y
  let mut im := img
  if width ≤ 1 then
    for p in pts do
      im := im.putPixel p.x p.y color
  else
    let half : Int := (width : Int) / 2
    for p in pts do
      for j in [0:width] do
        for i in [0:width] do
          im := im.putPixel (p.x - half + (i : Int)) (p.y - half + (j : Int)) color
  return im

/-- Draw a rectangle: filled with `fill` if given (row spans over `r`
intersected with the image bounds), then outlined with `outline` if given
(the pixels of the clipped region within `width` of any of `r`'s four
edges — a `width`-deep inset border drawn from the outer ring inward; if
`width` covers the whole rectangle the "outline" is just the filled
rectangle). `r` is half-open as always. -/
def rect (img : Image) (r : Rect) (fill : Option Color := none)
    (outline : Option Color := none) (width : Nat := 1) : Image := Id.run do
  let imgBounds : Rect := ⟨0, 0, (img.width : Int), (img.height : Int)⟩
  let clipped := r.intersect imgBounds
  let mut im := img
  if !clipped.isEmpty then
    let x0 := clipped.left.toNat
    let x1 := clipped.right.toNat
    let y0 := clipped.top.toNat
    let y1 := clipped.bottom.toNat
    if let some c := fill then
      for y in [y0:y1] do
        for x in [x0:x1] do
          im := im.putPixel (x : Int) (y : Int) c
    if let some c := outline then
      if width > 0 then
        let w : Int := (width : Int)
        for y in [y0:y1] do
          for x in [x0:x1] do
            let xi : Int := x
            let yi : Int := y
            if xi - r.left < w || r.right - 1 - xi < w || yi - r.top < w || r.bottom - 1 - yi < w then
              im := im.putPixel xi yi c
  return im

/-- Does the ellipse inscribed in `bounds` contain the point `(x, y)`
(pixel treated as occupying the unit cell whose top-left corner is
`(x, y)`, matching `Rect`'s half-open convention)? Pure integer test: with
`w = bounds.right - bounds.left`, `h = bounds.bottom - bounds.top`, and
doubled center-relative offsets `dx2 = 2x + 1 - (left + right)`,
`dy2 = 2y + 1 - (top + bottom)` (double the pixel-center offset from the
box center), the continuous ellipse equation
`(dx2/w)² + (dy2/h)² ≤ 1` is cleared of fractions as
`dx2²h² + dy2²w² ≤ w²h²`. Symmetric under reflection about the box center
by construction, and `false` for degenerate (empty) `bounds`. -/
private def ellipseContains (bounds : Rect) (x y : Int) : Bool :=
  let w : Int := bounds.right - bounds.left
  let h : Int := bounds.bottom - bounds.top
  if w ≤ 0 || h ≤ 0 then false
  else
    let dx2 := 2 * x + 1 - (bounds.left + bounds.right)
    let dy2 := 2 * y + 1 - (bounds.top + bounds.bottom)
    dx2 * dx2 * h * h + dy2 * dy2 * w * w ≤ w * w * h * h

/-- Draw the ellipse inscribed in `bounds` (filled and/or outlined).
Filling and outlining both loop only over `bounds` intersected with the
image, testing `ellipseContains` per pixel (equivalent to, but simpler and
less bug-prone than, deriving explicit per-row spans from an octant
midpoint walk). The outline is the band between the outer ellipse
(`bounds`) and the ellipse inset by `width` on both axes; if the inset
collapses (`width` at least half of `bounds`'s shorter side) the "outline"
degenerates to the full fill. Degenerate `bounds` (empty, or a single
pixel) draw nothing resp. exactly that one pixel — never loop forever. -/
def ellipse (img : Image) (bounds : Rect) (fill : Option Color := none)
    (outline : Option Color := none) (width : Nat := 1) : Image := Id.run do
  let mut im := img
  if bounds.isEmpty then
    return im
  let imgBounds : Rect := ⟨0, 0, (img.width : Int), (img.height : Int)⟩
  let clipped := bounds.intersect imgBounds
  if clipped.isEmpty then
    return im
  let x0 := clipped.left.toNat
  let x1 := clipped.right.toNat
  let y0 := clipped.top.toNat
  let y1 := clipped.bottom.toNat
  if let some c := fill then
    for y in [y0:y1] do
      for x in [x0:x1] do
        if ellipseContains bounds (x : Int) (y : Int) then
          im := im.putPixel (x : Int) (y : Int) c
  if let some c := outline then
    if width > 0 then
      let w : Int := (width : Int)
      let inner : Rect :=
        ⟨bounds.left + w, bounds.top + w, bounds.right - w, bounds.bottom - w⟩
      for y in [y0:y1] do
        for x in [x0:x1] do
          let xi : Int := x
          let yi : Int := y
          if ellipseContains bounds xi yi && (inner.isEmpty || !ellipseContains inner xi yi) then
            im := im.putPixel xi yi c
  return im

/-- Even-odd point-in-polygon test (Franklin's PNPOLY algorithm) at
integer point `(x, y)`. For each edge, `(a.y > y) != (b.y > y)` is true
exactly when the edge straddles the horizontal line `y`; this both skips
horizontal edges automatically (both sides of the comparison agree) and
gives a consistent half-open treatment of shared vertices (a vertex
exactly on the scanline is "counted" by at most one of its two edges), so
this is the classic scanline even-odd rule computed per pixel rather than
via an explicit sorted edge-crossing list per row. Pure integer arithmetic
(cross-multiplication instead of division), so there is no rounding to get
wrong. -/
private def polygonContains (pts : Array Point) (x y : Int) : Bool := Id.run do
  let n := pts.size
  let mut inside := false
  for i in [0:n] do
    let a := pts[i]!
    let b := pts[(i + 1) % n]!
    if (a.y > y) != (b.y > y) then
      let dy := b.y - a.y
      let dx := b.x - a.x
      let lhs := (x - a.x) * dy
      let rhs := (y - a.y) * dx
      let crosses := if dy > 0 then lhs < rhs else lhs > rhs
      if crosses then
        inside := !inside
  return inside

/-- Axis-aligned bounding box of `pts` (half-open, so it includes the
extremal points). `pts` must be nonempty. -/
private def polygonBBox (pts : Array Point) : Rect := Id.run do
  let mut minX := pts[0]!.x
  let mut maxX := pts[0]!.x
  let mut minY := pts[0]!.y
  let mut maxY := pts[0]!.y
  for p in pts do
    minX := min minX p.x
    maxX := max maxX p.x
    minY := min minY p.y
    maxY := max maxY p.y
  return ⟨minX, minY, maxX + 1, maxY + 1⟩

/-- Draw a polygon through `pts`. For 3 or more points: `outline` draws the
lines between consecutive points plus the closing edge (last point back to
first), and `fill` uses an even-odd scanline fill (`polygonContains`)
restricted to `pts`'s bounding box intersected with the image, so it never
loops over off-canvas pixels. Degenerate inputs "degrade": 0 points draw
nothing, 1 point draws that point, 2 points draw the line between them —
in both degenerate cases using `outline`'s color if given, else `fill`'s
(a zero-area shape has no distinct interior, so the two parameters can't be
told apart; whichever is supplied is used, `outline` taking priority if
both are). -/
def polygon (img : Image) (pts : Array Point) (fill : Option Color := none)
    (outline : Option Color := none) : Image := Id.run do
  let degenerateColor := outline <|> fill
  match pts.size with
  | 0 => return img
  | 1 =>
    match degenerateColor with
    | some c => return point img pts[0]! c
    | none => return img
  | 2 =>
    match degenerateColor with
    | some c => return line img pts[0]! pts[1]! c
    | none => return img
  | n =>
    let mut im := img
    if let some c := fill then
      let imgBounds : Rect := ⟨0, 0, (img.width : Int), (img.height : Int)⟩
      let bbox := (polygonBBox pts).intersect imgBounds
      if !bbox.isEmpty then
        let x0 := bbox.left.toNat
        let x1 := bbox.right.toNat
        let y0 := bbox.top.toNat
        let y1 := bbox.bottom.toNat
        for y in [y0:y1] do
          for x in [x0:x1] do
            if polygonContains pts (x : Int) (y : Int) then
              im := im.putPixel (x : Int) (y : Int) c
    if let some c := outline then
      for i in [0:n] do
        im := line im pts[i]! pts[(i + 1) % n]! c
    return im

/-- Flood-fill the connected region of `seed`'s color with `color`
(4-connectivity). Iterative, using an explicit `Array` as a stack (never
recurses, so it can't blow the call stack). No separate "visited" set is
needed: since a pixel is only ever pushed for exploration when it still
equals the original `target` color, and every pixel that gets painted is
immediately set to `color ≠ target`, each pixel can be painted at most
once — so the stack drains in a bounded number of steps (never loops
forever) even though neighbors are pushed without checking whether they
are already queued. No-op if `seed` is out of bounds (including on a `0×0`
image, where every point is out of bounds) or `seed`'s color already
equals `color`. -/
def floodFill (img : Image) (seed : Point) (color : Color) : Image := Id.run do
  match img.getPixel? seed.x seed.y with
  | none => return img
  | some target =>
    if target == color then
      return img
    else
      let mut im := img
      let mut stack : Array Point := #[seed]
      repeat
        if stack.size == 0 then
          break
        else
          let p := stack.back!
          stack := stack.pop
          if let some c := im.getPixel? p.x p.y then
            if c == target then
              im := im.putPixel p.x p.y color
              stack := stack.push ⟨p.x + 1, p.y⟩
              stack := stack.push ⟨p.x - 1, p.y⟩
              stack := stack.push ⟨p.x, p.y + 1⟩
              stack := stack.push ⟨p.x, p.y - 1⟩
      return im

end PILean.Draw
