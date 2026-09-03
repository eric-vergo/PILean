import PILean.Draw.Basic

/-!
# Paths, arcs, and circular arrows

Multi-segment and circular drawing primitives built on `PILean.Draw.line`
and `Image.putPixel`: `polyline`, `dashedLine`, `arc`, and `circularArrow`.

Like every other primitive in `PILean.Draw`, these are **total** and **clip
silently**, and their cost is proportional to the requested geometry (the
number of segment steps, resp. the circle's circumference) rather than to
the image — off-canvas pixels are dropped by `putPixel`, not by an up-front
intersection.

## No floating point

Every function here is **pure integer arithmetic**. Angles are `Int`
degrees and trigonometry goes through a 91-entry `sinTable` of 16.16
fixed-point sines (`sinFP`/`cosFP`), so the rasterized pixel set of any
call is bit-identical on every machine, every Lean toolchain, and every
optimization level — which is what makes the drawing goldens meaningful.
The price is a fixed angular resolution: sector membership and endpoint
positions are decided by *exact* integer comparisons on *rounded* direction
vectors, so a pixel whose true direction lies within about `0.001°` of a
sector boundary may fall on either side of it. That choice is
deterministic, just not infinitely precise.

## Angle convention

Angles are `Int` degrees in Pillow's convention: `0°` points along `+x`
(3 o'clock) and increasing angles turn **clockwise on screen**, because `y`
grows downward. The point at angle `θ` on the circle of radius `r` about
`c` is `(c.x + r·cos θ, c.y + r·sin θ)` (see `circlePoint`). Angles outside
`[0, 360)` are reduced modulo `360`, so `-225°` and `135°` are the same
direction — this is what makes a positive and a negative sweep describe the
*same* arc pixels with the arrowhead at opposite ends.
-/

namespace PILean.Draw

open PILean

/-! ## Fixed-point trigonometry -/

/-- `round(sin(d°) · 65536)` for `d = 0, 1, …, 90` — sine as an unsigned
16.16 fixed-point fraction, so `sinTable[0]! = 0` and `sinTable[90]! = 65536`.

Computed once, offline, by
`[math.floor(math.sin(d * math.pi / 180) * 65536 + 0.5) for d in range(91)]`
(CPython 3.9.6) and pasted here as literals: the library itself never
evaluates a transcendental function and contains no `Float`. Ninety-one
entries is far below the ~1000-element array-literal limit in `CLAUDE.md`,
so this is a literal rather than a decoded hex blob. -/
def sinTable : Array Nat :=
  #[    0,  1144,  2287,  3430,  4572,  5712,  6850,  7987,  9121, 10252,
    11380, 12505, 13626, 14742, 15855, 16962, 18064, 19161, 20252, 21336,
    22415, 23486, 24550, 25607, 26656, 27697, 28729, 29753, 30767, 31772,
    32768, 33754, 34729, 35693, 36647, 37590, 38521, 39441, 40348, 41243,
    42126, 42995, 43852, 44695, 45525, 46341, 47143, 47930, 48703, 49461,
    50203, 50931, 51643, 52339, 53020, 53684, 54332, 54963, 55578, 56175,
    56756, 57319, 57865, 58393, 58903, 59396, 59870, 60326, 60764, 61183,
    61584, 61966, 62328, 62672, 62997, 63303, 63589, 63856, 64104, 64332,
    64540, 64729, 64898, 65048, 65177, 65287, 65376, 65446, 65496, 65526,
    65536]

/-- Round a 16.16 fixed-point value to the nearest whole number, **half away
from zero**: `(v + 32768) >>> 16` for `v ≥ 0` and the negation of the same
computation on `-v` for `v < 0`. Symmetric by construction, so
`fpRound (-v) = -fpRound v` for every `v`; in particular a shape's pixels do
not drift when it is mirrored through the origin. -/
def fpRound (v : Int) : Int :=
  if 0 ≤ v then
    (((v.toNat + 32768) >>> 16 : Nat) : Int)
  else
    -((((-v).toNat + 32768) >>> 16 : Nat) : Int)

/-- `sin` of an `Int` degree angle as a signed 16.16 fixed-point value in
`[-65536, 65536]`. The angle is reduced modulo `360` (so negative and
out-of-range degrees are fine), then `sinTable` is extended to the other
three quadrants by the exact symmetries `sin(180° − d) = sin d` and
`sin(d + 180°) = −sin d`. Exact at the four axis directions:
`sinFP 0 = 0`, `sinFP 90 = 65536`, `sinFP 180 = 0`, `sinFP 270 = -65536`. -/
def sinFP (deg : Int) : Int :=
  let d := (((deg % 360) + 360) % 360).toNat
  if d ≤ 90 then (sinTable[d]! : Int)
  else if d ≤ 180 then (sinTable[180 - d]! : Int)
  else if d ≤ 270 then -(sinTable[d - 180]! : Int)
  else -(sinTable[360 - d]! : Int)

/-- `cos` of an `Int` degree angle as a signed 16.16 fixed-point value,
defined by the shift `cos d = sin (d + 90°)` so that it shares `sinFP`'s
table, symmetries, and exactness at the axes. -/
def cosFP (deg : Int) : Int := sinFP (deg + 90)

/-- The pixel at angle `deg` on the circle of radius `radius` about
`center`: `(center.x + radius·cos deg, center.y + radius·sin deg)`, with
each coordinate computed in 16.16 fixed point and rounded by `fpRound`
(half away from zero). With `0°` at 3 o'clock and `y` growing downward,
increasing `deg` walks clockwise on screen. -/
def circlePoint (center : Point) (radius : Nat) (deg : Int) : Point :=
  ⟨center.x + fpRound ((radius : Int) * cosFP deg),
   center.y + fpRound ((radius : Int) * sinFP deg)⟩

/-! ## Shared pixel stamp -/

/-- Plot one point with `Draw.line`'s thickness rule: `width ≤ 1` sets the
single pixel, and `width > 1` stamps a filled `width × width` square
centered on it, offset toward the top-left by `width / 2` (so an even
`width` extends `⌈width/2⌉` past the point on one side and `⌊width/2⌋` on
the other). Clipped, like everything else. -/
private def stampPoint (img : Image) (p : Point) (color : Color) (width : Nat) : Image :=
  Id.run do
    if width ≤ 1 then
      return img.putPixel p.x p.y color
    let mut im := img
    let half : Int := (width : Int) / 2
    for j in [0:width] do
      for i in [0:width] do
        im := im.putPixel (p.x - half + (i : Int)) (p.y - half + (j : Int)) color
    return im

/-! ## Polylines -/

/-- Draw the segments between consecutive points of `pts` with `Draw.line`
(same Bresenham walk, same `width` rule, same silent clipping). Fewer than
two points draw nothing and return `img` unchanged; `closed := true` adds
the segment from the last point back to the first. Segments are drawn in
order, so a later segment overwrites an earlier one where they cross — with
a single `color` that is invisible. -/
def polyline (img : Image) (pts : Array Point) (color : Color) (width : Nat := 1)
    (closed : Bool := false) : Image := Id.run do
  if pts.size < 2 then
    return img
  let mut im := img
  for i in [0:pts.size - 1] do
    im := line im pts[i]! pts[i + 1]! color width
  if closed then
    im := line im pts[pts.size - 1]! pts[0]! color width
  return im

/-! ## Dashed lines -/

/-- `p / q` rounded to the nearest integer, **half away from zero**, for
`q > 0` (and `0` for `q = 0`, which callers never hit). Computed as
`(2|p| + q) / (2q)` on `Nat` and re-signed, so it never relies on the
rounding direction of `Int` division. -/
private def divRoundHalfAway (p : Int) (q : Nat) : Int :=
  if q == 0 then 0
  else if 0 ≤ p then (((2 * p.toNat + q) / (2 * q) : Nat) : Int)
  else -((((2 * (-p).toNat + q) / (2 * q) : Nat) : Int))

/-- Draw the segment `a → b` as a dashed line.

The segment is walked by an integer DDA along its **major axis**: with
`dx = b.x - a.x`, `dy = b.y - a.y` and `N = max |dx| |dy|`, step `i` (for
`i = 0, 1, …, N`, so both endpoints are steps) is the pixel
`(a.x + round(i·dx / N), a.y + round(i·dy / N))`, each coordinate rounded
half away from zero by `divRoundHalfAway`. For `N = 0` (a zero-length
segment) there is exactly one step, at `a`.

Step `i` is inked according to the period `dash + gap`, in this order:

* `dash + gap = 0` — the period is degenerate, so **every** step is drawn
  (a solid line); this includes `dash = gap = 0`.
* otherwise `dash = 0` — **nothing** is drawn (a period of pure gap).
* otherwise step `i` is drawn iff `i % (dash + gap) < dash`.

So the dash pattern is counted in DDA *steps*, not in Euclidean length: a
diagonal dash of `dash = 3` covers three steps, which is `3√2` pixels long.
`width` follows `Draw.line`'s rule (`width × width` square stamped on each
inked step, `width / 2` toward the top-left). -/
def dashedLine (img : Image) (a b : Point) (color : Color) (dash gap : Nat)
    (width : Nat := 1) : Image := Id.run do
  let dx := b.x - a.x
  let dy := b.y - a.y
  let n := max dx.natAbs dy.natAbs
  let period := dash + gap
  if period != 0 && dash == 0 then
    return img
  let mut im := img
  for i in [0:n + 1] do
    if period == 0 || i % period < dash then
      let p : Point :=
        if n == 0 then a
        else ⟨a.x + divRoundHalfAway ((i : Int) * dx) n,
              a.y + divRoundHalfAway ((i : Int) * dy) n⟩
      im := stampPoint im p color width
  return im

/-! ## Arcs -/

/-- Does the direction `(dx, dy)` lie in the closed sector swept clockwise
from the ray `u = (ux, uy)` to the ray `v = (vx, vy)`?

`full` short-circuits a whole circle. Otherwise the test is two signed
integer cross products, `cross u p = ux·dy − uy·dx` and
`cross p v = dx·vy − dy·vx`, each of which is `≥ 0` exactly when `p` lies in
the closed half-plane on the clockwise side of that ray:

* narrow sector (`wide = false`, span `≤ 180°`) — the sector is the
  *intersection* of the two half-planes, so **both** cross products must be
  `≥ 0`;
* wide sector (`wide = true`, span `> 180°`) — the sector is the complement
  of the open gap from `v` to `u`, and that gap is the intersection of the
  two strictly-negative half-planes, so **either** cross product being `≥ 0`
  puts `p` in the sector.

Both forms are closed, so the two boundary rays themselves are always
drawn. Scale-invariant in sign, so the 16.16 fixed-point rays and the
small integer pixel offset can be compared directly. -/
private def inSector (full wide : Bool) (ux uy vx vy dx dy : Int) : Bool :=
  if full then true
  else
    let cu := ux * dy - uy * dx
    let cv := dx * vy - dy * vx
    if wide then 0 ≤ cu || 0 ≤ cv else 0 ≤ cu && 0 ≤ cv

/-- Draw the arc of the circle of radius `radius` about `center` that starts
at `startDeg` and sweeps `sweepDeg` degrees — **clockwise on screen** when
`sweepDeg > 0`, counterclockwise when `sweepDeg < 0`.

`radius = 0` or `sweepDeg = 0` draw nothing; `|sweepDeg| ≥ 360` draws the
whole circle. A positive and a negative sweep that describe the same sector
(for instance `startDeg = 135, sweepDeg = 270` and
`startDeg = 45, sweepDeg = -270`) produce **exactly** the same pixels: only
`min startDeg (startDeg + sweepDeg)` and `max startDeg (startDeg + sweepDeg)`
enter the rasterizer.

Rasterization is the integer midpoint circle algorithm (decision variable
`d = 3 − 2r`, one octant walked and reflected into all eight; boundary
pixels are emitted more than once, which is harmless for a single color),
filtered by `inSector`. `width` follows `Draw.line`'s rule: `width > 1`
stamps a filled `width × width` square on each arc pixel, offset toward the
top-left by `width / 2`. The walk costs `O(radius)` regardless of how much
of the circle lands on the canvas. -/
def arc (img : Image) (center : Point) (radius : Nat) (startDeg sweepDeg : Int)
    (color : Color) (width : Nat := 1) : Image := Id.run do
  if radius == 0 || sweepDeg == 0 then
    return img
  let lo := min startDeg (startDeg + sweepDeg)
  let hi := max startDeg (startDeg + sweepDeg)
  let full := 360 ≤ hi - lo
  let wide := 180 < hi - lo
  let ux := cosFP lo
  let uy := sinFP lo
  let vx := cosFP hi
  let vy := sinFP hi
  let mut im := img
  let mut x : Int := 0
  let mut y : Int := (radius : Int)
  let mut d : Int := 3 - 2 * (radius : Int)
  -- `x` rises from `0` and `y` falls from `radius`, so the walk ends in at
  -- most `radius + 2` steps; the bound makes termination syntactic.
  for _ in [0:radius + 2] do
    if y < x then
      break
    for k in [0:8] do
      let (ox, oy) : Int × Int :=
        match k with
        | 0 => (x, y)
        | 1 => (y, x)
        | 2 => (y, -x)
        | 3 => (x, -y)
        | 4 => (-x, -y)
        | 5 => (-y, -x)
        | 6 => (-y, x)
        | _ => (-x, y)
      if inSector full wide ux uy vx vy ox oy then
        im := stampPoint im ⟨center.x + ox, center.y + oy⟩ color width
    x := x + 1
    if 0 < d then
      y := y - 1
      d := d + 4 * (x - y) + 10
    else
      d := d + 4 * x + 6
  return im

/-- Draw `arc img center radius startDeg sweepDeg color width` and put an
arrowhead on the **end** of the arc, at angle `startDeg + sweepDeg`.

The head is two `Draw.line` segments of length `headLength` running from
the tip *backwards*: the direction of travel at the end point is
`startDeg + sweepDeg ± 90°` (`+` for a clockwise sweep, `−` for a
counterclockwise one), and the two segments leave the tip along that
direction reversed and then rotated by `±headHalfAngleDeg`. Both endpoints
are placed by `circlePoint`, i.e. in 16.16 fixed point rounded half away
from zero.

Because `arc` depends only on the *sector*, `(startDeg := 135, sweepDeg := 270)`
and `(startDeg := 45, sweepDeg := -270)` draw the identical arc and differ
only in which end carries the head — a fixed turn icon whose direction is
read off the arrowhead alone.

`headLength = 0` draws the plain arc. `radius = 0` or `sweepDeg = 0` draw
nothing at all: with no sweep there is no direction of travel, so there is
no arrowhead either. -/
def circularArrow (img : Image) (center : Point) (radius : Nat)
    (startDeg sweepDeg : Int) (color : Color) (width : Nat := 1)
    (headLength : Nat := 8) (headHalfAngleDeg : Nat := 30) : Image := Id.run do
  if radius == 0 || sweepDeg == 0 then
    return img
  let mut im := arc img center radius startDeg sweepDeg color width
  if headLength != 0 then
    let endDeg := startDeg + sweepDeg
    let travelDeg := if 0 < sweepDeg then endDeg + 90 else endDeg - 90
    let backDeg := travelDeg + 180
    let tip := circlePoint center radius endDeg
    let halfAngle : Int := (headHalfAngleDeg : Int)
    im := line im tip (circlePoint tip headLength (backDeg + halfAngle)) color width
    im := line im tip (circlePoint tip headLength (backDeg - halfAngle)) color width
  return im

end PILean.Draw
