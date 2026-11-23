/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Geometry

/-!
# Paths

Vector outlines: subpaths of lines, quadratic and cubic Béziers, optionally closed. A path is a
value; drawing it (filling, stroking) is the business of the back ends (`PILean.Svg` today, the
rasteriser later).

## Main definitions

* `PathCmd`, `Path`: the commands and the path; `Path.moveTo`, `lineTo`, `quadTo`, `cubicTo`,
  `close` build one; `Path.rect`, `Path.roundedRect`, `Path.polyline`, `Path.ellipse` common
  shapes.
* `Path.arc`, `Path.arcTo`: a circular arc between two angles as cubic Béziers, each spanning at
  most a quarter turn, within `arcError` of the circle (at most 0.0273 % of the radius).
* `Path.transform`: the path under an affine transform (Béziers are affine invariant).
* `Path.flatten`: the path as polylines, each curve cut so that no point of the polyline is
  farther than a tolerance from the curve.
* `Path.controlBounds`, `Path.bounds`: the box of all points, control points included, and the
  tight box with the curves' extrema.

## Implementation notes

`flatten` cuts a curve into `n` equal parameter steps, with `n` from the second differences of the
control points: a quadratic with `D = ‖p₀ - 2p₁ + p₂‖` strays at most `D / (4n²)` from its chords,
a cubic with `D` the larger of its two second differences at most `3D / (4n²)`, so the smallest
`n` meeting the tolerance is used (at most `maxPieces`, so a huge or non-finite curve costs a
bounded amount of work).

An arc of sweep `Δ` is cut into `⌈|Δ| / (π/2)⌉` equal pieces, each drawn as the cubic whose
control points lie on the tangents at its ends at the distance `(4/3) tan (δ/4) r` (`δ` the
sweep of the piece). That cubic meets the circle at its ends and its middle and keeps within
`r (2/27) sin⁶(δ/4) / cos²(δ/4)` of the radius in between (Goldapp, *Approximation of circular
arcs by cubic polynomials*, Computer Aided Geometric Design 8, 1991); for a quarter turn this is
`2.73 × 10⁻⁴ r`, the error `Path.ellipse` has for its four quarters.
-/

namespace PILean

/-- A path command, in absolute coordinates. -/
inductive PathCmd where
  /-- Start a subpath at the point. -/
  | move (p : Point)
  /-- A line to the point. -/
  | line (p : Point)
  /-- A quadratic Bézier with control point `c` to `p`. -/
  | quad (c p : Point)
  /-- A cubic Bézier with control points `c1`, `c2` to `p`. -/
  | cubic (c1 c2 p : Point)
  /-- Close the subpath with a line to its start. -/
  | close
  deriving BEq, Inhabited, Repr

/-- A path: commands in order. A command before the first `move` starts at the origin. -/
structure Path where
  /-- The commands. -/
  cmds : Array PathCmd := #[]
  deriving BEq, Inhabited, Repr

/-- A polyline from flattening: its points and whether it is closed. -/
structure Polyline where
  /-- The points in order. -/
  points : Array Point
  /-- Whether the last point joins the first. -/
  closed : Bool
  deriving BEq, Inhabited, Repr

namespace PathCmd

/-- The command's points, control points included. -/
def points : PathCmd → List Point
  | .move p | .line p => [p]
  | .quad c p => [c, p]
  | .cubic c1 c2 p => [c1, c2, p]
  | .close => []

/-- The command under a transform. -/
def transform (m : Affine) : PathCmd → PathCmd
  | .move p => .move (m.apply p)
  | .line p => .line (m.apply p)
  | .quad c p => .quad (m.apply c) (m.apply p)
  | .cubic c1 c2 p => .cubic (m.apply c1) (m.apply c2) (m.apply p)
  | .close => .close

end PathCmd

namespace Path

/-- The empty path. -/
def empty : Path := {}

/-- The path with a new subpath started at `p`. -/
def moveTo (path : Path) (p : Point) : Path := ⟨path.cmds.push (.move p)⟩

/-- The path with a line to `p`. -/
def lineTo (path : Path) (p : Point) : Path := ⟨path.cmds.push (.line p)⟩

/-- The path with a quadratic Bézier through `c` to `p`. -/
def quadTo (path : Path) (c p : Point) : Path := ⟨path.cmds.push (.quad c p)⟩

/-- The path with a cubic Bézier through `c1`, `c2` to `p`. -/
def cubicTo (path : Path) (c1 c2 p : Point) : Path := ⟨path.cmds.push (.cubic c1 c2 p)⟩

/-- The path with its current subpath closed. -/
def close (path : Path) : Path := ⟨path.cmds.push .close⟩

/-- Both paths' commands, `p` first. -/
def append (p q : Path) : Path := ⟨p.cmds ++ q.cmds⟩

/-- An open polyline through the points (the empty path for no points). -/
def polyline (ps : Array Point) : Path :=
  ⟨(List.range ps.size).toArray.filterMap fun i =>
    ps[i]?.map fun p => if i == 0 then .move p else .line p⟩

/-- The closed rectangle with corners `(x, y)` and `(x + w, y + h)`, drawn clockwise on
screen. -/
def rect (x y w h : Float) : Path :=
  ((((empty.moveTo ⟨x, y⟩).lineTo ⟨x + w, y⟩).lineTo ⟨x + w, y + h⟩).lineTo ⟨x, y + h⟩).close

/-- The ratio of the control distance to the radius for a cubic quarter circle,
`4 (√2 - 1) / 3`. -/
def kappa : Float := 0.5522847498307936

/-- The closed ellipse with centre `c` and radii `rx`, `ry`, as four cubic quarter arcs (radial
error below 0.03 % of the radius). -/
def ellipse (c : Point) (rx ry : Float) : Path :=
  let k := kappa
  let p := fun (dx dy : Float) => (⟨c.x + dx, c.y + dy⟩ : Point)
  (((((empty.moveTo (p rx 0)).cubicTo (p rx (k * ry)) (p (k * rx) ry) (p 0 ry)).cubicTo
    (p (-k * rx) ry) (p (-rx) (k * ry)) (p (-rx) 0)).cubicTo (p (-rx) (-k * ry))
    (p (-k * rx) (-ry)) (p 0 (-ry))).cubicTo (p (k * rx) (-ry)) (p rx (-k * ry)) (p rx 0)).close

/-- The number of cubic pieces of an arc of sweep `Δ` radians: `⌈|Δ| / (π/2)⌉`, at least 1 and
at most 4 (a sweep beyond a full turn is drawn as a full turn); 0 for a sweep that is not
finite. -/
def arcPieceCount (sweep : Float) : Nat :=
  if sweep.isNaN || sweep.isInf then 0
  else
    let q := (sweep.abs / (3.141592653589793 / 2)).ceil
    if q ≤ 1 then 1 else if q ≥ 4 then 4 else q.toUInt64.toNat

/-- The largest radial error of the cubic piece of sweep `δ` (at most a quarter turn) of a
circle of radius `r`, as a distance: `r (2/27) sin⁶(δ/4) / cos²(δ/4)` (see the module
docstring). -/
def arcError (r δ : Float) : Float :=
  let s := (δ / 4).sin
  let c := (δ / 4).cos
  r.abs * 2 / 27 * s ^ 6 / (c * c)

/-- The cubic pieces of the arc of the circle with centre `c` and radius `r` from angle `θ₀` to
`θ₁` (radians; a point at angle `θ` is `c + r (cos θ, sin θ)`, so on screen, with `y` down, a
growing angle turns clockwise). The sweep `θ₁ - θ₀` is clamped to one full turn either way; the
commands start where the arc starts (no move). No commands when the radius or an angle is not
finite. -/
def arcCmds (c : Point) (r θ₀ θ₁ : Float) : Array PathCmd := Id.run do
  let bad := fun (x : Float) => x.isNaN || x.isInf
  if bad r || bad θ₀ || bad θ₁ then return #[]
  let tau := 2 * 3.141592653589793
  let sweep := max (-tau) (min tau (θ₁ - θ₀))
  let n := arcPieceCount sweep
  let δ := sweep / n.toFloat
  let k := 4 / 3 * (δ / 4).tan * r
  let at_ := fun (θ : Float) => (⟨c.x + r * θ.cos, c.y + r * θ.sin⟩ : Point)
  let tangent := fun (θ : Float) => (⟨-θ.sin, θ.cos⟩ : Point)
  let mut out := #[]
  for i in [0:n] do
    let a := θ₀ + δ * i.toFloat
    let b := if i + 1 == n then θ₀ + sweep else θ₀ + δ * (i + 1).toFloat
    out := out.push (.cubic (at_ a + k * tangent a) (at_ b - k * tangent b) (at_ b))
  return out

/-- The open arc of the circle with centre `c` and radius `r` from angle `θ₀` to `θ₁` (see
`arcCmds`), starting with a move to its first point; the empty path for a sweep or radius that is
not finite. -/
def arc (c : Point) (r θ₀ θ₁ : Float) : Path :=
  let cmds := arcCmds c r θ₀ θ₁
  if cmds.isEmpty then empty
  else ⟨#[.move ⟨c.x + r * θ₀.cos, c.y + r * θ₀.sin⟩] ++ cmds⟩

/-- The path continued by the arc from angle `θ₀` to `θ₁` (see `arcCmds`): a line to the arc's
first point, then the arc; for a sector, `(empty.moveTo c).arcTo c r θ₀ θ₁ |>.close`. -/
def arcTo (path : Path) (c : Point) (r θ₀ θ₁ : Float) : Path :=
  let cmds := arcCmds c r θ₀ θ₁
  if cmds.isEmpty then path
  else ⟨path.cmds.push (.line ⟨c.x + r * θ₀.cos, c.y + r * θ₀.sin⟩) ++ cmds⟩

/-- The closed rectangle with corners `(x, y)` and `(x + w, y + h)` and its corners rounded to
quarter circles of radius `r` (clamped to `0` and to half the shorter side), each a cubic arc
(`kappa`), drawn clockwise on screen. Its area is `w h - (4 - π) r²` to within the cubic arcs'
error. -/
def roundedRect (x y w h r : Float) : Path :=
  let r := max 0 (min r (min (w / 2) (h / 2)))
  let k := kappa * r
  let (x1, y1) := (x + w, y + h)
  empty
    |>.moveTo ⟨x + r, y⟩ |>.lineTo ⟨x1 - r, y⟩
    |>.cubicTo ⟨x1 - r + k, y⟩ ⟨x1, y + r - k⟩ ⟨x1, y + r⟩ |>.lineTo ⟨x1, y1 - r⟩
    |>.cubicTo ⟨x1, y1 - r + k⟩ ⟨x1 - r + k, y1⟩ ⟨x1 - r, y1⟩ |>.lineTo ⟨x + r, y1⟩
    |>.cubicTo ⟨x + r - k, y1⟩ ⟨x, y1 - r + k⟩ ⟨x, y1 - r⟩ |>.lineTo ⟨x, y + r⟩
    |>.cubicTo ⟨x, y + r - k⟩ ⟨x + r - k, y⟩ ⟨x + r, y⟩ |>.close

/-- The path under the transform. -/
def transform (m : Affine) (path : Path) : Path := ⟨path.cmds.map (·.transform m)⟩

/-- The box of every point of the path, control points included; `none` without points. -/
def controlBounds (path : Path) : Option Box :=
  Box.ofPoints (path.cmds.foldl (fun acc c => acc ++ c.points.toArray) #[])

/-- The parameters in `(0, 1)` where one coordinate of a Bézier with coefficients `cs` (three or
four) has a zero derivative. -/
private def extremaParams (cs : List Float) : List Float :=
  let inside := fun (t : Float) => t > 0 && t < 1
  match cs with
  | [a, b, c] =>
    let d := a - 2 * b + c
    if d == 0 then [] else [(a - b) / d].filter inside
  | [a, b, c, e] =>
    let qa := -a + 3 * b - 3 * c + e
    let qb := 2 * (a - 2 * b + c)
    let qc := b - a
    if qa.abs < 1e-12 then (if qb == 0 then [] else [-qc / qb].filter inside)
    else
      let disc := qb * qb - 4 * qa * qc
      if disc < 0 then []
      else [(-qb + disc.sqrt) / (2 * qa), (-qb - disc.sqrt) / (2 * qa)].filter inside
  | _ => []

/-- The point at `t` of the Bézier with control points `ps` (two to four). -/
def bezierAt (ps : List Point) (t : Float) : Point :=
  match ps with
  | [p, q] => p.lerp q t
  | [p, c, q] => (p.lerp c t).lerp (c.lerp q t) t
  | [p, c1, c2, q] =>
    let a := p.lerp c1 t
    let b := c1.lerp c2 t
    let c := c2.lerp q t
    (a.lerp b t).lerp (b.lerp c t) t
  | _ => ⟨0, 0⟩

/-- The tight box of the path: end points and the extrema of every curve; `none` without
points. -/
def bounds (path : Path) : Option Box := Id.run do
  let mut pts : Array Point := #[]
  let mut cur : Point := ⟨0, 0⟩
  let mut start : Point := ⟨0, 0⟩
  for c in path.cmds do
    match c with
    | .move p => pts := pts.push p; cur := p; start := p
    | .line p => pts := pts.push p; cur := p
    | .close => cur := start
    | .quad c1 p =>
      let ctrl := [cur, c1, p]
      pts := pts.push p
      for t in extremaParams (ctrl.map (·.x)) ++ extremaParams (ctrl.map (·.y)) do
        pts := pts.push (bezierAt ctrl t)
      cur := p
    | .cubic c1 c2 p =>
      let ctrl := [cur, c1, c2, p]
      pts := pts.push p
      for t in extremaParams (ctrl.map (·.x)) ++ extremaParams (ctrl.map (·.y)) do
        pts := pts.push (bezierAt ctrl t)
      cur := p
  return Box.ofPoints pts

/-- The most pieces one curve is cut into by `flatten`. -/
def maxPieces : Nat := 4096

/-- The number of equal parameter steps that keep a curve whose chord error is at most
`k / n²` within `tol` (at least 1, at most `maxPieces`). -/
def piecesFor (k tol : Float) : Nat :=
  if !(k > 0) || !(tol > 0) || k.isInf then (if k.isInf then maxPieces else 1)
  else
    let n := (k / tol).sqrt.ceil
    if n.isNaN || n < 1 then 1
    else if n ≥ maxPieces.toFloat then maxPieces else n.toUInt64.toNat

/-- The path as polylines, every curve within `tol` of its chords (in the path's units). Each
subpath becomes one polyline; `close` marks it closed. -/
def flatten (path : Path) (tol : Float := 0.1) : Array Polyline := Id.run do
  let mut out : Array Polyline := #[]
  let mut cur : Array Point := #[]
  let mut pos : Point := ⟨0, 0⟩
  let mut start : Point := ⟨0, 0⟩
  for c in path.cmds do
    match c with
    | .move p =>
      if cur.size > 1 then out := out.push ⟨cur, false⟩
      cur := #[p]; pos := p; start := p
    | .line p =>
      if cur.isEmpty then cur := #[pos]
      cur := cur.push p; pos := p
    | .quad c1 p =>
      if cur.isEmpty then cur := #[pos]
      let d := (pos - (2 : Float) * c1 + p).norm
      let n := piecesFor (d / 4) tol
      for i in [1:n + 1] do cur := cur.push (bezierAt [pos, c1, p] (i.toFloat / n.toFloat))
      pos := p
    | .cubic c1 c2 p =>
      if cur.isEmpty then cur := #[pos]
      let d := max (pos - (2 : Float) * c1 + c2).norm (c1 - (2 : Float) * c2 + p).norm
      let n := piecesFor (3 * d / 4) tol
      for i in [1:n + 1] do cur := cur.push (bezierAt [pos, c1, c2, p] (i.toFloat / n.toFloat))
      pos := p
    | .close =>
      if cur.size > 1 then out := out.push ⟨cur, true⟩
      cur := #[]; pos := start
  if cur.size > 1 then out := out.push ⟨cur, false⟩
  return out

end Path

end PILean
