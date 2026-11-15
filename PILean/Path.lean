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
  `close` build one; `Path.rect`, `Path.polyline`, `Path.ellipse` common shapes.
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
