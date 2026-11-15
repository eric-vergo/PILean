/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Path

/-!
# Strokes

A stroke of a path as polygons to fill: the stroke's outline is the union of one rectangle per
segment, a join at every corner and a cap at each open end, all wound the same way, so that
filling them with the non-zero rule gives the stroke without seams.

* **Width**, **caps** (butt, round, square), **joins** (miter with a miter limit, falling back
  to bevel as SVG does; round; bevel), **dashes** (lengths alternately on and off, repeated,
  started `dashOffset` into the pattern), as SVG and PostScript define them.
* **Curves** are flattened first by `Path.flatten` with the stroke's tolerance (the deviation of
  the flattened curve from the true one, in pixels).
* **Hairlines on pixel centres**: `crisp` puts a coordinate on the nearest pixel centre, so that
  a one-pixel horizontal or vertical line covers one row or column of pixels exactly.

## Main definitions

* `Cap`, `Join`, `Stroke`.
* `strokePolygons`: a path's stroke as closed polygons.
* `dashPolyline`: a polyline cut by a dash pattern.
* `crisp`.
-/

namespace PILean.Raster

/-- How an open subpath ends. -/
inductive Cap where
  /-- At the end point. -/
  | butt
  /-- A half disc. -/
  | round
  /-- Half a width beyond the end point. -/
  | square
  deriving BEq, Inhabited, Repr

/-- How segments meet. -/
inductive Join where
  /-- Extended edges meeting at a point, within the miter limit, else bevelled. -/
  | miter
  /-- A disc. -/
  | round
  /-- The outer corners joined by a straight line. -/
  | bevel
  deriving BEq, Inhabited, Repr

/-- A stroke's style. -/
structure Stroke where
  /-- The width. -/
  width : Float := 1
  /-- The caps. -/
  cap : Cap := .butt
  /-- The joins. -/
  join : Join := .miter
  /-- The miter limit: the most the miter length may be, in widths (SVG's default, 4). -/
  miterLimit : Float := 4
  /-- The dash pattern (empty: solid). -/
  dash : Array Float := #[]
  /-- Where in the dash pattern the stroke starts. -/
  dashOffset : Float := 0
  /-- The flattening tolerance, in pixels. -/
  tolerance : Float := 0.1
  deriving Inhabited, Repr

/-- The nearest pixel centre of a coordinate (`⌊v⌋ + ½`). -/
def crisp (v : Float) : Float := v.floor + 0.5

/-- The most polygon points a stroke may produce. -/
def maxStrokePoints : Nat := 4000000

/-- Twice the signed area of a polygon. -/
def signedArea2 (ps : Array Point) : Float := Id.run do
  let mut s := 0
  for i in [0:ps.size] do
    let p := ps[i]?.getD ⟨0, 0⟩
    let q := ps[(i + 1) % ps.size]?.getD ⟨0, 0⟩
    s := s + (p.x * q.y - q.x * p.y)
  return s

/-- The polygon wound positively (reversed if its signed area is negative). -/
def orient (ps : Array Point) : Array Point := if signedArea2 ps < 0 then ps.reverse else ps

/-- A disc of radius `r` as a polygon within `tol` of the circle. -/
def disc (c : Point) (r tol : Float) : Array Point := Id.run do
  if r ≤ 0 then return #[]
  let tol := max tol 0.01
  let ratio := max (-1) (min 1 (1 - tol / r))
  let step := 2 * Float.acos ratio
  let n : Nat := max 8 (min 1024 (if step > 0 then (6.283185307179586 / step).ceil.toUInt64.toNat
    else 1024))
  return (Array.range n).map fun i =>
    let t := 6.283185307179586 * i.toFloat / n.toFloat
    ⟨c.x + r * Float.cos t, c.y + r * Float.sin t⟩

/-- The unit vector of `d`, or `none` for a zero vector. -/
def unit? (d : Point) : Option Point :=
  let n := d.norm
  if n == 0 || n.isNaN then none else some ⟨d.x / n, d.y / n⟩

/-- The pieces of the stroke of one polyline (see the module docstring). -/
def polylinePieces (st : Stroke) (pts : Array Point) (closed : Bool) : Array (Array Point) :=
  Id.run do
  -- drop repeated points
  let pts := pts.foldl (init := #[]) fun acc p =>
    if acc.back? == some p then acc else acc.push p
  let pts := if closed && pts.size > 1 && pts.back? == pts[0]? then pts.pop else pts
  let hw := st.width / 2
  if hw ≤ 0 || hw.isNaN then return #[]
  let mut out : Array (Array Point) := #[]
  if pts.size == 1 then
    -- a dot: drawn by round and square caps only
    let p := pts[0]?.getD ⟨0, 0⟩
    match st.cap with
    | .round => return #[disc p hw st.tolerance]
    | .square => return #[#[⟨p.x - hw, p.y - hw⟩, ⟨p.x + hw, p.y - hw⟩, ⟨p.x + hw, p.y + hw⟩,
        ⟨p.x - hw, p.y + hw⟩]]
    | .butt => return #[]
  let n := pts.size
  let segs := if closed then n else n - 1
  for i in [0:segs] do
    let p := pts[i]?.getD ⟨0, 0⟩
    let q := pts[(i + 1) % n]?.getD ⟨0, 0⟩
    let some u := unit? (q - p) | continue
    let nv : Point := ⟨-u.y * hw, u.x * hw⟩
    -- square caps lengthen the first and last segments of an open polyline
    let ext := fun (first : Bool) =>
      if !closed && st.cap == .square && ((first && i == 0) || (!first && i + 1 == segs)) then
        hw else 0
    let p' := p - ext true * u
    let q' := q + ext false * u
    out := out.push (orient #[p' + nv, q' + nv, q' - nv, p' - nv])
  -- joins
  let corners := if closed then (List.range n).toArray else (List.range' 1 (n - 2)).toArray
  for i in corners do
    let p := pts[(i + n - 1) % n]?.getD ⟨0, 0⟩
    let c := pts[i]?.getD ⟨0, 0⟩
    let q := pts[(i + 1) % n]?.getD ⟨0, 0⟩
    let (some u1, some u2) := (unit? (c - p), unit? (q - c)) | continue
    let cross := u1.x * u2.y - u1.y * u2.x
    if cross == 0 && u1.x * u2.x + u1.y * u2.y > 0 then continue
    match st.join with
    | .round => out := out.push (orient (disc c hw st.tolerance))
    | j =>
      -- the outer side: left of the travel for a right turn, and so on
      let s : Float := if cross > 0 then -1 else 1
      let a := c + (s * hw) * (⟨-u1.y, u1.x⟩ : Point)
      let b := c + (s * hw) * (⟨-u2.y, u2.x⟩ : Point)
      let cosT := -(u1.x * u2.x + u1.y * u2.y)
      -- the miter length over the width is 1 / sin(θ/2), θ the angle between the segments
      let sinHalf := ((1 - cosT) / 2).sqrt
      if j == .miter && sinHalf > 0 && 1 / sinHalf ≤ st.miterLimit then
        let bis := unit? ((a - c) + (b - c))
        match bis with
        | some v =>
          let tip := c + (hw / sinHalf) * v
          out := out.push (orient #[c, a, tip, b])
        | none => out := out.push (orient #[c, a, b])
      else out := out.push (orient #[c, a, b])
  -- round caps
  if !closed && st.cap == .round then
    out := out.push (disc (pts[0]?.getD ⟨0, 0⟩) hw st.tolerance)
    out := out.push (disc (pts.back?.getD ⟨0, 0⟩) hw st.tolerance)
  return out

/-- A polyline cut by a dash pattern starting `offset` into it: the pieces drawn, open. An
empty, negative or all-zero pattern draws the whole polyline. -/
def dashPolyline (pts : Array Point) (closed : Bool) (pattern : Array Float) (offset : Float) :
    Array (Array Point) := Id.run do
  let total := pattern.foldl (· + ·) 0
  if pattern.isEmpty || total ≤ 0 || pattern.any (fun d => d < 0 || d.isNaN) then
    return #[if closed then pts.push (pts[0]?.getD ⟨0, 0⟩) else pts]
  let pts := if closed then pts.push (pts[0]?.getD ⟨0, 0⟩) else pts
  -- the position in the pattern
  let off := offset - total * (offset / total).floor
  let mut idx := 0
  let mut left := pattern[0]?.getD 0
  let mut skip := off
  for _ in [0:pattern.size * 2 + 2] do
    if skip < left then break
    skip := skip - left
    idx := (idx + 1) % pattern.size
    left := pattern[idx]?.getD 0
  left := left - skip
  let mut on := idx % 2 == 0
  let mut out : Array (Array Point) := #[]
  let mut cur : Array Point := if on then #[pts[0]?.getD ⟨0, 0⟩] else #[]
  let mut pieces := 0
  for i in [0:pts.size - 1] do
    let mut p := pts[i]?.getD ⟨0, 0⟩
    let q := pts[i + 1]?.getD ⟨0, 0⟩
    let mut segLeft := (q - p).norm
    for _ in [0:100000] do
      if segLeft ≤ left then
        left := left - segLeft
        if on then cur := cur.push q
        break
      -- the dash or gap ends inside this segment
      let t := left / segLeft
      let m := p + t * (q - p)
      if on then
        out := out.push (cur.push m); cur := #[]
      else cur := #[m]
      pieces := pieces + 1
      segLeft := segLeft - left
      p := m
      on := !on
      idx := (idx + 1) % pattern.size
      left := pattern[idx]?.getD 0
    if pieces > maxStrokePoints then break
  if on && cur.size > 1 then out := out.push cur
  return out

/-- A path's stroke as closed polygons, every one wound positively; their non-zero fill is the
stroke. -/
def strokePolygons (path : Path) (st : Stroke) : Array (Array Point) := Id.run do
  let mut out := #[]
  let mut count := 0
  for pl in path.flatten st.tolerance do
    let pieces := if st.dash.isEmpty then #[(pl.points, pl.closed)]
      else (dashPolyline pl.points pl.closed st.dash st.dashOffset).map (·, false)
    for (pts, closed) in pieces do
      for poly in polylinePieces st pts closed do
        count := count + poly.size
        if count > maxStrokePoints then return out
        out := out.push poly
  return out

end PILean.Raster
