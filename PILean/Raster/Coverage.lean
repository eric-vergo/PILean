/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Path

/-!
# Coverage

The anti-aliased scanline fill: the coverage of each pixel by a set of closed polylines under
the non-zero or the even-odd rule, as runs of pixels of equal coverage.

## The method

Every edge is cut at the pixel grid into pieces, each inside one pixel (a *cell*). A piece
going down by `dy` adds `dy` to its cell's *cover* (the winding it carries to the cells right of
it) and `dy · (xa + xb)` to the cell's *area* (twice the area of the piece's trapezoid to the
cell's left edge, `xa` and `xb` the piece's ends from that edge). Sweeping a row from the left,
the signed winding area of a cell is `512 · C − A` (in units of 1/131072 of a pixel), `C` the
covers of the cells up to and including it and `A` its area; past the last cell of a run the
winding is `C` whole. The non-zero rule takes the winding area's magnitude, at most one pixel;
the even-odd rule folds it modulo two pixels. This is exact area coverage for a polygon whose
edges do not cross inside one pixel (where they do, the two rules' usual approximation applies,
as in font rasterisers).

## Arithmetic

Coordinates are rounded to 1/256 of a pixel (`subpixel`); everything after that is integer
arithmetic, with the crossing of an edge and a pixel boundary rounded to the nearest 1/256
pixel. The result is the same on every machine, and coverage is computed exactly for edges on
the 1/256 grid between their crossings. The conversion of the input's `Float` coordinates is the
only floating-point step.

## Bounds

Work is bounded by the image and the edges: rows above or below the image are not visited,
edges are clipped to it (an edge left of the image becomes a vertical edge at its left side,
which covers the same pixels; one right of it is dropped), so an edge costs at most one piece
per pixel it crosses. Polylines with more than `maxPoints` points in all are rejected.

## Main definitions

* `FillRule`, `Span`, `IRect`.
* `coverage`: the spans of a fill, clipped to a rectangle.
* `Span.alphaAt`, `spansAlpha`: the coverage of a pixel.

## References

* The cell accumulation follows the published descriptions of signed-area scan conversion
  (Raph Levien's description of the font-rs rasteriser, 2016; the FreeType project's
  description of its anti-aliasing rasteriser): the method, not code.
-/

namespace PILean.Raster

/-- How overlapping areas count: inside where the winding number is not zero, or where it is
odd. -/
inductive FillRule where
  /-- Non-zero winding. -/
  | nonZero
  /-- Even-odd. -/
  | evenOdd
  deriving BEq, Inhabited, Repr

/-- A rectangle of pixels `[x0, x1) × [y0, y1)`. -/
structure IRect where
  /-- Left. -/
  x0 : Nat
  /-- Top. -/
  y0 : Nat
  /-- Right (exclusive). -/
  x1 : Nat
  /-- Bottom (exclusive). -/
  y1 : Nat
  deriving BEq, Inhabited, Repr

/-- The intersection of two rectangles (empty when they do not meet). -/
def IRect.inter (a b : IRect) : IRect :=
  let x0 := max a.x0 b.x0
  let y0 := max a.y0 b.y0
  ⟨x0, y0, max x0 (min a.x1 b.x1), max y0 (min a.y1 b.y1)⟩

/-- A run of pixels on row `y`, from `x` for `len` pixels, all with coverage `alpha` (0 none,
255 whole). -/
structure Span where
  /-- The row. -/
  y : Nat
  /-- The first pixel. -/
  x : Nat
  /-- The number of pixels. -/
  len : Nat
  /-- The coverage. -/
  alpha : UInt8
  deriving BEq, Inhabited, Repr

/-- Whether a span lies inside a rectangle. -/
def Span.inside (r : IRect) (s : Span) : Bool :=
  r.y0 ≤ s.y && s.y < r.y1 && r.x0 ≤ s.x && s.x + s.len ≤ r.x1

/-- Subpixels per pixel. -/
def subpixel : Int := 256

/-- The most points `coverage` accepts in all its polylines. -/
def maxPoints : Nat := 4000000

/-- `a / b` rounded to the nearest integer, halves away from zero; 0 when `b = 0`. -/
def roundDiv (a b : Int) : Int :=
  if b == 0 then 0
  else
    let q := (2 * a.natAbs + b.natAbs) / (2 * b.natAbs)
    if (a < 0) != (b < 0) then -(q : Int) else q

/-- A float coordinate in subpixels, rounded, within ±2³⁰ (a non-finite value gives 0). -/
def toSub (v : Float) : Int :=
  if v.isNaN then 0
  else
    let s := v * 256
    let s := if s > 1073741824 then 1073741824 else if s < -1073741824 then -1073741824 else s
    let r := (s.abs + 0.5).floor
    let n : Int := r.toUInt64.toNat
    if s < 0 then -n else n

/-- A cell's contribution: row-major key, cover and area. -/
abbrev Cell := Int × Int × Int

/-- The pieces of an edge inside one row band, from `(xa, ya)` to `(xb, yb)` with `ya < yb`,
cut at the pixel columns, as cells of row `row` (keys `row * stride + column`). `sign` is +1 for
an edge going down, -1 going up. -/
def rowPieces (stride row : Int) (sign xa ya xb yb : Int) (out : Array Cell) : Array Cell :=
  Id.run do
  let mut out := out
  -- the multiples of 256 strictly between xa and xb, in the direction of travel
  let lo := min xa xb
  let hi := max xa xb
  let first := (lo / subpixel + 1) * subpixel
  let count := if first < hi then ((hi - 1) / subpixel - lo / subpixel).toNat else 0
  let mut px := xa
  let mut py := ya
  for i in [0:count + 1] do
    let (qx, qy) :=
      if i < count then
        let bx := if xa < xb then first + subpixel * i else first + subpixel * (count - 1 - i)
        (bx, ya + roundDiv ((yb - ya) * (bx - xa)) (xb - xa))
      else (xb, yb)
    let col := min px qx / subpixel
    let fp := px - col * subpixel
    let fq := qx - col * subpixel
    let dy := sign * (qy - py)
    if dy != 0 then out := out.push (row * stride + col, dy, dy * (fp + fq))
    px := qx; py := qy
  return out

/-- The cells of one edge from `(ax, ay)` to `(bx, by)` (subpixels) in an image `w` × `h`
pixels, after clipping it to the image (see the module docstring). -/
def edgeCells (w h : Nat) (ax ay bx by_ : Int) (out : Array Cell) : Array Cell := Id.run do
  if ay == by_ then return out
  let sign : Int := if by_ > ay then 1 else -1
  let (x0, y0, x1, y1) := if by_ > ay then (ax, ay, bx, by_) else (bx, by_, ax, ay)
  let top := 0
  let bottom := (h : Int) * subpixel
  if y1 ≤ top || y0 ≥ bottom then return out
  let xAt := fun (y : Int) => x0 + roundDiv ((x1 - x0) * (y - y0)) (y1 - y0)
  let (x0, y0) := if y0 < top then (xAt top, top) else (x0, y0)
  let (x1, y1) := if y1 > bottom then (xAt bottom, bottom) else (x1, y1)
  if y0 ≥ y1 then return out
  -- split at the image's left and right sides
  let right := (w : Int) * subpixel
  let yAtX := fun (x : Int) => y0 + roundDiv ((y1 - y0) * (x - x0)) (x1 - x0)
  let mut pts : Array (Int × Int) := #[(x0, y0)]
  let mut cuts : Array (Int × Int) := #[]
  for b in [0, right] do
    if (x0 < b && b < x1) || (x1 < b && b < x0) then cuts := cuts.push (b, yAtX b)
  cuts := cuts.qsort (fun p q => p.2 < q.2)
  pts := pts ++ cuts |>.push (x1, y1)
  let stride := (w : Int) + 2
  let mut out := out
  for i in [0:pts.size - 1] do
    let (pa, ya) := pts[i]?.getD (0, 0)
    let (pb, yb) := pts[i + 1]?.getD (0, 0)
    if ya ≥ yb then continue
    -- a piece right of the image changes no visible pixel; one left of it counts at x = 0
    if pa ≥ right && pb ≥ right then continue
    let pa := max 0 (min right pa)
    let pb := max 0 (min right pb)
    let firstRow := ya / subpixel
    let lastRow := (yb - 1) / subpixel
    for r in [firstRow.toNat:lastRow.toNat + 1] do
      let rt := (r : Int) * subpixel
      let sa := max ya rt
      let sb := min yb (rt + subpixel)
      if sa ≥ sb then continue
      let xs := fun (y : Int) => pa + roundDiv ((pb - pa) * (y - ya)) (yb - ya)
      out := rowPieces stride r sign (xs sa) sa (xs sb) sb out
  return out

/-- The coverage of a winding area (`512 · C − A`, 131072 a whole pixel) under a rule, 0 to
255 (in 1/255 of a pixel). -/
def coverageOf (rule : FillRule) (v : Int) : Nat :=
  let full : Nat := 131072
  let m := v.natAbs
  let m := match rule with
    | .nonZero => min m full
    | .evenOdd => let t := m % (2 * full); if t > full then 2 * full - t else t
  (m * 255 + full / 2) / full

/-- `coverageOf` as a byte (it is at most 255, `coverageOf_le`, so nothing is cut off). -/
def alphaOf (rule : FillRule) (v : Int) : UInt8 := (coverageOf rule v).toUInt8

/-- The spans of a fill (see `coverage`), before the spans are filtered to the clip (`coverage`). -/
def coverageRaw (polys : Array (Array Point)) (rule : FillRule) (w h : Nat) (clip : IRect) :
    Option (Array Span) := Id.run do
  let total := polys.foldl (fun n p => n + p.size) 0
  if total > maxPoints then return none
  let clip := clip.inter ⟨0, 0, w, h⟩
  let mut found : Array Cell := #[]
  for poly in polys do
    if poly.size < 2 then continue
    let pts := poly.map fun p => (toSub p.x, toSub p.y)
    for i in [0:pts.size] do
      let (ax, ay) := pts[i]?.getD (0, 0)
      let (bx, by_) := pts[(i + 1) % pts.size]?.getD (0, 0)
      found := edgeCells w h ax ay bx by_ found
  let sorted := found.qsort (fun a b => a.1 < b.1)
  let cells := sorted
  let stride := (w : Int) + 2
  let mut out : Array Span := #[]
  let mut i := 0
  for _ in [0:cells.size] do
    if i ≥ cells.size then break
    let row := (cells[i]?.getD (0, 0, 0)).1 / stride
    -- the row's cells, merged by column
    let mut acc : Int := 0
    for _ in [0:cells.size] do
      if i ≥ cells.size then break
      let (k, _, _) := cells[i]?.getD (0, 0, 0)
      if k / stride != row then break
      let col := k % stride
      let mut cov : Int := 0
      let mut area : Int := 0
      for _ in [0:cells.size] do
        let (k2, c2, a2) := cells[i]?.getD (-1, 0, 0)
        if k2 != k || i ≥ cells.size then break
        cov := cov + c2; area := area + a2; i := i + 1
      acc := acc + cov
      let a := alphaOf rule (512 * acc - area)
      let next := match cells[i]? with
        | some (k3, _, _) => if k3 / stride == row then k3 % stride else (w : Int)
        | none => (w : Int)
      let y := row.toNat
      if y < clip.y0 || y ≥ clip.y1 then continue
      -- the cell itself
      let cx := col.toNat
      if a != 0 && clip.x0 ≤ cx && cx < clip.x1 then out := out.push ⟨y, cx, 1, a⟩
      -- the run up to the next cell
      let runA := alphaOf rule (512 * acc)
      let s := max (cx + 1) clip.x0
      let e := min next.toNat clip.x1
      if runA != 0 && s < e then out := out.push ⟨y, s, e - s, runA⟩
  return some out

/-- The spans of the pixels that closed polylines cover, in an image `w` × `h`, clipped to
`clip`: rows top to bottom, spans left to right, none of coverage 0; or `none` past
`maxPoints`. Every span lies inside `clip` and the image (`coverage_inside`): the spans are
inside by construction, and the filter makes that a guarantee. -/
def coverage (polys : Array (Array Point)) (rule : FillRule) (w h : Nat) (clip : IRect) :
    Option (Array Span) :=
  (coverageRaw polys rule w h clip).map (·.filter (Span.inside (clip.inter ⟨0, 0, w, h⟩)))

/-- The coverage of pixel `(x, y)` in a list of spans (0 outside them). -/
def spansAlpha (spans : Array Span) (x y : Nat) : UInt8 :=
  match spans.find? fun s => s.y == y && s.x ≤ x && x < s.x + s.len with
  | some s => s.alpha
  | none => 0

end PILean.Raster
