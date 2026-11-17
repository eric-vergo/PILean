/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Graph.Layout

/-!
# Routes of edges through the free space of a layered drawing

An edge of a layered drawing runs from its upper node down through the layers to its lower
node. The room it may use is a sequence of *gates* (Gansner, Koutsofios, North and Vo call the
regions between them boxes): at the lower edge of the layer it leaves, at the upper and lower
edge of every layer it crosses and at the upper edge of the layer it enters, a stretch across the
layer between its neighbours there. Between two layers every route is free.

The route is found in two steps, as in section 5 of that paper:

1. **The shortest route** (`tautRoute`): the polyline from the start through every gate to the
   end that is as short as can be, a string pulled tight. It bends only at ends of gates, and an
   edge with nothing in its way is one straight line. The gates lie one below the other, so the
   funnel of directions that still pass every gate seen is an interval of slopes, and the method
   of Lee and Preparata (as simplified by Hershberger and Snoeyink) needs no triangulation.
2. **The curve** (`roundedPieces`, `fitPieces`): one piecewise Bézier curve along the shortest
   route, which rounds each of its bends by a parabola from the middle of the part before the
   bend to the middle of the part after it (the quadratic B-spline of the route). It turns no
   more than the route does and never the other way. A parabola that leaves the room it was
   given (`Zone`) is drawn closer to its bend, by halves, and after a few rounds the bend is
   left a corner: the polyline itself always fits.

Work: `O(k²)` for the shortest route through `k` gates at worst and `O(k)` when it bends
seldom; `O(k · s)` per round of the fit for `s` samples of every piece.

## References

* Gansner, Koutsofios, North, Vo, *A technique for drawing directed graphs*, IEEE Transactions
  on Software Engineering 19 (1993), section 5.
* Lee, Preparata, *Euclidean shortest paths in the presence of rectilinear barriers*, Networks
  14 (1984).
* Hershberger, Snoeyink, *Computing minimum length paths of a given homotopy class*,
  Computational Geometry 4 (1994).

## Main definitions

* `Gate`, `tautRoute`: the shortest route.
* `Zone`, `roundedPieces`, `piecesFit`, `fitPieces`: the curve.
* `shortenEnd`, `shortenStart`: room for an arrowhead.
-/

namespace PILean.Graph

/-- A number larger than any coordinate or slope of a drawing, the bound of an empty funnel. A
constant, so that it is computed once. -/
def beyond : Float := 1e30

/-- The least height between two gates that counts. -/
def leastRise : Float := 1e-9

/-- A gate: at the height `y` (along the layers) a route may pass between `lo` and `hi` (across
the layers). -/
structure Gate where
  /-- The lowest coordinate across the layers. -/
  lo : Float
  /-- The highest coordinate across the layers. -/
  hi : Float
  /-- The height. -/
  y : Float
  deriving Inhabited, Repr

/-- The shortest polyline from `start` through the gates, in order, to `finish`. The heights of
`start`, the gates and `finish` must increase; a gate with `hi < lo` is taken as the point `lo`.
The result starts with `start`, ends with `finish`, and every point between is an end of a
gate. -/
def tautRoute (start : Point) (gates : Array Gate) (finish : Point) : Array Point := Id.run do
  let all := gates.push ⟨finish.x, finish.x, finish.y⟩
  let n := all.size
  let big := beyond
  let mut out : Array Point := #[start]
  let mut apex := start
  -- the slopes (across per along) from the apex that pass every gate looked at, and the gate
  -- ends that bound them
  let mut lo : Float := -big
  let mut hi : Float := big
  let mut loAt := 0
  let mut hiAt := 0
  let mut loPt := start
  let mut hiPt := start
  let mut i := 0
  for _ in [0:n * n + n + 4] do
    if i ≥ n then break
    let g := all.getD i default
    let glo := g.lo
    let ghi := max g.lo g.hi
    let dy := max leastRise (g.y - apex.y)
    let a := (glo - apex.x) / dy
    let b := (ghi - apex.x) / dy
    if a > hi then
      -- the gate lies beyond the high side of the funnel: the route bends there
      apex := hiPt
      out := out.push apex
      i := hiAt + 1
      lo := -big; hi := big; loPt := apex; hiPt := apex; loAt := i; hiAt := i
    else if b < lo then
      apex := loPt
      out := out.push apex
      i := loAt + 1
      lo := -big; hi := big; loPt := apex; hiPt := apex; loAt := i; hiAt := i
    else
      if a > lo then
        lo := a; loPt := ⟨glo, g.y⟩; loAt := i
      if b < hi then
        hi := b; hiPt := ⟨ghi, g.y⟩; hiAt := i
      i := i + 1
  return out.push finish

/-- The room of a route in one layer: between the heights `y0` and `y1` it must stay between
`lo` and `hi`. -/
structure Zone where
  /-- The lowest coordinate across the layers. -/
  lo : Float
  /-- The highest coordinate across the layers. -/
  hi : Float
  /-- The upper height. -/
  y0 : Float
  /-- The lower height. -/
  y1 : Float
  deriving Inhabited, Repr

/-- The point of a cubic piece at the parameter `t`. -/
def pieceAt (p : Piece) (t : Float) : Point :=
  let (a, b, c, d) := p
  let s := 1 - t
  (s * s * s) * a + (3 * s * s * t) * b + (3 * s * t * t) * c + (t * t * t) * d

/-- The straight piece from `p` to `q`. -/
def linePiece (p q : Point) : Piece :=
  (p, p.lerp q (1 / 3), p.lerp q (2 / 3), q)

/-- The curve that rounds the bends of the polyline `pts`: straight along every part, and around
the bend at an inner point a parabola (a quadratic Bézier curve with the bend as its control
point, written as a cubic) that leaves the part before the bend and joins the part after it,
each at the distance `cut i` times the most that the bend may use of the shorter of them: half of
a part between two bends, the whole of a part that ends the polyline. With every `cut` at `1`
(the default for a `cut` shorter than `pts`) the curve is the quadratic B-spline of the polyline;
with `0` it is the polyline. The curve turns exactly as much as the polyline does, never the
other way, and stays inside the triangles of its bends.

Returns the pieces and, for each, the inner point whose bend it rounds (`0` for a straight
piece). -/
def roundedPieces (pts : Array Point) (cut : Array Float := #[]) : Array Piece × Array Nat :=
  Id.run do
  let n := pts.size
  if n < 2 then return (#[], #[])
  let at_ := fun (i : Nat) => pts.getD i ⟨0, 0⟩
  let mut pieces : Array Piece := #[]
  let mut bends : Array Nat := #[]
  let mut cur := at_ 0
  for i in [1:n - 1] do
    let v := at_ i
    let before := (at_ (i - 1)).dist v
    let after := v.dist (at_ (i + 1))
    let share := fun (j : Nat) => if j == 0 || j + 2 == n then (1 : Float) else 0.5
    let d := cut.getD i 1 * min (share (i - 1) * before) (share i * after)
    if d < 0.25 then
      if cur.dist v > 0.01 then
        pieces := pieces.push (linePiece cur v)
        bends := bends.push 0
      cur := v
    else
      let a := v + (d / before) * (at_ (i - 1) - v)
      let c := v + (d / after) * (at_ (i + 1) - v)
      if cur.dist a > 0.01 then
        pieces := pieces.push (linePiece cur a)
        bends := bends.push 0
      pieces := pieces.push (a, a.lerp v (2 / 3), c.lerp v (2 / 3), c)
      bends := bends.push i
      cur := c
  if cur.dist (at_ (n - 1)) > 0.01 || pieces.isEmpty then
    pieces := pieces.push (linePiece cur (at_ (n - 1)))
    bends := bends.push 0
  return (pieces, bends)

/-- The parameter at which a piece whose heights increase reaches the height `y` (by bisection;
`0` or `1` when `y` is outside the piece). -/
def paramAt (p : Piece) (y : Float) : Float := Id.run do
  let mut lo : Float := 0
  let mut hi : Float := 1
  for _ in [0:22] do
    let mid := (lo + hi) / 2
    if (pieceAt p mid).y < y then lo := mid else hi := mid
  return (lo + hi) / 2

/-- For every piece, whether its curve stays in the zones: checked for every zone that the
piece's heights reach, where the piece enters it, where it leaves it and at `samples` parameters
between. The heights along a piece must increase. -/
def piecesFit (pieces : Array Piece) (zones : Array Zone) (samples : Nat := 3)
    (eps : Float := 0.01) : Array Bool :=
  pieces.map fun pc =>
    let (a, _, _, d) := pc
    zones.all fun z =>
      z.y1 < a.y || z.y0 > d.y ||
        (let t0 := if z.y0 ≤ a.y then 0 else paramAt pc z.y0
         let t1 := if z.y1 ≥ d.y then 1 else paramAt pc z.y1
         (Array.range (samples + 2)).all fun k =>
           let p := pieceAt pc (t0 + (t1 - t0) * k.toFloat / (samples + 1).toFloat)
           z.lo - eps ≤ p.x && p.x ≤ z.hi + eps)

/-- The curve along the polyline `pts` that stays in the zones: `roundedPieces`, with the cut
of every bend whose parabola leaves the zones halved, up to `rounds` times, and then dropped, so
that the bend is a corner. When the polyline lies in the zones, so does the result where it is
checked (`piecesFit`). -/
def fitPieces (pts : Array Point) (zones : Array Zone) (rounds : Nat := 5) : Array Piece :=
  Id.run do
  let mut cut : Array Float := Array.replicate pts.size 1
  let mut pieces := #[]
  for r in [0:rounds + 1] do
    let (ps, bends) := roundedPieces pts cut
    pieces := ps
    let ok := piecesFit ps zones
    if ok.all id then break
    for i in [0:ok.size] do
      let bend := bends.getD i 0
      if !ok.getD i true && bend > 0 then
        cut := cut.modify bend (· * (if r + 1 ≥ rounds then 0 else 0.5))
  return pieces

/-- The pieces with the last one ending `cut` earlier, on the line it arrives along, and the
direction it arrives in (the zero vector for no pieces): the room and direction of an arrowhead
whose tip is the old end. -/
def shortenEnd (pieces : Array Piece) (cut : Float) : Array Piece × Point :=
  match pieces.back? with
  | none => (pieces, ⟨0, 0⟩)
  | some (a, b, c, d) =>
    let dir := if (d - c).norm > 1e-6 then unit (d - c) else unit (d - a)
    let len := (d - a).norm
    let cut := min cut (len / 2)
    let e := d - cut * dir
    -- the handle keeps its direction and loses what the curve lost, but for a pixel, so that
    -- the curve still ends along `dir`
    let h := max (min 1 (len / 4)) ((d - c).norm - cut)
    (pieces.pop.push (a, b, e - h * dir, e), dir)

/-- The pieces with the first one starting `cut` later, on the line it leaves along, and the
direction it arrives in when followed backwards: `shortenEnd` for an arrowhead at the start. -/
def shortenStart (pieces : Array Piece) (cut : Float) : Array Piece × Point :=
  let (r, dir) := shortenEnd (reversePieces pieces) cut
  (reversePieces r, dir)

end PILean.Graph
