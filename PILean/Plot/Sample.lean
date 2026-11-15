/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Geometry

/-!
# Sampling functions for plots

A function's graph is drawn from samples chosen for the picture: dense where the curve bends,
sparse where it is straight, and broken where it is not continuous.

* The interval starts as 64 equal pieces. A piece is halved while its midpoint is more than a
  tolerance (a quarter of a pixel) off the chord, or the piece is wider than 8 pixels, down to a
  depth of 14 halvings, within a budget of points. Values more than the plot's height beyond the
  range it shows are treated as at that distance, so that nothing is refined out of sight.
* A sample whose value is not finite breaks the curve; the edge of the region where the function
  is defined is found by halving (so `√x` reaches its end and `1/x` stops at its pole).
* A piece halved to the full depth whose ends still lie more than two pixels apart is a jump:
  the curve is broken there instead of drawn across it (the vertical line through a pole of
  `tan x` is not drawn, nor the risers of `⌊x⌋`). When the budget stops the halving first, only
  ends more than the plot's height apart count as a jump.

Work is bounded: at most `maxPoints` evaluations of the function.

## Main definitions

* `sampleFunction`.
-/

namespace PILean.Plot

/-- One piece of the interval: its ends, their values and its depth. -/
private structure Piece where
  a : Float
  fa : Float
  b : Float
  fb : Float
  depth : Nat

/-- Whether a value is finite. -/
def finite (v : Float) : Bool := !(v.isNaN || v.isInf)

/-- The graph of `f` on `[x0, x1]` as polylines in data coordinates, for a plot where a unit of
`x` is `sx` pixels, a unit of `y` is `sy` pixels, the plot is `height` pixels high and shows the
values from `ylo` to `yhi` (see the module docstring). -/
def sampleFunction (f : Float → Float) (x0 x1 : Float) (sx sy height : Float)
    (ylo yhi : Float) (maxPoints : Nat := 6000) (tol : Float := 0.25) : Array (Array Point) :=
  Id.run do
  if !(finite x0 && finite x1) || x1 ≤ x0 then return #[]
  -- values beyond the visible range by more than its height count as at that distance, so that
  -- the curve is not refined where it cannot be seen
  let span := (yhi - ylo).abs
  let cy := fun (v : Float) => max (min ylo yhi - span) (min (max ylo yhi + span) v)
  let n := 64
  let maxDepth := 14
  let xs := (List.range (n + 1)).toArray.map fun i => x0 + (x1 - x0) * i.toFloat / n.toFloat
  let mut out : Array (Array Point) := #[]
  let mut cur : Array Point := #[]
  let mut evals := n + 1
  let fx := xs.map f
  let push := fun (cur : Array Point) (p : Point) =>
    if finite p.y then cur.push p else cur
  if let some v := fx[0]? then cur := push cur ⟨x0, v⟩
  for i in [0:n] do
    let a := xs[i]?.getD x0
    let b := xs[i + 1]?.getD x1
    let fa := fx[i]?.getD 0
    let fb := fx[i + 1]?.getD 0
    -- pieces to process, the leftmost last
    let mut stack : Array Piece := #[⟨a, fa, b, fb, 0⟩]
    for _ in [0:4 * maxPoints] do
      let some pc := stack.back? | break
      stack := stack.pop
      let canSplit := pc.depth < maxDepth && evals < maxPoints
      let m := (pc.a + pc.b) / 2
      if !canSplit then
        -- emit the right end, breaking the curve at a jump or an undefined end
        -- at full depth a continuous function moves by far less than a pixel; when the budget
        -- stopped the halving, only a move across the whole plot counts as a jump
        let limit := if pc.depth ≥ maxDepth then 2 else height
        let jump := finite pc.fa && finite pc.fb && (cy pc.fb - cy pc.fa).abs * sy > limit
        if jump || !finite pc.fb then
          if cur.size > 1 then out := out.push cur
          cur := #[]
        cur := push cur ⟨pc.b, pc.fb⟩
        continue
      let fm := f m
      evals := evals + 1
      let bothFinite := finite pc.fa && finite pc.fb
      let needSplit :=
        if !bothFinite then finite pc.fa || finite pc.fb || finite fm
        else if !finite fm then true
        else
          let off := (cy fm - (cy pc.fa + cy pc.fb) / 2).abs * sy
          off > tol || (pc.b - pc.a) * sx > 8 ||
            ((cy pc.fb - cy pc.fa).abs * sy > height)
      if needSplit then
        stack := stack.push ⟨m, fm, pc.b, pc.fb, pc.depth + 1⟩
        stack := stack.push ⟨pc.a, pc.fa, m, fm, pc.depth + 1⟩
      else
        if !finite pc.fb then
          if cur.size > 1 then out := out.push cur
          cur := #[]
        else cur := push cur ⟨pc.b, pc.fb⟩
  if cur.size > 1 then out := out.push cur
  return out

end PILean.Plot
