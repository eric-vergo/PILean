/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Raster.Draw

/-!
# Gaussian blur and drop shadows

A Gaussian blur of a coverage mask (an alpha layer), and the drop shadow of a shape built from
it: the shape's coverage, moved, blurred and painted in a colour under what is drawn next.

The blur is separable: a horizontal pass and then a vertical pass, each a weighted sum over the
same one-dimensional kernel. The kernel's weights are integers that add up to exactly `2 ^ 16`
(`gaussianKernel`), computed from the Gaussian `exp (-i² / 2σ²)` with the basic floating-point
operations only (`expNeg`), which IEEE 754 rounds the same on every machine; everything after the
weights is integer arithmetic (the sums are integers below `2 ^ 53`, accumulated exactly in
`Float`), with one rounding (half up) after each pass. So a blur is the same on every machine,
and a constant layer stays exactly constant.

Outside the mask the layer counts as transparent (0): a shape near the edge loses the part of
its shadow that would fall outside.

## Bounds

The standard deviation is at most `maxSigma` pixels and the kernel reaches `⌈3σ⌉` pixels each
way; a mask has at most `maxBlurPixels` pixels. Beyond either cap the blur gives `none`. The work
is at most `(2 ⌈3σ⌉ + 1)` multiply-adds a pixel and pass, and only the rows and columns within
the kernel's reach of a covered pixel are visited.

## Main definitions

* `expNeg`: `exp x` for `x ≤ 0`, from the basic operations.
* `gaussianKernel`: the integer weights of a standard deviation.
* `Mask.blur`: a mask blurred.
* `Canvas.fillMask`, `Draw.fillMask`: a paint through a whole-image mask.
* `Draw.dropShadow`: a shape's drop shadow.
-/

namespace PILean.Raster

/-- The largest standard deviation the blur takes, in pixels. -/
def maxSigma : Float := 256

/-- The largest mask the blur takes, in pixels (`4096 × 4096`). -/
def maxBlurPixels : Nat := 16777216

/-- The sum of the weights of a kernel: `2 ^ 16`. -/
def kernelTotal : Nat := 65536

/-- `exp x` for `x ≤ 0` (`0` below `-745`, where the double underflows; `1` for `x ≥ 0` and for
`NaN`), from additions, multiplications and divisions only: the series of `exp (x / 2 ^ 10)` to its
twentieth power, squared ten times. Its relative error is below `10 ^ -12`, and it is the same
on every machine, unlike a library's `exp`. -/
def expNeg (x : Float) : Float := Id.run do
  if !(x < 0) then return 1
  if x < -745 then return 0
  -- 2 ^ 10 halvings keep |y| ≤ 0.73 for x ≥ -745: the series converges in 20 terms
  let y := x / 1024
  let mut term := 1.0
  let mut sum := 1.0
  for k in [1:21] do
    term := term * y / k.toFloat
    sum := sum + term
  for _ in [0:10] do
    sum := sum * sum
  return sum

/-- The weights of a Gaussian of standard deviation `sigma` pixels at offsets `-r` to `r`
(`r = ⌈3σ⌉`), as integers that add up to exactly `kernelTotal`: each weight is the Gaussian's
share rounded to the nearest integer, and the centre takes what the rounding left over. A
standard deviation below `1/32` gives the identity `#[kernelTotal]`; one above `maxSigma`, or not
a number, gives `none`. -/
def gaussianKernel (sigma : Float) : Option (Array Nat) := Id.run do
  if sigma.isNaN || sigma > maxSigma then return none
  if sigma < 1 / 32 then return some #[kernelTotal]
  let r : Nat := (3 * sigma).ceil.toUInt64.toNat
  let g := (Array.range (2 * r + 1)).map fun i =>
    let d := i.toFloat - r.toFloat
    expNeg (-(d * d) / (2 * sigma * sigma))
  let total := g.foldl (· + ·) 0
  let w := g.map fun v => (v / total * kernelTotal.toFloat + 0.5).floor.toUInt64.toNat
  let sideSum := (w.extract 0 r).foldl (· + ·) 0
  -- the two sides are equal (the Gaussian is even), so the centre absorbs the rounding
  if 2 * sideSum ≥ kernelTotal then return some #[kernelTotal]
  return some (w.set! r (kernelTotal - 2 * sideSum))

/-- The byte at `i` of `d` as a `Float` (0 outside). -/
@[inline] private def byteF (d : ByteArray) (i : Nat) : Float :=
  if h : i < d.size then d[i].toNat.toFloat else 0

/-- The 16-bit little-endian value at element `i` of `d` as a `Float` (0 outside). -/
@[inline] private def wordF (d : ByteArray) (i : Nat) : Float :=
  if h : 2 * i + 1 < d.size then (d[2 * i].toNat + 256 * d[2 * i + 1].toNat).toFloat else 0

/-- `v / 2 ^ k` rounded half up, for an integer-valued `v ≥ 0`, as a natural number. -/
@[inline] private def shiftRound (v : Float) (k : Nat) : Nat :=
  (v.toUInt64.toNat + 2 ^ k / 2) / 2 ^ k

/-- The box `[x0, x1) × [y0, y1)` holding every pixel of the mask that is not 0, or `none` when
every pixel is 0. -/
def Mask.inkBox (m : Mask) : Option IRect := Id.run do
  let mut x0 := m.width
  let mut y0 := m.height
  let mut x1 := 0
  let mut y1 := 0
  for y in [0:m.height] do
    for x in [0:m.width] do
      if m.get x y != 0 then
        x0 := min x0 x
        y0 := min y0 y
        x1 := max x1 (x + 1)
        y1 := max y1 (y + 1)
  if x1 == 0 then return none
  return some ⟨x0, y0, x1, y1⟩

/-- The mask blurred by a Gaussian of standard deviation `sigma` pixels (see the module
docstring): each pass sums the kernel's weights times the samples, with the samples outside the
mask taken as 0, and rounds; the result has the mask's size. `none` when `sigma` or the mask is
beyond the caps (`maxSigma`, `maxBlurPixels`); the mask itself when every pixel is 0. -/
def Mask.blur (m : Mask) (sigma : Float) : Option Mask := Id.run do
  if m.width * m.height > maxBlurPixels then return none
  let some k := gaussianKernel sigma | return none
  let some box := m.inkBox | return some m
  let r := k.size / 2
  let ws := FloatArray.mk (k.map (·.toFloat))
  let w := m.width
  let h := m.height
  -- the rows and columns the kernel reaches from a covered pixel
  let (cx0, cx1) := (box.x0 - min box.x0 r, min w (box.x1 + r))
  let (cy0, cy1) := (box.y0 - min box.y0 r, min h (box.y1 + r))
  -- horizontal pass, 16 bits a sample: the sum over the kernel / 2 ^ 8
  let mut mid := Png.filledBytes (2 * w * h)
  for y in [box.y0:box.y1] do
    for x in [cx0:cx1] do
      let mut s : Float := 0
      for j in [0:k.size] do
        let sx : Int := (x : Int) + j - r
        if 0 ≤ sx && sx < w then
          s := s + ws[j]! * byteF m.data (y * w + sx.toNat)
      let v := shiftRound s 8
      let i := 2 * (y * w + x)
      mid := (mid.set! i (v % 256).toUInt8).set! (i + 1) (v / 256).toUInt8
  -- vertical pass back to 8 bits: the sum over the kernel / 2 ^ 24
  let mut out := Png.filledBytes (w * h)
  for y in [cy0:cy1] do
    for x in [cx0:cx1] do
      let mut s : Float := 0
      for j in [0:k.size] do
        let sy : Int := (y : Int) + j - r
        if 0 ≤ sy && sy < h then
          s := s + ws[j]! * wordF mid (sy.toNat * w + x)
      out := out.set! (y * w + x) (min 255 (shiftRound s 24)).toUInt8
  return some { m with data := out }

/-- The mask of a path's fill (non-zero by default) over a `w × h` image, curves flattened to
`tol` pixels; `none` when the rasteriser refuses the path (`coverage`). -/
def Mask.ofPath (p : Path) (w h : Nat) (rule : FillRule := .nonZero) (tol : Float := 0.1) :
    Option Mask :=
  (coverage ((p.flatten tol).map (·.points)) rule w h ⟨0, 0, w, h⟩).map (Mask.ofSpans w h)

/-- The canvas with `paint` composited at every pixel through the whole-image mask `m` (same
size; a pixel outside it counts as 0), at an opacity (0 to 1), and through the clip mask `clip`
if any. -/
def Canvas.fillMask (c : Canvas) (m : Mask) (paint : Paint) (opacity : Float := 1)
    (clip : Option Mask := none) : Canvas := Id.run do
  let op : Nat := ((if opacity.isNaN then 0 else max 0 (min 1 opacity)) * 65535 + 0.5).floor
    |>.toUInt64.toNat
  let solid := match paint with | .solid col => some (Lin.ofRgba col c.space) | _ => none
  let mut d := c.data
  for y in [0:min c.height m.height] do
    for x in [0:min c.width m.width] do
      let a := m.get x y
      if a == 0 then continue
      let cm := match clip with | some cl => cl.get x y | none => 255
      let k := mulDiv (mulDiv a 65535 255) (mulDiv op cm 255) 65535
      if k == 0 then continue
      d := Canvas.blendAt d ((y * c.width + x) * 8) (solid.getD (paint.at x y c.space)) k
  return { c with data := d }

/-- A paint composited through a whole-image mask (`Canvas.fillMask`), within the drawing's clip
rectangle and clip mask. -/
def Draw.fillMask (d : Draw) (m : Mask) (paint : Paint) (opacity : Float := 1) : Draw :=
  let r := d.clip
  let whole := r.x0 == 0 && r.y0 == 0 && r.x1 ≥ m.width && r.y1 ≥ m.height
  let inside : Mask := if whole then m else
    { m with data := Id.run do
        let mut out := m.data
        for y in [0:m.height] do
          for x in [0:m.width] do
            if !(r.x0 ≤ x && x < r.x1 && r.y0 ≤ y && y < r.y1) then
              out := out.set! (y * m.width + x) 0
        return out }
  { d with canvas := d.canvas.fillMask inside paint opacity d.mask }

/-- The drawing with the drop shadow of path `p` painted in `color`: the path's fill coverage
moved by `(dx, dy)` pixels, blurred by a Gaussian of standard deviation `sigma` pixels
(`Mask.blur`), and composited at the colour's alpha. Draw the shape itself afterwards, over its
shadow. The drawing unchanged when the path is refused or the blur is beyond its caps. -/
def Draw.dropShadow (d : Draw) (p : Path) (dx dy sigma : Float) (color : Rgba) : Draw :=
  let w := d.canvas.width
  let h := d.canvas.height
  match (Mask.ofPath (p.transform (Affine.translate dx dy)) w h).bind (·.blur sigma) with
  | some m => d.fillMask m (.solid color)
  | none => d

end PILean.Raster
