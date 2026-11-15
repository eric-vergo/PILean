/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean

/-!
# Blur and shadow checks

Named checks of `PILean.Raster.Blur`: the exponential against the library's, the kernel's
weights (their sum, symmetry and variance), the blur of a constant layer (exactly constant), of a
point (symmetric, its total kept), of a straight edge against the closed form of a Gaussian's
cumulative distribution, determinism (the same bytes twice, and a recorded SHA-256), the caps, the
drop shadow, the rounded rectangle's area, and alpha compositing.
-/

namespace PILeanTest.Blur

open PILean PILean.Raster

/-- Whether `a` and `b` differ by at most `tol`. -/
def close (a b tol : Float) : Bool := (a - b).abs ≤ tol

/-- A `w × h` mask whose pixel `(x, y)` is `f x y`. -/
def maskOf (w h : Nat) (f : Nat → Nat → Nat) : Mask :=
  ⟨w, h, ⟨Array.ofFn (n := w * h) fun i => (f (i.val % w) (i.val / w)).toUInt8⟩⟩

/-- The kernel of `sigma`, empty when refused. -/
def kernel (sigma : Float) : Array Nat := (gaussianKernel sigma).getD #[]

/-- The variance of a kernel, in pixels squared. -/
def variance (k : Array Nat) : Float :=
  let r := (k.size / 2).toFloat
  (Array.range k.size).foldl (init := 0) fun acc i =>
    let d := i.toFloat - r
    acc + (k[i]!).toFloat * d * d / kernelTotal.toFloat

/-- The standard normal distribution's cumulative distribution at `t`, by Simpson's rule on
`[-10, t]` with 4000 steps (accurate to far better than `10 ^ -6`). -/
def normalCdf (t : Float) : Float := Id.run do
  let a : Float := -10
  if t ≤ a then return 0
  let n := 4000
  let h := (t - a) / n.toFloat
  let f := fun (x : Float) => Float.exp (-(x * x) / 2) / Float.sqrt (2 * 3.141592653589793)
  let mut s := f a + f t
  for i in [1:n] do
    s := s + (if i % 2 == 1 then 4 else 2) * f (a + i.toFloat * h)
  return s * h / 3

/-- The exponential and the kernel. -/
def kernelChecks : Array (String × Bool) :=
  let xs : Array Float := #[-0.001, -0.5, -1, -2.5, -10, -50, -300, -700]
  let sigmas : Array Float := #[0.5, 1, 2.5, 18, 100]
  #[("blur: expNeg agrees with exp to 1e-12 relative on [-700, 0]",
      xs.all fun x => (expNeg x - Float.exp x).abs ≤ 1e-12 * Float.exp x),
    ("blur: expNeg is 1 at 0 and 0 far below", expNeg 0 == 1 && expNeg (-800) == 0),
    ("blur: every kernel's weights add up to exactly 2^16",
      sigmas.all fun s => (kernel s).foldl (· + ·) 0 == kernelTotal),
    ("blur: every kernel is symmetric and reaches ceil(3 sigma)",
      sigmas.all fun s =>
        let k := kernel s
        k.size == 2 * (3 * s).ceil.toUInt64.toNat + 1 && k == k.reverse),
    ("blur: a kernel's variance is the truncated Gaussian's within 2 % (sigma ≥ 1)",
      #[1.0, 2.5, 18].all fun s =>
        let k := kernel s
        let t := ((k.size / 2).toFloat + 0.5) / s
        let phi := Float.exp (-(t * t) / 2) / Float.sqrt (2 * 3.141592653589793)
        let want := s * s * (1 - 2 * t * phi / (2 * normalCdf t - 1))
        close (variance k) want (0.02 * want)),
    ("blur: a tiny sigma is the identity and a huge one is refused",
      kernel 0.01 == #[kernelTotal] && (gaussianKernel 300).isNone &&
        (gaussianKernel (0 / 0)).isNone)]

/-- The blur of a constant layer, a point and an edge. -/
def blurChecks : Array (String × Bool) :=
  let flat := maskOf 64 64 fun _ _ => 200
  let flatB := (flat.blur 3).getD flat
  -- far enough from the edges (r = 9) the layer stays exactly 200
  let flatInside := (List.range 40).all fun i =>
    (List.range 40).all fun j => flatB.get (12 + i) (12 + j) == 200
  let point := maskOf 41 41 fun x y => if x == 20 && y == 20 then 255 else 0
  let pointB := (point.blur 2).getD point
  let total := (List.range 41).foldl (init := 0) fun acc y =>
    (List.range 41).foldl (init := acc) fun acc x => acc + pointB.get x y
  let symmetric := (List.range 41).all fun y => (List.range 41).all fun x =>
    pointB.get x y == pointB.get (40 - x) y && pointB.get x y == pointB.get y x
  -- a straight edge: columns 0..31 covered; the blur of column x is 255 Φ((31.5 - x) / σ)
  let sigma : Float := 3
  let edge := maskOf 64 40 fun x _ => if x < 32 then 255 else 0
  let edgeB := (edge.blur sigma).getD edge
  let edgeOk := (List.range 30).all fun i =>
    let x := 17 + i
    let want := 255 * normalCdf ((31.5 - x.toFloat) / sigma)
    close (edgeB.get x 20).toFloat want 1.0
  #[("blur: a constant layer stays exactly constant away from the edges", flatInside),
    ("blur: a point spreads symmetrically", symmetric),
    -- each of the (2 r + 1)² = 169 pixels it reaches rounds by at most a half
    ("blur: a point's total coverage is kept within rounding", total + 85 ≥ 255 && total ≤ 340),
    ("blur: a straight edge follows the Gaussian's cumulative distribution within 1/255", edgeOk),
    ("blur: an empty mask stays empty", ((maskOf 8 8 fun _ _ => 0).blur 4).map (·.data.data) ==
      some (maskOf 8 8 fun _ _ => 0).data.data)]

/-- A disc blurred, the determinism fixture. -/
def discBlur : Option Mask :=
  (Mask.ofPath (Path.ellipse ⟨40, 30⟩ 18 12) 80 60).bind (·.blur 5.5)

/-- The SHA-256 of `discBlur`'s samples, recorded: a change to the kernel or the passes shows
here. -/
def discBlurSha : String :=
  "19fcd0703f511b94474da42e44d96f89e40829936472c804c4463544d7f1d656"

/-- Determinism, caps, shadows, rounded rectangles and compositing. -/
def otherChecks : Array (String × Bool) :=
  let big : Mask := ⟨5000, 5000, .empty⟩
  let shadowed := (Draw.new 60 60 ⟨0, 0, 0, 0⟩).dropShadow (Path.rect 20 20 10 10) 6 4 2
    ⟨0, 0, 0, 255⟩
  let im := shadowed.toImage
  -- the shadow's darkest pixel sits under the moved square's centre
  let at_ := fun (x y : Nat) => (im.getpixel x y).a
  let none_ := (Draw.new 20 20).dropShadow {} 3 3 2 ⟨0, 0, 0, 255⟩
  let rr := (coverage ((Path.roundedRect 4 6 40 30 8).flatten 0.01 |>.map (·.points)) .nonZero
    64 64 ⟨0, 0, 64, 64⟩).getD #[]
  let rrArea := rr.foldl (fun n s => n + s.len * s.alpha.toNat) 0
  let want := (40 * 30 - (4 - 3.141592653589793) * 64) * 255
  let red : Rgba := ⟨255, 0, 0, 255⟩
  let blue : Rgba := ⟨0, 0, 255, 255⟩
  let comp := Image.alphaComposite (Image.new .rgba 2 1 blue) (Image.new .rgba 1 1
    ⟨255, 0, 0, 128⟩) 1 0
  #[("blur: the same mask blurs to the same bytes twice",
      discBlur.map (·.data.data) == discBlur.map (·.data.data)),
    ("blur: a blurred disc has its recorded SHA-256",
      (discBlur.map fun m => Sha256.hex (Sha256.hash m.data)) == some discBlurSha),
    ("blur: a mask over the size cap is refused", (big.blur 1).isNone),
    ("shadow: the darkest point is under the moved shape's centre",
      at_ 31 29 ≥ at_ 25 25 && at_ 31 29 > 200 && at_ 5 5 == 0),
    ("shadow: an empty path changes nothing",
      none_.toImage.data.data == (Draw.new 20 20).toImage.data.data),
    ("rounded rectangle: its area is w h - (4 - π) r²",
      (rrArea.toFloat - want).abs ≤ 0.002 * want),
    ("compositing: opaque over anything is itself, half over blue is the mix",
      Image.overRgba red blue == red && Image.overRgba ⟨0, 0, 0, 0⟩ blue == blue &&
        comp.getpixel 0 0 == blue && comp.getpixel 1 0 == ⟨128, 0, 127, 255⟩)]

/-- Every check of this module. -/
def checks : Array (String × Bool) := kernelChecks ++ blurChecks ++ otherChecks

end PILeanTest.Blur
