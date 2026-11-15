/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Image.Basic

/-!
# Image operations

The Pillow-style operations on `Image`: cropping, pasting (with an optional mask), mode
conversion, flips and quarter turns, and resizing with a choice of filters. Every operation
returns a new image.

## Main definitions

* `Image.generate`: an image from a function of the pixel position and the channel.
* `Image.sample`: one sample, 0 outside the image.
* `Image.crop`, `Image.paste`, `Image.convert`.
* `Image.flipLeftRight`, `Image.flipTopBottom`, `Image.rotate90`, `Image.rotate180`,
  `Image.rotate270`, `Image.transpose`.
* `Filter`, `Image.resize`.

## Implementation notes

* Everything except `resize` is built with `Image.generate`, whose size is right by construction
  (`Image.generate_wellFormed`); a malformed input reads as 0 where samples are missing.
* `crop` and `paste` take `Int` coordinates; `crop` fills outside areas with 0 in every channel
  (transparent black in RGBA, black in L and RGB), as Pillow does.
* A masked `paste` blends every channel (alpha included) as
  `(dst * (255 - m) + src * m + 127) / 255` in integer arithmetic, that is
  `dst + (src - dst) * m / 255` rounded to nearest, ties up. `m = 0` keeps `dst`, `m = 255` takes
  `src`.
* `convert` from RGBA to RGB or L drops the alpha channel without compositing, as Pillow does.
* `resize` is separable: a horizontal and then a vertical pass, each a weighted sum over a kernel
  of integer weights. The output pixel `i` samples the input at `(i + 0.5) * in / out - 0.5`
  (Pillow's pixel-centre convention). `box` weights are exact integers (the overlap lengths of
  the output pixel's footprint with the input pixels), so box resizing uses no `Float`. The
  `bilinear` and `lanczos` weights are computed in `Float` (`sin` is needed for Lanczos), then
  rounded to integers with 16 fractional bits and normalised by their integer sum. The weighted
  sums are exact (integers accumulated in `Float`, see `Image.resize`), and each output sample
  is rounded (half up) and clamped to `0..255` once. The weights are deterministic for a given
  platform's `sin`; they are rounded coarsely enough that platforms agree in practice. A kernel
  is only ever applied to samples inside the image (the weights of missing neighbours are
  dropped and the rest renormalised).
  RGBA is resampled premultiplied: the colour of an output pixel is the alpha-weighted mean of
  the input colours, and its alpha the mean alpha, so fully transparent pixels contribute no
  colour. The work is `O(output samples * kernel support)`; the supports are 1 (`nearest`), the
  scale ratio (`box`), and twice and six times the scale ratio (`bilinear`, `lanczos`), at least
  2 and 6.

## References

* Pillow's documentation of `Image.crop`, `Image.paste`, `Image.convert`, `Image.transpose` and
  `Image.resize` (behaviour only): <https://pillow.readthedocs.io/en/stable/reference/Image.html>
* ITU-R Recommendation BT.601 (luma weights).
* Lanczos resampling and the pixel-centre convention: Wikipedia, "Lanczos resampling";
  K. Turkowski, "Filters for Common Resampling Tasks", Graphics Gems I (1990).
-/

namespace PILean

namespace Image

/-! ### Building images -/

/-- The image of a mode and size whose sample at column `x`, row `y`, channel `k` is `f x y k`. -/
def generate (mode : Mode) (width height : Nat) (f : Nat → Nat → Nat → UInt8) : Image :=
  let c := mode.channels
  { mode, width, height
    data := ⟨Array.ofFn (n := width * height * c) fun i => f ((i / c) % width) ((i / c) / width)
      (i % c)⟩ }

/-- The sample at column `x`, row `y`, channel `k`: 0 outside the image and where the image
lacks the sample. -/
def sample (im : Image) (x y k : Nat) : UInt8 :=
  if x < im.width ∧ y < im.height ∧ k < im.mode.channels then
    if h : (y * im.width + x) * im.mode.channels + k < im.data.size then
      im.data[(y * im.width + x) * im.mode.channels + k] else 0
  else 0

/-- `Image.sample` at integer coordinates: 0 when a coordinate is negative. -/
def sampleInt (im : Image) (x y : Int) (k : Nat) : UInt8 :=
  if 0 ≤ x ∧ 0 ≤ y then im.sample x.toNat y.toNat k else 0

/-! ### Crop, paste, convert -/

/-- The part of the image in the box `[x0, x1) × [y0, y1)` (Pillow's `crop((left, upper,
right, lower))`; right and lower exclusive). The result is `max 0 (x1 - x0)` wide and
`max 0 (y1 - y0)` high; where the box leaves the image the samples are 0 (transparent black in
RGBA, black in L and RGB). -/
def crop (im : Image) (x0 y0 x1 y1 : Int) : Image :=
  generate im.mode (x1 - x0).toNat (y1 - y0).toNat fun x y k =>
    im.sampleInt (x0 + x) (y0 + y) k

/-- The image converted to another mode: RGB to L by ITU-R 601 luma (`Image.samplesOf`), L to
RGB or RGBA by replication (alpha 255), RGB to RGBA with alpha 255, RGBA to RGB or L by
dropping the alpha channel (no compositing over a background, as Pillow does). The same mode
returns the image itself. -/
def convert (im : Image) (mode : Mode) : Image :=
  if im.mode = mode then im
  else generate mode im.width im.height fun x y k =>
    (samplesOf mode (im.getpixel x y)).getD k 0

/-- The mask value of `m` at `(x, y)`: the grey of an `L` mask, the alpha of an `RGBA` mask, the
luma of an `RGB` mask; 0 outside the mask. -/
def maskValue (m : Image) (x y : Nat) : UInt8 :=
  match m.mode with
  | .l => m.sample x y 0
  | .rgba => m.sample x y 3
  | .rgb => (m.convert .l).sample x y 0

/-- The blend `dst + (src - dst) * m / 255` of two samples, in integers, rounded to nearest with
ties up: `(dst * (255 - m) + src * m + 127) / 255`. -/
def blend (dst src m : UInt8) : UInt8 :=
  ((dst.toNat * (255 - m.toNat) + src.toNat * m.toNat + 127) / 255).toUInt8

/-- `dst` with `src` pasted with its top left corner at `(x, y)` (Pillow's `paste`). `src` is
converted to `dst`'s mode. Without a mask the covered pixels are replaced; with a mask (an `L`
image, or the alpha of an `RGBA` image; where it is smaller than `src` it counts as 0) each
channel of a covered pixel becomes `blend`. Parts of `src` outside `dst` are clipped. The result
has `dst`'s mode and size. -/
def paste (dst src : Image) (x y : Int) (mask : Option Image := none) : Image :=
  let s := src.convert dst.mode
  generate dst.mode dst.width dst.height fun px py k =>
    let sx : Int := (px : Int) - x
    let sy : Int := (py : Int) - y
    if 0 ≤ sx ∧ sx < s.width ∧ 0 ≤ sy ∧ sy < s.height then
      let v := s.sample sx.toNat sy.toNat k
      match mask with
      | none => v
      | some m => blend (dst.sample px py k) v (maskValue m sx.toNat sy.toNat)
    else dst.sample px py k

/-! ### Flips and quarter turns -/

/-- The mirror image, left to right. -/
def flipLeftRight (im : Image) : Image :=
  generate im.mode im.width im.height fun x y k => im.sample (im.width - 1 - x) y k

/-- The mirror image, top to bottom. -/
def flipTopBottom (im : Image) : Image :=
  generate im.mode im.width im.height fun x y k => im.sample x (im.height - 1 - y) k

/-- A quarter turn counter-clockwise (Pillow's `ROTATE_90`); the result is `height` wide and
`width` high. -/
def rotate90 (im : Image) : Image :=
  generate im.mode im.height im.width fun x y k => im.sample (im.width - 1 - y) x k

/-- A half turn. -/
def rotate180 (im : Image) : Image :=
  generate im.mode im.width im.height fun x y k =>
    im.sample (im.width - 1 - x) (im.height - 1 - y) k

/-- A quarter turn clockwise (Pillow's `ROTATE_270`); the result is `height` wide and `width`
high. -/
def rotate270 (im : Image) : Image :=
  generate im.mode im.height im.width fun x y k => im.sample y (im.height - 1 - x) k

/-- The reflection in the main diagonal (Pillow's `TRANSPOSE`): the pixel at column `x`, row `y`
moves to column `y`, row `x`; the result is `height` wide and `width` high. It equals
`flipTopBottom (rotate90 im)`. -/
def transpose (im : Image) : Image :=
  generate im.mode im.height im.width fun x y k => im.sample y x k

/-! ### Resizing -/

/-- The resampling filters of `Image.resize`. -/
inductive Filter where
  /-- The nearest input pixel (no smoothing). -/
  | nearest
  /-- Linear interpolation (a triangle kernel, widened when downscaling). -/
  | bilinear
  /-- Area averaging: the area-weighted mean of the input pixels under the output pixel;
  exact for integer ratios; the recommended filter for downscaling. -/
  | box
  /-- Lanczos with `a = 3` (a windowed sinc, widened when downscaling). -/
  | lanczos
deriving BEq, Repr, Inhabited, DecidableEq

namespace Resize

/-- A kernel row: the first input index and the integer weights of the consecutive pixels from
there. -/
abbrev Row := Nat × Array Int

/-- The row selecting the nearest input pixel for output pixel `i`. -/
def nearestRow (nIn nOut i : Nat) : Row :=
  if nIn = 0 then (0, #[]) else (min (nIn - 1) (((2 * i + 1) * nIn) / (2 * nOut)), #[1])

/-- The exact box row of output pixel `i`: the overlaps, in units of `1 / nOut` input pixels, of
the footprint `[i * nIn, (i + 1) * nIn)` with the input pixels `[j * nOut, (j + 1) * nOut)`. -/
def boxRow (nIn nOut i : Nat) : Row := Id.run do
  let lo := (i * nIn) / nOut
  let hi := min nIn (((i + 1) * nIn + nOut - 1) / nOut)
  let mut ws : Array Int := #[]
  for j in [lo:hi] do
    let a := max (j * nOut) (i * nIn)
    let b := min ((j + 1) * nOut) ((i + 1) * nIn)
    ws := ws.push ((b - a : Nat) : Int)
  return (lo, ws)

/-- The triangle kernel (support 1). -/
def triangle (x : Float) : Float := max 0 (1 - x.abs)

/-- The Lanczos kernel with `a = 3` (support 3). -/
def lanczos3 (x : Float) : Float :=
  if x.abs < 1e-9 then 1
  else if x.abs < 3 then
    let px := 3.141592653589793 * x
    3 * px.sin * (px / 3).sin / (px * px)
  else 0

/-- The row of a `Float` kernel `k` of the given support for output pixel `i`: weights sampled
at the input pixel centres, the kernel stretched by the scale ratio when downscaling,
rounded to integers with 16 fractional bits and normalised by their sum; the nearest pixel if
the sum is not positive. -/
def floatRow (k : Float → Float) (support : Float) (nIn nOut i : Nat) : Row := Id.run do
  let s := nIn.toFloat / nOut.toFloat
  let f := max 1 s
  let center := (i.toFloat + 0.5) * s
  let loF := (center - support * f).floor
  let lo := if loF < 0 then 0 else loF.toUInt64.toNat
  let hi := min nIn ((center + support * f).ceil.toUInt64.toNat)
  let mut ws : Array Float := #[]
  let mut sum : Float := 0
  for j in [lo:hi] do
    let w := k ((j.toFloat + 0.5 - center) / f)
    ws := ws.push w
    sum := sum + w
  if !(sum > 0) then return nearestRow nIn nOut i
  let q := ws.map fun w => (w / sum * 65536).round.toInt64.toInt
  if q.foldl (· + ·) 0 ≤ 0 then return nearestRow nIn nOut i
  return (lo, q)

/-- The kernel rows of every output pixel of an axis of `nIn` input and `nOut` output pixels. -/
def rows (filter : Filter) (nIn nOut : Nat) : Array Row :=
  Array.ofFn (n := nOut) fun i =>
    match filter with
    | .nearest => nearestRow nIn nOut i
    | .box => boxRow nIn nOut i
    | .bilinear => floatRow triangle 1 nIn nOut i
    | .lanczos => floatRow lanczos3 3 nIn nOut i

/-- The sum of the weights of a row. -/
def Row.total (r : Row) : Int := r.2.foldl (· + ·) 0

/-- The weights of a kernel row as `Float`s (integers, so exactly). -/
def Row.toFloats (r : Row) : Nat × Array Float := (r.1, r.2.map Float.ofInt)

/-- A sample of a plane, 0 outside. -/
def planeAt (a : FloatArray) (i : Nat) : Float := if h : i < a.size then a[i] else 0

/-- One horizontal pass over `h` rows of `w` pixels of `c` channels: for each output pixel and
channel the sum of the input samples times the integer weights. The sums are integers below
`2 ^ 53`, so the `Float` additions and products are exact (see `Image.resize`). -/
def passH (src : FloatArray) (w h c : Nat) (ks : Array (Nat × Array Float)) : FloatArray :=
  Id.run do
  let mut out := FloatArray.emptyWithCapacity (ks.size * h * c)
  for y in [0:h] do
    for (st, ws) in ks do
      for ch in [0:c] do
        let mut acc : Float := 0
        let mut j := st
        for wt in ws do
          if wt != 0 then acc := acc + wt * planeAt src ((y * w + j) * c + ch)
          j := j + 1
        out := out.push acc
  return out

/-- One vertical pass over `w` columns of `c` channels; as `passH`. -/
def passV (src : FloatArray) (w c : Nat) (ks : Array (Nat × Array Float)) : FloatArray :=
  Id.run do
  let mut out := FloatArray.emptyWithCapacity (ks.size * w * c)
  for (st, ws) in ks do
    for x in [0:w] do
      for ch in [0:c] do
        let mut acc : Float := 0
        let mut j := st
        for wt in ws do
          if wt != 0 then acc := acc + wt * planeAt src ((j * w + x) * c + ch)
          j := j + 1
        out := out.push acc
  return out

/-- `s / d` rounded to nearest, ties up, for `s ≥ 0` and `d > 0`; 0 otherwise. -/
def roundDiv (s d : Int64) : Int64 := if s > 0 ∧ d > 0 then (2 * s + d) / (2 * d) else 0

/-- A non-negative integer clamped into a byte. -/
def toByte (v : Int64) : UInt8 := (min 255 v).toInt.toNat.toUInt8

/-- A sum of a plane as an integer (exact: the sums are integers). -/
def planeInt (a : FloatArray) (i : Nat) : Int64 := (planeAt a i).toInt64

end Resize

/-- The image resized to `w × h` pixels (Pillow's `resize`), separably: a horizontal pass and a
vertical pass with the kernels of `filter`; output pixel `i` samples input coordinate
`(i + 0.5) * in / out - 0.5`. The default is `.box`, which averages the input area under each
output pixel and is the right choice for shrinking; use `.bilinear` or `.lanczos` for enlarging
smoothly. RGBA is resampled premultiplied and un-premultiplied afterwards, so transparent
pixels contribute no colour. The same size returns the image itself. A zero-sized axis gives
samples 0.

The weights of `box` and `nearest` are integers; those of `bilinear` and `lanczos` come from
`Float` (see the module docstring) and are integers from then on. The weighted sums are
accumulated in `Float`, which is exact here: every term is an integer and every partial sum is
an integer below `2 ^ 53` (a sample is below `2 ^ 16`, the weights of a row sum to at most
about `2 ^ 17` for the float filters and to the input length for `box`, so the bound holds for
any image whose pixel count is below `10 ^ 11`). `Float` is used because it is an unboxed
number in Lean, where integers beyond 31 bits are slow. Everything after the sums is `Int64`
arithmetic, with one rounding (half up) per output sample. -/
def resize (im : Image) (w h : Nat) (filter : Filter := .box) : Image :=
  if w = im.width ∧ h = im.height then im
  else Id.run do
    let c := im.mode.channels
    let n := im.width * im.height
    let at_ := fun (i : Nat) => if hi : i < im.data.size then im.data[i].toUInt64 else 0
    let mut plane := FloatArray.emptyWithCapacity (n * c)
    for p in [0:n] do
      if im.mode = .rgba then
        let a := at_ (p * 4 + 3)
        for k in [0:3] do plane := plane.push (at_ (p * 4 + k) * a).toFloat
        plane := plane.push a.toFloat
      else
        for k in [0:c] do plane := plane.push (at_ (p * c + k)).toFloat
    let kx := Resize.rows filter im.width w
    let ky := Resize.rows filter im.height h
    let tx := kx.map fun r => r.total.toInt64
    let ty := ky.map fun r => r.total.toInt64
    let mid := Resize.passH plane im.width im.height c (kx.map Resize.Row.toFloats)
    let fin := Resize.passV mid w c (ky.map Resize.Row.toFloats)
    let mut data := ByteArray.emptyWithCapacity (w * h * c)
    for y in [0:h] do
      for x in [0:w] do
        let d := tx.getD x 0 * ty.getD y 0
        let base := (y * w + x) * c
        if im.mode = .rgba then
          let sa := Resize.planeInt fin (base + 3)
          for k in [0:3] do
            data := data.push (Resize.toByte (Resize.roundDiv (Resize.planeInt fin (base + k)) sa))
          data := data.push (Resize.toByte (Resize.roundDiv sa d))
        else
          for k in [0:c] do
            data := data.push (Resize.toByte (Resize.roundDiv (Resize.planeInt fin (base + k)) d))
    return { mode := im.mode, width := w, height := h, data }

end Image

end PILean
