/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Image.Basic

/-!
# Frame sequences

The input of the animated-image writers (`FrameSeq.toApng`, `FrameSeq.toGif`) and the output of
the readers (`Anim.readApng`, `Anim.readGif`): a list of equally sized RGBA frames with a delay
each, and the pieces both formats share (errors, reader caps, rational delays, bounding boxes of
differences).

## Main definitions

* `FrameSeq`: width, height, frames, delays as `(numerator, denominator)` seconds, loop count.
* `Anim.AnimError`, `Anim.Limits`: why writing or reading failed; the caps of the readers.
* `FrameSeq.validate`, `FrameSeq.rgbaFrames`: the checks the writers make and the frames as
  RGBA samples.
* `Anim.reduceFrac`, `Anim.addFrac`, `Anim.fitFrac`: delays as reduced fractions, added, and
  approximated by fractions that fit 16 bits.
* `Anim.mergeEqual`: equal neighbouring frames merged, their delays added.
* `Anim.Rect`, `Anim.diffRect`, `Anim.cropBytes`: the bounding box of what changed between two
  frames and the samples inside a box.

## Implementation notes

All indexing goes through total accessors (`Png.byteAt`, `Png.setByte`), so no function here can
panic, whatever the sizes of the data it is given.
-/

namespace PILean

namespace Anim

/-- Why writing or reading an animated image failed. -/
inductive AnimError where
  /-- The writer was given an invalid frame sequence. -/
  | invalidInput (msg : String)
  /-- The data being read is malformed. -/
  | malformed (msg : String)
  /-- The data being read is larger than the caller's `Limits`. -/
  | tooLarge (msg : String)
  /-- The data ends before the format says it should. -/
  | truncated
  /-- A feature the codec does not provide. -/
  | unsupported (msg : String)
deriving Repr, BEq, Inhabited

/-- A short description of the error. -/
def AnimError.toString : AnimError → String
  | .invalidInput m => s!"invalid input: {m}"
  | .malformed m => s!"malformed data: {m}"
  | .tooLarge m => s!"too large: {m}"
  | .truncated => "data is truncated"
  | .unsupported m => s!"unsupported: {m}"

instance : ToString AnimError := ⟨AnimError.toString⟩

/-- The caps the readers apply to untrusted input before they allocate. -/
structure Limits where
  /-- The largest accepted `width * height` of the canvas. -/
  maxPixels : Nat := 1 <<< 24
  /-- The largest accepted number of frames. -/
  maxFrames : Nat := 65535
  /-- The largest accepted size, in bytes, of all composed frames together (4 bytes per pixel
  and frame) and of any decompressed data. -/
  maxBytes : Nat := 1 <<< 28
deriving Repr, Inhabited

/-! ### Rational delays -/

/-- The fraction `n / d` in lowest terms (unchanged if both are zero). -/
def reduceFrac (n d : Nat) : Nat × Nat :=
  let g := Nat.gcd n d
  if g == 0 then (n, d) else (n / g, d / g)

/-- The sum of two fractions, in lowest terms. -/
def addFrac (a b : Nat × Nat) : Nat × Nat := reduceFrac (a.1 * b.2 + b.1 * a.2) (a.2 * b.2)

/-- Whether `p / q` is strictly closer to `n / d` than `p' / q'` is (all denominators
positive). -/
def closerFrac (n d p q p' q' : Nat) : Bool :=
  let e1 := (Int.natAbs ((p : Int) * d - (n : Int) * q))
  let e2 := (Int.natAbs ((p' : Int) * d - (n : Int) * q'))
  e1 * q' < e2 * q

/-- The fraction `n / d` in lowest terms if numerator and denominator are at most `bound`,
otherwise the closest fraction among the continued-fraction convergents and the last
semiconvergent that fit (a value above `bound` becomes `bound / 1`). `d` must be positive. -/
def fitFrac (n d : Nat) (bound : Nat := 65535) : Nat × Nat :=
  let (n, d) := reduceFrac n d
  if n ≤ bound && d ≤ bound then (n, d)
  else if n > bound * d then (bound, 1)
  else Id.run do
    let mut x := n
    let mut y := d
    let mut (h1, k1, h2, k2) := (1, 0, 0, 1)
    let mut best := (0, 1)
    for _ in [0:2 * (n.log2 + d.log2) + 4] do
      if y == 0 then break
      let a := x / y
      let h := a * h1 + h2
      let k := a * k1 + k2
      if h > bound || k > bound then
        let tH := if h1 == 0 then a else (bound - h2) / h1
        let tK := if k1 == 0 then a else (bound - k2) / k1
        let t := min a (min tH tK)
        let semi := (t * h1 + h2, t * k1 + k2)
        if t ≥ 1 && semi.2 ≥ 1 && closerFrac n d semi.1 semi.2 h1 k1 then best := semi
        else best := (h1, k1)
        break
      best := (h, k)
      (h2, k2) := (h1, k1)
      (h1, k1) := (h, k)
      (x, y) := (y, x % y)
    return if best.2 == 0 then (bound, 1) else best

end Anim

/-! ### Frame sequences -/

/-- A sequence of frames to encode: all frames are `width × height` RGBA images (other modes are
converted); frame `i` is shown for `delays[i] = (num, den)` seconds; `loops = 0` repeats forever,
else the number of plays. -/
structure FrameSeq where
  /-- The width of every frame in pixels. -/
  width : Nat
  /-- The height of every frame in pixels. -/
  height : Nat
  /-- The frames. -/
  frames : Array Image
  /-- The time each frame is shown, as `(numerator, denominator)` seconds. -/
  delays : Array (Nat × Nat)
  /-- The number of plays; 0 repeats forever. -/
  loops : Nat := 0

namespace Image

/-- The samples of an image as RGBA bytes: grey becomes `(g, g, g, 255)`, RGB gets alpha 255.
An image whose sample count does not match its size gives none. -/
def toRgbaData (im : Image) : Option ByteArray :=
  if im.data.size != im.width * im.height * im.mode.channels then none
  else
    match im.mode with
    | .rgba => some im.data
    | .rgb => some (Id.run do
        let mut out := ByteArray.emptyWithCapacity (im.width * im.height * 4)
        for i in [0:im.width * im.height] do
          out := out.push (Png.byteAt im.data (3 * i))
          out := out.push (Png.byteAt im.data (3 * i + 1))
          out := out.push (Png.byteAt im.data (3 * i + 2))
          out := out.push 255
        return out)
    | .l => some (Id.run do
        let mut out := ByteArray.emptyWithCapacity (im.width * im.height * 4)
        for i in [0:im.width * im.height] do
          let g := Png.byteAt im.data i
          out := ((out.push g).push g).push g |>.push 255
        return out)

end Image

namespace FrameSeq

/-- Checks a sequence: at least one and at most 65535 frames, sides from 1 to 65535, every frame
of the stated size with a sample count that matches its mode, one delay per frame, and every
delay denominator positive. -/
def validate (s : FrameSeq) : Except Anim.AnimError Unit := do
  if s.width == 0 || s.height == 0 then throw (.invalidInput "zero width or height")
  if s.width > 65535 || s.height > 65535 then throw (.invalidInput "a side exceeds 65535")
  if s.frames.isEmpty then throw (.invalidInput "no frames")
  if s.frames.size > 65535 then throw (.invalidInput "more than 65535 frames")
  if s.delays.size != s.frames.size then throw (.invalidInput "delays and frames differ in number")
  if s.delays.any (·.2 == 0) then throw (.invalidInput "a delay has denominator 0")
  if s.loops ≥ 2 ^ 32 then throw (.invalidInput "loop count exceeds 2^32 - 1")
  for im in s.frames do
    if im.width != s.width || im.height != s.height then
      throw (.invalidInput "a frame differs in size from the sequence")
    if (im.toRgbaData).isNone then
      throw (.invalidInput "a frame's sample count does not match its size and mode")

/-- The frames as RGBA samples, after `validate`. -/
def rgbaFrames (s : FrameSeq) : Except Anim.AnimError (Array ByteArray) := do
  s.validate
  let mut out := #[]
  for im in s.frames do
    match im.toRgbaData with
    | some d => out := out.push d
    | none => throw (.invalidInput "a frame's sample count does not match its size and mode")
  return out

end FrameSeq

namespace Anim

/-- A rectangle of pixels: left, top, width and height. -/
structure Rect where
  /-- Left edge. -/
  x : Nat
  /-- Top edge. -/
  y : Nat
  /-- Width. -/
  w : Nat
  /-- Height. -/
  h : Nat
deriving Repr, BEq, Inhabited

/-- The smallest rectangle containing both. -/
def Rect.union (a b : Rect) : Rect :=
  let x0 := min a.x b.x
  let y0 := min a.y b.y
  { x := x0, y := y0, w := max (a.x + a.w) (b.x + b.w) - x0,
    h := max (a.y + a.h) (b.y + b.h) - y0 }

/-- Whether pixel `i` (of `bpp` bytes) is the same in both arrays. -/
def samePixel (a b : ByteArray) (bpp i : Nat) : Bool := Id.run do
  for k in [0:bpp] do
    if Png.byteAt a (i * bpp + k) != Png.byteAt b (i * bpp + k) then return false
  return true

/-- The bounding box of the pixels (of `bpp` bytes, `w × h`) at which `a` and `b` differ, or
none if they agree everywhere. -/
def diffRect (a b : ByteArray) (w h bpp : Nat) : Option Rect := Id.run do
  let mut x0 := w
  let mut x1 := 0
  let mut y0 := h
  let mut y1 := 0
  for y in [0:h] do
    for x in [0:w] do
      if !samePixel a b bpp (y * w + x) then
        x0 := min x0 x
        x1 := max x1 (x + 1)
        y0 := min y0 y
        y1 := y + 1
  if y1 == 0 then return none
  return some { x := x0, y := y0, w := x1 - x0, h := y1 - y0 }

/-- The samples inside `r` of an image `w` pixels wide with `bpp` bytes per pixel, row by row. -/
def cropBytes (a : ByteArray) (w bpp : Nat) (r : Rect) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (r.w * r.h * bpp)
  for y in [r.y:r.y + r.h] do
    out := out ++ a.extract ((y * w + r.x) * bpp) ((y * w + r.x + r.w) * bpp)
  return out

/-- The frames with equal neighbours merged (their delays added). -/
def mergeEqual (frames : Array ByteArray) (delays : Array (Nat × Nat)) :
    Array ByteArray × Array (Nat × Nat) := Id.run do
  let mut fs : Array ByteArray := #[]
  let mut ds : Array (Nat × Nat) := #[]
  for (f, d) in frames.zip delays do
    match fs.back?, ds.back? with
    | some last, some dl =>
      if last == f then ds := ds.pop.push (addFrac dl d)
      else
        fs := fs.push f
        ds := ds.push d
    | _, _ =>
      fs := fs.push f
      ds := ds.push d
  return (fs, ds)

end Anim

end PILean
