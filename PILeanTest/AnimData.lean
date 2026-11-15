/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean

/-!
# Test data of the animated-image codecs

Synthetic frame sequences (all colours exact, alpha 0 or 255), pseudo-random data, and builders
of small APNG and GIF files written by hand, so that the readers are checked on files the
writers do not produce.
-/

namespace PILeanTest.AnimData

open PILean PILean.Anim

/-- Whether a result is a value. -/
def isOk {α ε : Type} (r : Except ε α) : Bool := match r with | .ok _ => true | .error _ => false

/-- One step of a linear congruential generator. -/
def lcg (s : UInt32) : UInt32 := s * 1664525 + 1013904223

/-- `n` pseudo-random indices below `2 ^ bits`. -/
def noiseIndices (seed : UInt32) (n bits : Nat) : ByteArray := Id.run do
  let mut s := seed
  let mut b := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    s := lcg s
    b := b.push ((s >>> 16).toUInt8 &&& ((1 <<< bits) - 1).toUInt8)
  return b

/-- Indices with long runs and some noise, below `2 ^ bits`. -/
def runIndices (seed : UInt32) (n bits : Nat) : ByteArray := Id.run do
  let mut s := seed
  let mut b := ByteArray.emptyWithCapacity n
  for i in [0:n] do
    s := lcg s
    let noisy := s >>> 28 == 0
    b := b.push ((if noisy then (s >>> 8).toUInt8 else (i / 37 % 5).toUInt8) &&&
      ((1 <<< bits) - 1).toUInt8)
  return b

/-- The white opaque colour. -/
def white : Rgba := ⟨255, 255, 255, 255⟩

/-- A `w × h` image of one colour with a `size × size` square of another at `(x, y)`. -/
def square (w h x y size : Nat) (bg fg : Rgba) : Image := Id.run do
  let mut im := Image.new .rgba w h bg
  for dy in [0:size] do
    for dx in [0:size] do
      im := im.putpixel (x + dx) (y + dy) fg
  return im

/-- A sequence with the same delay after every frame. -/
def seqOf (frames : Array Image) (delay : Nat × Nat) (loops : Nat := 0) : FrameSeq :=
  { width := (frames.getD 0 (Image.new .rgba 1 1)).width,
    height := (frames.getD 0 (Image.new .rgba 1 1)).height, frames,
    delays := Array.replicate frames.size delay, loops }

/-- A red square moving over white. -/
def movingSquare : FrameSeq :=
  seqOf ((Array.range 12).map fun k => square 48 32 (4 * k) (6 + k) 8 white ⟨200, 0, 0, 255⟩)
    (1, 10)

/-- A blue bar that grows to the right. -/
def growingBar : FrameSeq :=
  seqOf ((Array.range 10).map fun k => Id.run do
    let mut im := Image.new .rgba 40 16 white
    for x in [0:3 * (k + 1)] do
      for y in [4:12] do im := im.putpixel x y ⟨0, 0, 255, 255⟩
    return im) (1, 20) (loops := 3)

/-- Frames that repeat: `A A B B A`, with different delays. -/
def identicalFrames : FrameSeq :=
  let a := square 20 20 2 2 6 white ⟨0, 0, 0, 255⟩
  let b := square 20 20 9 9 6 white ⟨0, 128, 0, 255⟩
  { width := 20, height := 20, frames := #[a, a, b, b, a],
    delays := #[(1, 10), (1, 20), (1, 4), (3, 100), (1, 50)], loops := 2 }

/-- A single frame. -/
def singleFrame : FrameSeq :=
  { width := 17, height := 9, frames := #[square 17 9 3 2 4 white ⟨9, 9, 200, 255⟩],
    delays := #[(7, 10)] }

/-- Opaque shapes on a transparent background: a square that moves and then vanishes for a frame
and returns, so that opaque pixels become transparent. -/
def transparentFrames : FrameSeq :=
  let clear : Rgba := ⟨0, 0, 0, 0⟩
  let g : Rgba := ⟨30, 160, 60, 255⟩
  seqOf ((Array.range 10).map fun k =>
    if k == 5 then Image.new .rgba 32 32 clear else square 32 32 (2 * k) (3 * k) 6 clear g)
    (1, 10)

/-- Every sequence the round-trip checks use, with a name. -/
def sequences : Array (String × FrameSeq) :=
  #[("moving square", movingSquare), ("growing bar", growingBar),
    ("identical frames", identicalFrames), ("single frame", singleFrame),
    ("transparent frames", transparentFrames)]

/-- A patterned `w × h` background of seven greys. -/
def pattern (w h : Nat) : Image := Id.run do
  let mut im := Image.new .rgba w h white
  for y in [0:h] do
    for x in [0:w] do
      let g := (200 + ((x * 3 + y * 5 + x * y) % 7) * 8).toUInt8
      im := im.putpixel x y ⟨g, g, g, 255⟩
  return im

/-- A black dot of 5 pixels moving over a patterned 160 × 120 canvas, 60 frames. -/
def dotSequence : FrameSeq :=
  let bg := pattern 160 120
  seqOf ((Array.range 60).map fun k => Id.run do
    let mut im := bg
    for dy in [0:5] do
      for dx in [0:5] do im := im.putpixel (2 * k + dx) (20 + k + dy) ⟨0, 0, 0, 255⟩
    return im) (1, 25)

/-- A smooth image with more than 256 colours. -/
def gradient (w h : Nat) : Image := Id.run do
  let mut im := Image.new .rgba w h white
  for y in [0:h] do
    for x in [0:w] do
      im := im.putpixel x y ⟨(x * 255 / (w - 1)).toUInt8, (y * 255 / (h - 1)).toUInt8,
        ((x + y) * 255 / (w + h - 2)).toUInt8, 255⟩
  return im

/-- One frame of a hand-built APNG: rectangle, RGBA samples, disposal, blend, delay `n/d`. -/
structure ApngFrame where
  /-- Left edge. -/
  x : Nat
  /-- Top edge. -/
  y : Nat
  /-- Width. -/
  w : Nat
  /-- Height. -/
  h : Nat
  /-- The RGBA samples. -/
  pix : ByteArray
  /-- `dispose_op`. -/
  dispose : UInt8 := 0
  /-- `blend_op`. -/
  blend : UInt8 := 0
  /-- Delay numerator. -/
  num : Nat := 1
  /-- Delay denominator. -/
  den : Nat := 10

/-- `w × h` RGBA samples of one colour. -/
def solid (w h : Nat) (c : Rgba) : ByteArray := Id.run do
  let mut b := ByteArray.empty
  for _ in [0:w * h] do b := (((b.push c.r).push c.g).push c.b).push c.a
  return b

/-- An APNG of canvas `w × h` from hand-written frames; the first frame is the default image. -/
def buildApng (w h : Nat) (fs : Array ApngFrame) : ByteArray := Id.run do
  let ihdr := Png.be32 w.toUInt32 ++ Png.be32 h.toUInt32 ++ ⟨#[8, 6, 0, 0, 0]⟩
  let mut out := Png.pngSignature ++ Png.chunk "IHDR" ihdr ++
    Png.chunk "acTL" (Png.be32 fs.size.toUInt32 ++ Png.be32 0)
  let mut seq := 0
  for i in [0:fs.size] do
    let f := fs.getD i { x := 0, y := 0, w := 1, h := 1, pix := ByteArray.empty }
    let r : Rect := { x := f.x, y := f.y, w := f.w, h := f.h }
    out := out ++ Png.chunk "fcTL" (fcTLData seq r f.num f.den f.dispose f.blend)
    seq := seq + 1
    let raw : Png.RawImage := { width := f.w, height := f.h, mode := .rgba, data := f.pix }
    let z := Png.zlibCompress (Png.filterImage raw (some 0)) 6
    if i == 0 then out := out ++ Png.chunk "IDAT" z
    else
      out := out ++ Png.chunk "fdAT" (Png.be32 seq.toUInt32 ++ z)
      seq := seq + 1
  return out ++ Png.chunk "IEND" ByteArray.empty

/-- One image of a hand-built GIF. -/
structure GifImage where
  /-- Left edge. -/
  x : Nat
  /-- Top edge. -/
  y : Nat
  /-- Width. -/
  w : Nat
  /-- Height. -/
  h : Nat
  /-- The indices, in stored order. -/
  ix : ByteArray
  /-- The disposal method. -/
  disposal : Nat := 0
  /-- The transparent index. -/
  transparent : Option Nat := none
  /-- Whether the rows are stored interlaced. -/
  interlaced : Bool := false

/-- A GIF with a 16-entry global table (entry `i` is grey `16 i`) from hand-written images, with
an optional comment extension before the first image. -/
def buildGif (w h : Nat) (imgs : Array GifImage) (comment : Bool := true) : ByteArray := Id.run do
  let mut out := "GIF89a".toUTF8 ++ le16 w ++ le16 h ++ ⟨#[0xF3, 0, 0]⟩
  for i in [0:16] do
    out := out ++ ⟨#[(16 * i).toUInt8, (16 * i).toUInt8, (16 * i).toUInt8]⟩
  if comment then out := out ++ ⟨#[0x21, 0xFE]⟩ ++ Lzw.packBlocks "hi".toUTF8
  for im in imgs do
    let flag := (im.disposal <<< 2) ||| (if im.transparent.isSome then 1 else 0)
    out := out ++ ⟨#[0x21, 0xF9, 4, flag.toUInt8]⟩ ++ le16 10 ++
      ⟨#[(im.transparent.getD 0).toUInt8, 0, 0x2C]⟩ ++ le16 im.x ++ le16 im.y ++ le16 im.w ++
      le16 im.h ++ ⟨#[if im.interlaced then 0x40 else 0, 4]⟩ ++
      Lzw.packBlocks (Lzw.encode 4 im.ix)
  return out.push 0x3B

end PILeanTest.AnimData
