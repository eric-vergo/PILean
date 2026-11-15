/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Anim.Frames
import PILean.Anim.Lzw
import PILean.Anim.Quantize

/-!
# The GIF writer

`FrameSeq.toGif` writes an animated GIF89a with one global colour table.

## Main definitions

* `FrameSeq.toGif`: the GIF bytes of a frame sequence, optionally dithered.
* `Anim.gifDelays`: delays in centiseconds, with the cumulative time kept exact.

## Implementation notes

* Colours: `Quant.quantize` over all frames (exact when there are at most 256 colours, else
  median cut); pixels with alpha below 128 are transparent, others opaque.
* Delays: with `T(i)` the start time of frame `i` (the sum of the earlier delays), frame `i` is
  shown for `round(100 * T(i + 1)) - round(100 * T(i))` centiseconds, so the cumulative time
  never drifts. Browsers treat delays below 2 centiseconds as 10, so a delay is at least 2
  (the cumulative rounding then continues from the time actually shown, which can run ahead of
  the exact time by the amount raised), and at most 65535 (the largest the format holds).
* Loops: `loops = 0` writes a `NETSCAPE2.0` extension with count 0 (forever); `loops = n ≥ 2`
  writes count `n - 1` (the count is the number of repeats); `loops = 1` writes no extension.
  The count must fit 16 bits.
* Frame differencing: frames equal to the one before are merged into it (delays added). Every
  later frame covers only the bounding box of the pixels that differ from the canvas it is drawn
  on, with disposal "do not dispose". Inside the box, pixels that equal the canvas may be
  written as the transparent index, which compresses better; the writer encodes both versions
  and keeps the transparent one only if its LZW stream is strictly shorter, so the result is
  never longer. A spare transparent index is added to the colour table for this when the colours
  leave room (a sequence of one frame needs none).
* If a frame makes a pixel transparent that was opaque before, the previous frame is disposed
  to the background ("restore to background", disposal 2) and made to cover every opaque pixel,
  so the canvas is empty when the frame is drawn.
* The first frame covers the whole canvas.

## References

* Graphics Interchange Format, Version 89a (CompuServe, 1990). Written from the specification.
-/

namespace PILean.Anim

/-- The delays in centiseconds for delays given as fractions of seconds; see the module
documentation. -/
def gifDelays (ds : Array (Nat × Nat)) : Array Nat := Id.run do
  let mut t : Nat × Nat := (0, 1)
  let mut shown := 0
  let mut out := #[]
  for d in ds do
    t := addFrac t d
    let target := (200 * t.1 + t.2) / (2 * t.2)
    let c := min 65535 (max 2 (target - shown))
    out := out.push c
    shown := shown + c
  return out

/-- A 16-bit number in little-endian byte order. -/
def le16 (v : Nat) : ByteArray := ⟨#[v.toUInt8, (v >>> 8).toUInt8]⟩

/-- The number of bits of an index into `n` entries, at least 1. -/
def tableBits (n : Nat) : Nat := Id.run do
  let mut b := 1
  for _ in [0:12] do
    if (1 <<< b) < n then b := b + 1
  return b

/-- Whether a pixel is non-transparent in `prev` and transparent (`t`) in `cur`. -/
def hasRemoval (prev cur : ByteArray) (t : Nat) : Bool :=
  cur.size.fold (fun i _ r => r || (Png.byteAt cur i).toNat == t &&
    (Png.byteAt prev i).toNat != t) false

/-- The index bytes of `plain` with every pixel that equals the one of `base` replaced by `t`. -/
def substitute (plain base : ByteArray) (t : UInt8) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity plain.size
  for i in [0:plain.size] do
    let v := Png.byteAt plain i
    out := out.push (if v == Png.byteAt base i then t else v)
  return out

/-- The bytes of a frame: graphic control extension, image descriptor and the LZW code stream
`stream`. -/
def gifFrame (r : Rect) (stream : ByteArray) (minCode cs disposal : Nat)
    (transparent : Option Nat) : ByteArray :=
  let flag := (disposal <<< 2) ||| (if transparent.isSome then 1 else 0)
  ⟨#[0x21, 0xF9, 4, flag.toUInt8]⟩ ++ le16 cs ++
    ⟨#[(transparent.getD 0).toUInt8, 0, 0x2C]⟩ ++ le16 r.x ++ le16 r.y ++ le16 r.w ++ le16 r.h ++
    ⟨#[0, minCode.toUInt8]⟩ ++
    Lzw.packBlocks stream

end Anim

namespace FrameSeq

open Anim in
/-- The GIF89a file for a frame sequence. With `dither`, colours are mapped by Floyd–Steinberg
error diffusion (only matters if there are more than 256 colours). Fails with
`AnimError.invalidInput` if `validate` does or the loop count exceeds 65536. -/
def toGif (s : FrameSeq) (dither : Bool := false) : Except AnimError ByteArray := do
  let rgba ← s.rgbaFrames
  if s.loops > 65536 then throw (.invalidInput "loop count above 65536 in a GIF")
  let pal := Quant.quantize rgba
  let mut cache : Quant.Cache := {}
  let mut idx : Array ByteArray := #[]
  for f in rgba do
    let (ix, c) := Quant.indexFrame pal cache f s.width s.height dither
    cache := c
    idx := idx.push ix
  let (fs, ds) := mergeEqual idx s.delays
  let nColors := pal.colors.size
  let spare := !pal.hasTransparent && fs.size > 1 && nColors ≤ 255
  let tIdx : Option Nat := if pal.hasTransparent || spare then some nColors else none
  let bits := tableBits (nColors + if tIdx.isSome then 1 else 0)
  let minCode := max 2 bits
  let mut out := "GIF89a".toUTF8 ++ le16 s.width ++ le16 s.height ++
    ⟨#[(0x80 ||| ((bits - 1) <<< 4) ||| (bits - 1)).toUInt8, 0, 0]⟩
  for i in [0:1 <<< bits] do
    let c := if i < nColors then pal.colors.getD i 0 else 0
    out := out ++ ⟨#[(c >>> 16).toUInt8, (c >>> 8).toUInt8, c.toUInt8]⟩
  if s.loops != 1 then
    out := out ++ ⟨#[0x21, 0xFF, 11]⟩ ++ "NETSCAPE2.0".toUTF8 ++ ⟨#[3, 1]⟩ ++
      le16 (if s.loops == 0 then 0 else s.loops - 1) ++ ⟨#[0]⟩
  let cs := gifDelays ds
  let t := nColors
  let w := s.width
  let h := s.height
  let allT := Png.filledBytes (w * h) t.toUInt8
  let mut clearThis := false
  for i in [0:fs.size] do
    let cur := fs.getD i ByteArray.empty
    let prev := fs.getD (i - 1) ByteArray.empty
    let clearNext := pal.hasTransparent && i + 1 < fs.size &&
      hasRemoval cur (fs.getD (i + 1) ByteArray.empty) t
    let disposal := if clearNext then 2 else 1
    let c := cs.getD i 2
    if i == 0 then
      out := out ++ gifFrame { x := 0, y := 0, w, h } (Lzw.encode minCode cur) minCode c disposal
        (if pal.hasTransparent then tIdx else none)
    else
      let base := if clearThis then allT else prev
      let cover := if clearNext then diffRect cur allT w h 1 else none
      let r : Rect := match diffRect base cur w h 1, cover with
        | some a, some b => a.union b
        | some a, none => a
        | none, some b => b
        | none, none => { x := 0, y := 0, w := 1, h := 1 }
      let plain := cropBytes cur w 1 r
      let ep := Lzw.encode minCode plain
      let sub := (tIdx.map fun tt => substitute plain (cropBytes base w 1 r) tt.toUInt8).getD plain
      let es := Lzw.encode minCode sub
      let useSub := tIdx.isSome && es.size < ep.size
      out := out ++ gifFrame r (if useSub then es else ep) minCode c disposal
        (if pal.hasTransparent || useSub then tIdx else none)
    clearThis := clearNext
  return out.push 0x3B

end FrameSeq

end PILean
