/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Anim.Frames
import PILean.Png

/-!
# The APNG writer

`FrameSeq.toApng` writes an animated PNG: a PNG file whose `IDAT` data is the first frame (and the
default image for readers that do not animate) followed by `fcTL` and `fdAT` chunks for the
other frames.

## Main definitions

* `FrameSeq.toApng`: the APNG bytes of a frame sequence.
* `Anim.fcTLData`: the 26 bytes of a frame-control chunk.

## Implementation notes

* Chunks, in order: `IHDR`, `sRGB`, `gAMA`, `acTL`, then for each frame its `fcTL` and its image
  data (`IDAT` for the first, `fdAT` for the others), `IEND`. The colour type is 6 (RGBA) at bit
  depth 8. The sequence numbers of the `fcTL` and `fdAT` chunks count up from 0.
* Frame differencing: every frame after the first is stored as the smallest rectangle that
  contains all pixels that differ from the previous frame, with `dispose_op = NONE` and
  `blend_op = SOURCE`; the rectangle's pixels replace the canvas, so the composed canvas after
  frame `i` is exactly frame `i`. (`blend_op = OVER` with unchanged pixels made transparent
  could not reproduce a pixel that becomes less opaque, so it is not used.)
* A frame equal to the one before it is not stored; its delay is added to the previous frame's.
* A delay is reduced to lowest terms; if numerator or denominator exceed 65535 the closest
  fraction that fits is stored (`Anim.fitFrac`).
* The output is a function of the arguments alone.

## References

* Animated Portable Network Graphics (APNG) Specification, MDN / Mozilla; PNG Specification,
  Third Edition (W3C), which defines the chunks the format extends. Written from the
  specifications.
-/

namespace PILean

namespace Anim

/-- The data of an `fcTL` chunk: sequence number, rectangle, delay `num / den` seconds,
`dispose_op` and `blend_op`. -/
def fcTLData (seq : Nat) (r : Rect) (num den : Nat) (dispose blend : UInt8) : ByteArray :=
  Png.be32 seq.toUInt32 ++ Png.be32 r.w.toUInt32 ++ Png.be32 r.h.toUInt32 ++
    Png.be32 r.x.toUInt32 ++ Png.be32 r.y.toUInt32 ++
    ⟨#[(num >>> 8).toUInt8, num.toUInt8, (den >>> 8).toUInt8, den.toUInt8, dispose, blend]⟩

/-- The chunks that carry the zlib stream `z`: `IDAT` pieces when `seq` is none, else `fdAT`
pieces numbered from `seq`. Returns the bytes and the next sequence number. -/
def dataChunks (z : ByteArray) (seq : Option Nat) : ByteArray × Nat := Id.run do
  let mut out := ByteArray.empty
  let mut pos := 0
  let mut n := seq.getD 0
  for _ in [0:z.size / Png.idatChunkSize + 1] do
    if pos ≥ z.size then break
    let e := min z.size (pos + Png.idatChunkSize)
    match seq with
    | none => out := out ++ Png.chunk "IDAT" (z.extract pos e)
    | some _ =>
      out := out ++ Png.chunk "fdAT" (Png.be32 n.toUInt32 ++ z.extract pos e)
      n := n + 1
    pos := e
  return (out, n)

end Anim

namespace FrameSeq

open Anim in
/-- The APNG file for a frame sequence, with the zlib compression `level` of `Png.zlibCompress`.
Fails with `AnimError.invalidInput` if `validate` does. -/
def toApng (s : FrameSeq) (level : Nat := 6) : Except AnimError ByteArray := do
  let rgba ← s.rgbaFrames
  let (fs, ds) := mergeEqual rgba s.delays
  let ihdr := Png.be32 s.width.toUInt32 ++ Png.be32 s.height.toUInt32 ++ ⟨#[8, 6, 0, 0, 0]⟩
  let mut out := Png.pngSignature ++ Png.chunk "IHDR" ihdr ++ Png.chunk "sRGB" ⟨#[0]⟩ ++
    Png.chunk "gAMA" (Png.be32 45455) ++
    Png.chunk "acTL" (Png.be32 fs.size.toUInt32 ++ Png.be32 s.loops.toUInt32)
  let full : Rect := { x := 0, y := 0, w := s.width, h := s.height }
  let mut seq := 0
  let mut prev := ByteArray.empty
  for (f, d) in fs.zip ds do
    let first := prev.isEmpty
    let r := if first then full else
      (diffRect prev f s.width s.height 4).getD { x := 0, y := 0, w := 1, h := 1 }
    let (num, den) := fitFrac d.1 d.2
    out := out ++ Png.chunk "fcTL" (fcTLData seq r num den 0 0)
    seq := seq + 1
    let raw : Png.RawImage :=
      { width := r.w, height := r.h, mode := .rgba, data := cropBytes f s.width 4 r }
    let z := Png.zlibCompress (Png.filterImage raw none) level
    let (bytes, seq') := dataChunks z (if first then none else some seq)
    out := out ++ bytes
    if !first then seq := seq'
    prev := f
  return out ++ Png.chunk "IEND" ByteArray.empty

end FrameSeq

end PILean
