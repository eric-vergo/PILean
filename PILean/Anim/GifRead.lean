/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Anim.Compose
import PILean.Anim.Lzw

/-!
# The GIF reader

`Anim.readGif` reads a GIF (87a or 89a) and composes every frame onto the canvas.

## Main definitions

* `Anim.readGif`: the composed RGBA frames, their delays (in centiseconds, as fractions of a
  second) and the loop count.
* `Anim.interlaceRows`: where the stored rows of an interlaced image belong.

## Implementation notes

* Understood: the header, the logical screen, global and local colour tables, graphic control
  extensions (disposal methods 0 to 3, transparency index, delay), the `NETSCAPE2.0` loop
  extension, and interlaced images. Comment, plain-text, other application and unknown
  extensions are skipped through their data sub-blocks. The background colour is ignored: the
  canvas starts transparent and "restore to background" clears to transparent, as browsers do.
  Disposal methods 4 to 7 act as 0.
* Loops: without a `NETSCAPE2.0` extension the animation plays once (`loops = 1`); an extension
  with count 0 gives `loops = 0` (forever), count `n` gives `n + 1`.
* The input is untrusted: the canvas must be at most `Limits.maxPixels` pixels, the frames at
  most `Limits.maxFrames`, the composed frames together at most `Limits.maxBytes`; a frame must
  lie inside the canvas and its pixel indices must exist in its colour table; the LZW stream
  must hold exactly the frame's pixels. Every loop is bounded by the input size. Failure is an
  `AnimError`, never a panic.

## References

* Graphics Interchange Format, Version 89a (CompuServe, 1990). Written from the specification.
-/

namespace PILean.Anim

/-- The image row each stored row of an interlaced image of height `h` belongs to: every eighth
row from 0, every eighth from 4, every fourth from 2, every second from 1. -/
def interlaceRows (h : Nat) : Array Nat := Id.run do
  let mut out := #[]
  for (start, step) in [(0, 8), (4, 8), (2, 4), (1, 2)] do
    for k in [0:h / step + 1] do
      if start + k * step < h then out := out.push (start + k * step)
  return out

/-- A 16-bit little-endian number at `i`. -/
def getLe16 (d : ByteArray) (i : Nat) : Nat :=
  (Png.byteAt d i).toNat + (Png.byteAt d (i + 1)).toNat * 256

/-- The RGBA samples of indices `ix` for a `w × h` image from the colour table `tab` (three bytes
per entry); the `transparent` index becomes transparent black. -/
def indicesToRgba (ix tab : ByteArray) (w h : Nat) (interlaced : Bool)
    (transparent : Option Nat) : Except AnimError ByteArray := do
  let rows := if interlaced then interlaceRows h else #[]
  let mut out := Png.filledBytes (w * h * 4)
  for j in [0:h] do
    let y := if interlaced then rows.getD j 0 else j
    for x in [0:w] do
      let v := (Png.byteAt ix (j * w + x)).toNat
      if transparent != some v then
        if 3 * v + 3 > tab.size then throw (.malformed "pixel index outside the colour table")
        let o := (y * w + x) * 4
        out := Png.setByte out o (Png.byteAt tab (3 * v))
        out := Png.setByte out (o + 1) (Png.byteAt tab (3 * v + 1))
        out := Png.setByte out (o + 2) (Png.byteAt tab (3 * v + 2))
        out := Png.setByte out (o + 3) 255
  return out

/-- Reads the colour table of `n` entries at `pos`, and the position after it. -/
def readTable (bytes : ByteArray) (pos n : Nat) : Except AnimError (ByteArray × Nat) := do
  if pos + 3 * n > bytes.size then throw .truncated
  return (bytes.extract pos (pos + 3 * n), pos + 3 * n)

/-- The graphic-control state that applies to the next image. -/
structure Gce where
  /-- The disposal method. -/
  disposal : Nat := 0
  /-- The transparent colour index. -/
  transparent : Option Nat := none
  /-- The delay in centiseconds. -/
  delay : Nat := 0

/-- Reads a GIF file and composes its frames. The delays are `(cs, 100)` in lowest terms. Fails
with an `AnimError` if the file is malformed, truncated or larger than `lim` allows. -/
def readGif (bytes : ByteArray) (lim : Limits := {}) : Except AnimError FrameSeq := do
  if bytes.size < 13 then throw .truncated
  let sig := bytes.extract 0 6
  if sig != "GIF89a".toUTF8 && sig != "GIF87a".toUTF8 then throw (.malformed "not a GIF file")
  let w := getLe16 bytes 6
  let h := getLe16 bytes 8
  let packed := (Png.byteAt bytes 10).toNat
  if w == 0 || h == 0 then throw (.malformed "zero-sized logical screen")
  if w * h > lim.maxPixels then throw (.tooLarge s!"{w} x {h} pixels")
  let mut pos := 13
  let mut gct := ByteArray.empty
  if packed &&& 0x80 != 0 then
    let (t, p) ← readTable bytes pos (1 <<< ((packed &&& 7) + 1))
    gct := t
    pos := p
  let mut comp : Composer := { w, h, canvas := Png.filledBytes (w * h * 4) }
  let mut gce : Gce := {}
  let mut loops := 1
  let mut done := false
  for _ in [0:bytes.size + 1] do
    if pos ≥ bytes.size then throw .truncated
    let b := Png.byteAt bytes pos
    if b == 0x3B then
      done := true
      break
    else if b == 0x21 then
      if pos + 2 > bytes.size then throw .truncated
      let label := Png.byteAt bytes (pos + 1)
      if label == 0xF9 then
        if pos + 8 > bytes.size then throw .truncated
        if Png.byteAt bytes (pos + 2) != 4 || Png.byteAt bytes (pos + 7) != 0 then
          throw (.malformed "invalid graphic control extension")
        let f := (Png.byteAt bytes (pos + 3)).toNat
        gce := { disposal := (f >>> 2) &&& 7,
                 transparent := if f &&& 1 != 0 then some (Png.byteAt bytes (pos + 6)).toNat
                   else none,
                 delay := getLe16 bytes (pos + 4) }
        pos := pos + 8
      else
        let (d, p) ← match Lzw.unpackBlocks bytes (pos + 2) with
          | .ok r => pure r
          | .error e => throw (.malformed e)
        if label == 0xFF && d.size ≥ 14 && d.extract 0 11 == "NETSCAPE2.0".toUTF8 &&
            Png.byteAt d 11 == 1 then
          let n := getLe16 d 12
          loops := if n == 0 then 0 else n + 1
        pos := p
    else if b == 0x2C then
      if pos + 10 > bytes.size then throw .truncated
      let r : Rect := { x := getLe16 bytes (pos + 1), y := getLe16 bytes (pos + 3),
                        w := getLe16 bytes (pos + 5), h := getLe16 bytes (pos + 7) }
      let f := (Png.byteAt bytes (pos + 9)).toNat
      pos := pos + 10
      let mut tab := gct
      if f &&& 0x80 != 0 then
        let (t, p) ← readTable bytes pos (1 <<< ((f &&& 7) + 1))
        tab := t
        pos := p
      if r.w == 0 || r.h == 0 || r.x + r.w > w || r.y + r.h > h then
        throw (.malformed "frame rectangle outside the screen")
      if comp.frames.size + 1 > lim.maxFrames then throw (.tooLarge "number of frames")
      if (comp.frames.size + 1) * (w * h * 4) > lim.maxBytes then
        throw (.tooLarge "composed frames")
      if pos ≥ bytes.size then throw .truncated
      let minCode := (Png.byteAt bytes pos).toNat
      let (stream, p) ← match Lzw.unpackBlocks bytes (pos + 1) with
        | .ok r => pure r
        | .error e => throw (.malformed e)
      pos := p
      let ix ← match Lzw.decode minCode stream (r.w * r.h) with
        | .ok r => pure r
        | .error e => throw (.malformed e)
      let pix ← indicesToRgba ix tab r.w r.h (f &&& 0x40 != 0) gce.transparent
      let dispose := if gce.disposal == 2 then 1 else if gce.disposal == 3 then 2 else 0
      comp := comp.add { rect := r, num := gce.delay, den := 100, dispose, blend := 1 } pix
      gce := {}
    else throw (.malformed "unknown block")
  if !done then throw .truncated
  if comp.frames.isEmpty then throw (.malformed "no frames")
  return { width := w, height := h, frames := comp.frames, delays := comp.delays, loops }

end PILean.Anim
