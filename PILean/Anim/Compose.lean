/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Anim.Frames

/-!
# Composing frames

The canvas of an animated image reader: drawing a frame's rectangle with `SOURCE` or `OVER`
blending and disposing of it as `NONE`, `BACKGROUND` or `PREVIOUS`, as APNG defines them and as
GIF's disposal methods map onto them.

## Main definitions

* `Anim.FrameCtl`: a frame's rectangle, delay, disposal and blend operation.
* `Anim.Composer`, `Anim.Composer.add`: the canvas and the frames shown so far; adding one frame.

## Implementation notes

* `OVER` composites straight (non-premultiplied) alpha with rounding to nearest, as the APNG
  specification's formulas give: opaque source pixels replace, transparent ones leave the
  canvas, and a transparent canvas takes the source.
* Every access goes through `Png.byteAt` and `Png.setByte`, so nothing can panic.
* A disposal of `PREVIOUS` on the first frame acts as `BACKGROUND`.

## References

* Animated Portable Network Graphics (APNG) Specification, MDN / Mozilla; Graphics Interchange
  Format, Version 89a (CompuServe, 1990). Written from the specifications.
-/

namespace PILean.Anim

/-- The fields of an `fcTL` chunk. -/
structure FrameCtl where
  /-- The frame's rectangle on the canvas. -/
  rect : Rect
  /-- Delay numerator. -/
  num : Nat
  /-- Delay denominator (0 means 100). -/
  den : Nat
  /-- `dispose_op`: 0 none, 1 background, 2 previous. -/
  dispose : Nat
  /-- `blend_op`: 0 source, 1 over. -/
  blend : Nat

/-- The canvas (RGBA samples) with the frames composed so far and their delays. -/
structure Composer where
  /-- Canvas width. -/
  w : Nat
  /-- Canvas height. -/
  h : Nat
  /-- The canvas after disposal of the last frame. -/
  canvas : ByteArray
  /-- The canvas as it was shown for each frame. -/
  frames : Array Image := #[]
  /-- The delay of each frame, in lowest terms. -/
  delays : Array (Nat × Nat) := #[]

/-- Source-over compositing of straight-alpha samples `src` onto `dst`, with rounding. -/
def overPixel (dst src : Array Nat) : Array Nat :=
  let sa := src.getD 3 0
  let da := dst.getD 3 0
  if sa == 255 || da == 0 then src
  else if sa == 0 then dst
  else
    let t := sa * 255 + da * (255 - sa)
    let ch := fun (k : Nat) =>
      (src.getD k 0 * sa * 255 + dst.getD k 0 * da * (255 - sa) + t / 2) / t
    #[ch 0, ch 1, ch 2, (t + 127) / 255]

/-- The canvas with the `r` area (of `pix`, `r.w × r.h` RGBA samples) drawn by `blend`. -/
def drawRect (canvas : ByteArray) (w : Nat) (r : Rect) (pix : ByteArray) (blend : Nat) :
    ByteArray := Id.run do
  let mut c := canvas
  for row in [0:r.h] do
    for col in [0:r.w] do
      let si := (row * r.w + col) * 4
      let di := ((r.y + row) * w + r.x + col) * 4
      let src := #[Png.byteAt pix si, Png.byteAt pix (si + 1), Png.byteAt pix (si + 2),
        Png.byteAt pix (si + 3)]
      let out :=
        if blend == 0 then src.map (·.toNat)
        else
          let old := #[Png.byteAt c di, Png.byteAt c (di + 1), Png.byteAt c (di + 2),
            Png.byteAt c (di + 3)]
          overPixel (old.map (·.toNat)) (src.map (·.toNat))
      for k in [0:4] do c := Png.setByte c (di + k) (out.getD k 0).toUInt8
  return c

/-- The canvas with the area `r` cleared to transparent black. -/
def clearRect (canvas : ByteArray) (w : Nat) (r : Rect) : ByteArray := Id.run do
  let mut c := canvas
  for row in [0:r.h] do
    for col in [0:r.w * 4] do
      c := Png.setByte c (((r.y + row) * w + r.x) * 4 + col) 0
  return c

/-- Composes one frame: draws it, records the canvas as the shown frame, then disposes. -/
def Composer.add (c : Composer) (ctl : FrameCtl) (pix : ByteArray) : Composer :=
  let drawn := drawRect c.canvas c.w ctl.rect pix ctl.blend
  let dispose := if c.frames.isEmpty && ctl.dispose == 2 then 1 else ctl.dispose
  let canvas := match dispose with
    | 1 => clearRect drawn c.w ctl.rect
    | 2 => c.canvas
    | _ => drawn
  let den := if ctl.den == 0 then 100 else ctl.den
  { c with
    canvas := canvas
    frames := c.frames.push { mode := .rgba, width := c.w, height := c.h, data := drawn }
    delays := c.delays.push (reduceFrac ctl.num den) }

end PILean.Anim
