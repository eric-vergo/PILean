/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Raster.Coverage
import PILean.Raster.SrgbTables
import PILean.Image.Basic

/-!
# Paint and compositing

The surface the rasteriser paints on, and what it paints with.

* **The surface** (`Canvas`) holds every pixel in linear light, premultiplied by its alpha, at
  16 bits a channel. Painting composites source over destination there, in linear light, as the
  physics of light adding up asks; the result is converted to 8-bit sRGB with straight alpha
  when it becomes an `Image` (`Canvas.toImage`). Conversions are table lookups at 16-bit
  precision (`PILean.Raster.SrgbTables`), so they are the same on every
  machine.
* **Paints**: a solid colour; a linear gradient along a segment; a radial gradient from a
  centre to a radius. A gradient's stops are interpolated in linear light (premultiplied), and
  it is padded beyond its ends. The parameter of a pixel (its centre's position along the
  gradient) is computed in `Float` with the basic operations, which IEEE 754 rounds the same
  everywhere; the interpolation that follows is integer.
* **Group opacity**: a group is painted on a canvas of its own and composited with its opacity
  (`Canvas.compositeOver`), so overlapping parts of the group do not show through each other.
* **Clipping**: to a rectangle by the spans themselves, and to a clip path through a coverage
  mask (`Mask`) that multiplies the coverage.

SVG interpolates gradients in sRGB by default (its `color-interpolation` is `sRGB`, and
browsers do not implement `linearRGB` for gradients); PILean's SVG writer therefore writes a
gradient with intermediate stops sampled from the linear-light interpolation, so that both
outputs show the same colours.

## Main definitions

* `Lin`: a linear-light premultiplied colour, 16 bits a channel.
* `Paint`, `Stop`; `Paint.at`.
* `Canvas`, `Canvas.new`, `Canvas.fillSpans`, `Canvas.compositeOver`, `Canvas.toImage`.
* `Mask`, `Mask.ofSpans`.
-/

namespace PILean.Raster

/-- A colour in linear light, premultiplied by its alpha, each channel 0 to 65535. -/
structure Lin where
  /-- Red, premultiplied. -/
  r : Nat
  /-- Green, premultiplied. -/
  g : Nat
  /-- Blue, premultiplied. -/
  b : Nat
  /-- Alpha. -/
  a : Nat
  deriving BEq, Inhabited, Repr

/-- The space colours are mixed in: linear light (the default, physically right), or the sRGB
encoding itself (as many renderers mix; offered for comparing with them). -/
inductive Space where
  /-- Linear light. -/
  | linear
  /-- The sRGB encoding, mixed as if it were linear. -/
  | srgb
  deriving BEq, Inhabited, Repr

/-- An 8-bit sRGB channel in the mixing space, 0 to 65535: linear light, or the encoded value
scaled. -/
def decode8 (v : UInt8) (s : Space := .linear) : Nat :=
  match s with
  | .linear => srgbDecode16[v.toNat]?.getD 0
  | .srgb => v.toNat * 257

/-- A linear-light channel (0 to 65535) as the nearest 8-bit sRGB value: the number of steps
of `srgbThreshold16` at or below it (a binary search). -/
def encode16 (v : Nat) (s : Space := .linear) : UInt8 := Id.run do
  if s == .srgb then return (min 255 ((v + 128) / 257)).toUInt8
  let mut lo := 0
  let mut hi := 255
  for _ in [0:9] do
    if lo ≥ hi then break
    let m := (lo + hi) / 2
    if srgbThreshold16[m]?.getD 65535 ≤ v then lo := m + 1 else hi := m
  return lo.toUInt8

/-- `a * b / c` rounded to the nearest integer (0 when `c = 0`). -/
def mulDiv (a b c : Nat) : Nat := if c == 0 then 0 else (a * b + c / 2) / c

/-- An 8-bit straight-alpha sRGB colour in linear light, premultiplied. -/
def Lin.ofRgba (c : Rgba) (s : Space := .linear) : Lin :=
  let a := mulDiv c.a.toNat 65535 255
  ⟨mulDiv (decode8 c.r s) a 65535, mulDiv (decode8 c.g s) a 65535, mulDiv (decode8 c.b s) a 65535,
    a⟩

/-- A premultiplied linear colour as 8-bit straight-alpha sRGB. -/
def Lin.toRgba (c : Lin) (s : Space := .linear) : Rgba :=
  if c.a == 0 then ⟨0, 0, 0, 0⟩
  else
    let un := fun (v : Nat) => min 65535 (mulDiv v 65535 c.a)
    ⟨encode16 (un c.r) s, encode16 (un c.g) s, encode16 (un c.b) s,
      (mulDiv c.a 255 65535).toUInt8⟩

/-- `a + (b - a) · t / 65536` for each channel, `t` from 0 to 65536. -/
def Lin.lerp (a b : Lin) (t : Nat) : Lin :=
  let f := fun (x y : Nat) => (x * (65536 - t) + y * t + 32768) / 65536
  ⟨f a.r b.r, f a.g b.g, f a.b b.b, f a.a b.a⟩

/-- A gradient stop: a position from 0 to 1 and a colour. -/
structure Stop where
  /-- The position along the gradient. -/
  offset : Float
  /-- The colour. -/
  color : Rgba
  deriving Inhabited, Repr

/-- What a shape is painted with. -/
inductive Paint where
  /-- One colour. -/
  | solid (c : Rgba)
  /-- A linear gradient: 0 at `p0`, 1 at `p1`, constant across. -/
  | linear (p0 p1 : Point) (stops : Array Stop)
  /-- A radial gradient: 0 at `centre`, 1 at distance `radius`. -/
  | radial (centre : Point) (radius : Float) (stops : Array Stop)
  deriving Inhabited, Repr

/-- The colour of the stops at parameter `t` (padded beyond 0 and 1), in linear light. -/
def stopsAt (stops : Array Stop) (t : Float) (s : Space := .linear) : Lin := Id.run do
  let some first := stops[0]? | return ⟨0, 0, 0, 0⟩
  let t := if t.isNaN then 0 else t
  if t ≤ first.offset then return Lin.ofRgba first.color s
  for i in [0:stops.size - 1] do
    let a := stops[i]?.getD first
    let b := stops[i + 1]?.getD first
    if t ≤ b.offset then
      let span := b.offset - a.offset
      let u := if span ≤ 0 then 1 else (t - a.offset) / span
      let k : Nat := (u * 65536 + 0.5).floor.toUInt64.toNat
      return (Lin.ofRgba a.color s).lerp (Lin.ofRgba b.color s) (min 65536 k)
  return Lin.ofRgba (stops.back?.getD first).color s

/-- The paint's colour at the pixel whose centre is `(x + ½, y + ½)`. -/
def Paint.at (p : Paint) (x y : Nat) (s : Space := .linear) : Lin :=
  match p with
  | .solid c => Lin.ofRgba c s
  | .linear p0 p1 stops =>
    let d := p1 - p0
    let len2 := d.x * d.x + d.y * d.y
    let q : Point := ⟨x.toFloat + 0.5 - p0.x, y.toFloat + 0.5 - p0.y⟩
    stopsAt stops (if len2 == 0 then 0 else (q.x * d.x + q.y * d.y) / len2) s
  | .radial c r stops =>
    let q : Point := ⟨x.toFloat + 0.5 - c.x, y.toFloat + 0.5 - c.y⟩
    stopsAt stops (if r ≤ 0 then 1 else (q.x * q.x + q.y * q.y).sqrt / r) s

/-- A coverage mask over a whole image: 0 to 255 a pixel. -/
structure Mask where
  /-- Width. -/
  width : Nat
  /-- Height. -/
  height : Nat
  /-- One byte a pixel. -/
  data : ByteArray

/-- The mask of a fill's spans. -/
def Mask.ofSpans (w h : Nat) (spans : Array Span) : Mask := Id.run do
  let mut data := Png.filledBytes (w * h)
  for s in spans do
    for x in [s.x:s.x + s.len] do
      let i := s.y * w + x
      if i < data.size then data := data.set! i s.alpha
  return ⟨w, h, data⟩

/-- The mask's value at a pixel (0 outside). -/
def Mask.get (m : Mask) (x y : Nat) : Nat :=
  let i := y * m.width + x
  if h : i < m.data.size then m.data[i].toNat else 0

/-- The surface: `width × height` pixels in premultiplied linear light, 16 bits a channel
(eight bytes a pixel, little-endian). -/
structure Canvas where
  /-- Width. -/
  width : Nat
  /-- Height. -/
  height : Nat
  /-- The pixels. -/
  data : ByteArray
  /-- The space colours are mixed in. -/
  space : Space := .linear

namespace Canvas

/-- A canvas filled with a colour. -/
def new (w h : Nat) (bg : Rgba := ⟨0, 0, 0, 0⟩) (space : Space := .linear) : Canvas :=
  Id.run do
  let c := Lin.ofRgba bg space
  let px : Array UInt8 := #[c.r, c.g, c.b, c.a].foldl (init := #[]) fun acc v =>
    acc.push (v % 256).toUInt8 |>.push (v / 256).toUInt8
  let mut data := ByteArray.emptyWithCapacity (w * h * 8)
  for _ in [0:w * h] do
    for b in px do data := data.push b
  return ⟨w, h, data, space⟩

/-- The 16-bit value at byte offset `i`. -/
@[inline] def get16 (d : ByteArray) (i : Nat) : Nat :=
  if h : i + 1 < d.size then d[i].toNat + 256 * d[i + 1].toNat else 0

/-- The array with the 16-bit value `v` at byte offset `i`. -/
@[inline] def set16 (d : ByteArray) (i v : Nat) : ByteArray :=
  if i + 1 < d.size then (d.set! i (v % 256).toUInt8).set! (i + 1) (v / 256 % 256).toUInt8
  else d

/-- The colour of pixel `(x, y)`. -/
def get (c : Canvas) (x y : Nat) : Lin :=
  let i := (y * c.width + x) * 8
  ⟨get16 c.data i, get16 c.data (i + 2), get16 c.data (i + 4), get16 c.data (i + 6)⟩

/-- Source over destination at one pixel: `src` (premultiplied) scaled by coverage `k`
(0 to 65535) over the pixel at byte offset `i`. -/
@[inline] def blendAt (d : ByteArray) (i : Nat) (src : Lin) (k : Nat) : ByteArray :=
  let sa := mulDiv src.a k 65535
  let keep := 65535 - sa
  let ch := fun (d : ByteArray) (o s : Nat) =>
    set16 d (i + o) (min 65535 (mulDiv s k 65535 + mulDiv (get16 d (i + o)) keep 65535))
  let d := ch d 0 src.r
  let d := ch d 2 src.g
  let d := ch d 4 src.b
  set16 d (i + 6) (min 65535 (sa + mulDiv (get16 d (i + 6)) keep 65535))

/-- Paints spans with a paint at an opacity (0 to 1), through an optional clip mask. Pixels
outside the spans are not changed; nor are pixels outside the canvas. -/
def fillSpans (c : Canvas) (spans : Array Span) (paint : Paint) (opacity : Float := 1)
    (mask : Option Mask := none) : Canvas := Id.run do
  let op : Nat := ((if opacity.isNaN then 0 else max 0 (min 1 opacity)) * 65535 + 0.5).floor
    |>.toUInt64.toNat
  let mut d := c.data
  let solid := match paint with | .solid col => some (Lin.ofRgba col c.space) | _ => none
  for s in spans do
    if s.y ≥ c.height then continue
    for x in [s.x:min (s.x + s.len) c.width] do
      let m := match mask with | some m => m.get x s.y | none => 255
      let k := mulDiv (mulDiv s.alpha.toNat 65535 255) (mulDiv op m 255) 65535
      if k == 0 then continue
      let src := solid.getD (paint.at x s.y c.space)
      d := blendAt d ((s.y * c.width + x) * 8) src k
  return { c with data := d }

/-- The canvas `layer` (same size) composited over `c` at an opacity: a group's opacity. -/
def compositeOver (c layer : Canvas) (opacity : Float := 1) : Canvas := Id.run do
  let op : Nat := ((if opacity.isNaN then 0 else max 0 (min 1 opacity)) * 65535 + 0.5).floor
    |>.toUInt64.toNat
  let mut d := c.data
  for y in [0:min c.height layer.height] do
    for x in [0:min c.width layer.width] do
      let src := layer.get x y
      if src.a == 0 then continue
      d := blendAt d ((y * c.width + x) * 8) src op
  return { c with data := d }

/-- The canvas as an 8-bit sRGB image with straight alpha (`RGBA`, or `RGB` or `L` without
the alpha, as `mode` asks). A run of equal pixels is converted once. -/
def toImage (c : Canvas) (mode : Mode := .rgba) : Image := Id.run do
  let n := mode.channels
  let mut data := ByteArray.emptyWithCapacity (c.width * c.height * n)
  let mut last : Lin := ⟨0, 0, 0, 0⟩
  let mut px : Array UInt8 := Image.samplesOf mode (Lin.toRgba last c.space)
  for y in [0:c.height] do
    for x in [0:c.width] do
      let v := c.get x y
      if v != last then
        last := v
        px := Image.samplesOf mode (v.toRgba c.space)
      for b in px do data := data.push b
  return { mode, width := c.width, height := c.height, data }

end Canvas

end PILean.Raster
