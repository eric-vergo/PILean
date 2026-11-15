/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Png.Tables
import Std.Data.HashMap

/-!
# Palette quantisation

One palette for all frames of a GIF: the exact colours when there are at most 256 of them, else
median cut, and the mapping of pixels to palette indices, optionally with error diffusion.

## Main definitions

* `Quant.Palette`: the colours and the index reserved for transparency, if any.
* `Quant.quantize`: the palette of a list of RGBA frames.
* `Quant.indexFrame`: a frame's pixels as palette indices (`Quant.Cache` memoises the nearest
  colour).

## Implementation notes

* A pixel with alpha below 128 is transparent; any other pixel is opaque with its colour. If any
  pixel is transparent, one palette entry (the last one, at index `colors.size`) is kept for it
  and the colours are at most 255.
* The colours are the distinct opaque colours, in order of their packed value `r·65536 + g·256
  + b`, when there are at most as many as fit; otherwise median cut: the box with the largest
  population times widest channel range is split at the median pixel along that channel (boxes
  are sorted by channel value, then packed value), until there are as many boxes as colours fit;
  each entry is the rounded population-weighted mean of its box. Everything is deterministic.
* Nearest colour: smallest squared distance in RGB, the lowest index on ties.
* Dithering is Floyd–Steinberg with the usual weights 7, 3, 5, 1 over 16, scanning every row left
  to right (not serpentine). Errors are integers scaled by 16 and rounded by an arithmetic
  shift, so the output is identical on every machine; transparent pixels neither take nor give
  error.

## References

* P. Heckbert, "Color image quantization for frame buffer display", SIGGRAPH 1982 (median cut).
* R. W. Floyd and L. Steinberg, "An adaptive algorithm for spatial grey scale", Proceedings of
  the Society for Information Display 17 (1976). Written from these descriptions.
-/

namespace PILean.Anim.Quant

/-- The palette: opaque colours as packed `r·65536 + g·256 + b`, and whether an entry at index
`colors.size` stands for transparency. -/
structure Palette where
  /-- The colours, packed. -/
  colors : Array UInt32
  /-- Whether an entry at index `colors.size` is reserved for transparent pixels. -/
  hasTransparent : Bool
  /-- Whether the palette holds every colour of the input exactly. -/
  exact : Bool

/-- The number of entries including the transparent one. -/
def Palette.size (p : Palette) : Nat := p.colors.size + if p.hasTransparent then 1 else 0

/-- The packed colour of three channels. -/
def pack (r g b : Nat) : UInt32 := (r.toUInt32 <<< 16) ||| (g.toUInt32 <<< 8) ||| b.toUInt32

/-- Channel `k` (0 red, 1 green, 2 blue) of a packed colour. -/
def chan (c : UInt32) (k : Nat) : Nat :=
  match k with
  | 0 => (c >>> 16).toNat &&& 255
  | 1 => (c >>> 8).toNat &&& 255
  | _ => c.toNat &&& 255

/-- The squared RGB distance between a colour and `(r, g, b)`. -/
def dist2 (c : UInt32) (r g b : Nat) : Nat :=
  let d := fun (k v : Nat) => (Int.natAbs ((chan c k : Int) - v)) ^ 2
  d 0 r + d 1 g + d 2 b

/-- The index of the palette colour nearest to `(r, g, b)` (the lowest on ties); 0 if the
palette has no colours. -/
def Palette.nearest (p : Palette) (r g b : Nat) : Nat := Id.run do
  let mut best := 0
  let mut bestD := 3 * 255 * 255 + 1
  for i in [0:p.colors.size] do
    let d := dist2 (p.colors.getD i 0) r g b
    if d < bestD then
      best := i
      bestD := d
  return best

/-- A box of colours (packed, with their pixel counts) with its statistics. -/
structure Box where
  /-- The colours with their counts. -/
  items : Array (UInt32 × Nat)
  /-- Total count. -/
  pop : Nat
  /-- The channel with the widest range. -/
  ch : Nat
  /-- That range. -/
  range : Nat

/-- The box of some items. -/
def Box.ofItems (items : Array (UInt32 × Nat)) : Box := Id.run do
  let mut lo := #[255, 255, 255]
  let mut hi := #[0, 0, 0]
  let mut pop := 0
  for (c, n) in items do
    pop := pop + n
    for k in [0:3] do
      lo := lo.setIfInBounds k (min (lo.getD k 0) (chan c k))
      hi := hi.setIfInBounds k (max (hi.getD k 0) (chan c k))
  let mut ch := 0
  let mut range := 0
  for k in [0:3] do
    let r := hi.getD k 0 - lo.getD k 0
    if r > range then
      ch := k
      range := r
  return { items, pop, ch, range }

/-- The rounded population-weighted mean colour of a box. -/
def Box.mean (b : Box) : UInt32 :=
  let s := fun (k : Nat) => b.items.foldl (fun a (c, n) => a + n * chan c k) 0
  let m := fun (k : Nat) => (s k * 2 + b.pop) / (2 * b.pop)
  pack (m 0) (m 1) (m 2)

/-- Splits a box with at least two colours at the median pixel along its widest channel. -/
def Box.split (b : Box) : Box × Box := Id.run do
  let sorted := b.items.qsort fun x y =>
    let cx := chan x.1 b.ch
    let cy := chan y.1 b.ch
    cx < cy || (cx == cy && x.1 < y.1)
  let mut cum := 0
  let mut cut := sorted.size - 1
  for i in [0:sorted.size] do
    cum := cum + (sorted.getD i (0, 0)).2
    if cum * 2 ≥ b.pop then
      cut := i + 1
      break
  let c := min (max cut 1) (sorted.size - 1)
  return (Box.ofItems (sorted.extract 0 c), Box.ofItems (sorted.extract c sorted.size))

/-- Median cut of weighted colours into at most `cap` entries. -/
def medianCut (items : Array (UInt32 × Nat)) (cap : Nat) : Array UInt32 := Id.run do
  let mut boxes : Array Box := #[Box.ofItems items]
  for _ in [0:cap] do
    if boxes.size ≥ cap then break
    let mut bi := boxes.size
    let mut bs := 0
    for i in [0:boxes.size] do
      let b := boxes.getD i (Box.ofItems #[])
      if b.items.size ≥ 2 && (bi == boxes.size || b.pop * b.range > bs) then
        bi := i
        bs := b.pop * b.range
    if bi == boxes.size then break
    let (l, r) := (boxes.getD bi (Box.ofItems #[])).split
    boxes := (boxes.setIfInBounds bi l).push r
  return boxes.map Box.mean

/-- The palette for RGBA frames (`4` bytes per pixel): see the module documentation. -/
def quantize (frames : Array ByteArray) (maxColors : Nat := 256) : Palette := Id.run do
  let mut hist : Std.HashMap UInt32 Nat := {}
  let mut transparent := false
  for f in frames do
    for i in [0:f.size / 4] do
      if (Png.byteAt f (4 * i + 3)) < 128 then transparent := true
      else
        let c := pack (Png.byteAt f (4 * i)).toNat (Png.byteAt f (4 * i + 1)).toNat
          (Png.byteAt f (4 * i + 2)).toNat
        hist := hist.insert c (hist.getD c 0 + 1)
  let cap := maxColors - if transparent then 1 else 0
  let items := hist.toArray.qsort fun x y => x.1 < y.1
  if items.size ≤ cap then
    return { colors := items.map (·.1), hasTransparent := transparent, exact := true }
  return { colors := medianCut items cap, hasTransparent := transparent, exact := false }

/-- The memo of nearest palette indices by packed colour. -/
abbrev Cache := Std.HashMap UInt32 Nat

/-- The index of the palette entry for `(r, g, b)`, using and extending the cache. -/
def lookup (p : Palette) (cache : Cache) (r g b : Nat) : Nat × Cache :=
  let key := pack r g b
  match cache[key]? with
  | some i => (i, cache)
  | none =>
    let i := p.nearest r g b
    (i, cache.insert key i)

/-- The clamp of an integer to the range 0 to 255. -/
def clamp8 (v : Int) : Nat := if v < 0 then 0 else if v > 255 then 255 else v.toNat

/-- The palette indices of an RGBA frame `w × h`; with `dither` by Floyd–Steinberg error
diffusion. Returns the indices and the extended cache. -/
def indexFrame (p : Palette) (cache : Cache) (f : ByteArray) (w h : Nat) (dither : Bool) :
    ByteArray × Cache := Id.run do
  let mut cache := cache
  let mut out := ByteArray.emptyWithCapacity (w * h)
  let mut cur : Array Int := Array.replicate (3 * (w + 2)) 0
  let mut nxt : Array Int := Array.replicate (3 * (w + 2)) 0
  for y in [0:h] do
    for x in [0:w] do
      let i := y * w + x
      if Png.byteAt f (4 * i + 3) < 128 then out := out.push p.colors.size.toUInt8
      else
        let orig := fun (k : Nat) => (Png.byteAt f (4 * i + k)).toNat
        let adj := fun (k : Nat) =>
          if dither then clamp8 ((orig k : Int) + ((cur.getD (3 * (x + 1) + k) 0 + 8) >>> 4))
          else orig k
        let (idx, c') := lookup p cache (adj 0) (adj 1) (adj 2)
        cache := c'
        out := out.push idx.toUInt8
        if dither then
          let pc := p.colors.getD idx 0
          for k in [0:3] do
            let e : Int := (adj k : Int) - chan pc k
            let add := fun (a : Array Int) (j : Nat) (wt : Int) =>
              a.setIfInBounds j (a.getD j 0 + e * wt)
            cur := add cur (3 * (x + 2) + k) 7
            nxt := add nxt (3 * x + k) 3
            nxt := add nxt (3 * (x + 1) + k) 5
            nxt := add nxt (3 * (x + 2) + k) 1
    cur := nxt
    nxt := Array.replicate (3 * (w + 2)) 0
  return (out, cache)

end PILean.Anim.Quant
