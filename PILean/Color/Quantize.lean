import PILean.Core.Image

/-!
# Color quantization

Adaptive palette generation for `.palette` conversion and GIF encoding
(WP13). Median-cut with an exact-palette fast path when the image already
has ≤ `colors` distinct colors (matching Pillow). No dithering in v1
(Floyd–Steinberg comes later).

## Algorithm

1. Promote every pixel to RGBA (`Image.getPixel!`, which also resolves
   `.palette` sources through their own palette), then **fold alpha to
   255** — v1 quantizes on RGB only, so two pixels that differ only in
   alpha are treated as the same color and the output palette is fully
   opaque. (A future version may quantize alpha too.)
2. Deduplicate into `(color, pixel count)` pairs.
3. **Fast path**: if there are at most `colors` distinct colors, the palette
   *is* that exact set — every pixel reconstructs exactly.
4. **Otherwise**: median cut. Starting from one box holding every distinct
   color, repeatedly split the box with the greatest range along its
   widest channel (R, G, or B) at the population-weighted median, until
   there are `colors` boxes (or no box has more than one distinct color
   left). Each box's palette entry is the population-weighted mean color
   of the colors it holds.
5. Every original pixel is remapped to its nearest palette entry
   (`Palette.nearestIndex`; linear scan, see that function's docstring).

`colors` is clamped to `[1, 256]` — `.palette` images store one byte per
pixel, and a 1-color quantize (every pixel maps to the same swatch) is a
legal degenerate case.

Test policy: quantizer output is **never** compared against Pillow's
(different quantizers legitimately differ) — it is property-tested
(palette size ≤ `colors`, bounded mean squared error, exactness for
≤ `colors`-color inputs).
-/

namespace PILean.Image

/-- Pack a color's RGB channels (alpha ignored — see the module docstring)
into one `UInt32` key, for cheap sorting/deduplication. -/
@[inline] private def packRgbKey (c : Color) : UInt32 :=
  (c.r.toUInt32 <<< 16) ||| (c.g.toUInt32 <<< 8) ||| c.b.toUInt32

/-- Inverse of `packRgbKey`; alpha is always restored as opaque. -/
@[inline] private def unpackRgbKey (k : UInt32) : Color :=
  ⟨(k >>> 16).toUInt8, (k >>> 8).toUInt8, k.toUInt8, 255⟩

/-- Collapse a sorted array of packed color keys into `(key, count)` pairs
for each maximal run of equal adjacent keys (i.e. distinct colors with their
pixel frequency), in ascending key order. -/
private def dedupCounts (sorted : Array UInt32) : Array (UInt32 × Nat) := Id.run do
  let n := sorted.size
  let mut out := Array.emptyWithCapacity (min n 256)
  let mut i := 0
  while i < n do
    let k := sorted[i]!
    let mut j := i + 1
    while j < n && sorted[j]! == k do
      j := j + 1
    out := out.push (k, j - i)
    i := j
  return out

/-- `max - min` of `proj` over the colors in `b` (ignoring their counts);
`0` for an empty box. The "range" half of median cut's widest-channel
split heuristic. -/
private def channelRange (b : Array (Color × Nat)) (proj : Color → UInt8) : Nat := Id.run do
  if b.size == 0 then
    return 0
  let mut lo := (proj b[0]!.1).toNat
  let mut hi := lo
  for (c, _) in b do
    let v := (proj c).toNat
    if v < lo then lo := v
    if v > hi then hi := v
  return hi - lo

/-- Which channel (`0` = R, `1` = G, `2` = B) has the greatest range in `b`;
ties favor R then G. -/
private def widestChannel (b : Array (Color × Nat)) : Nat :=
  let rr := channelRange b Color.r
  let gr := channelRange b Color.g
  let br := channelRange b Color.b
  if rr ≥ gr && rr ≥ br then 0
  else if gr ≥ br then 1
  else 2

/-- Sort a box's `(color, count)` pairs ascending by channel `chan`
(`0` = R, `1` = G, `2` = B). -/
private def sortBoxByChannel (b : Array (Color × Nat)) (chan : Nat) : Array (Color × Nat) :=
  match chan with
  | 0 => b.qsort (fun x y => x.1.r < y.1.r)
  | 1 => b.qsort (fun x y => x.1.g < y.1.g)
  | _ => b.qsort (fun x y => x.1.b < y.1.b)

/-- Split a channel-sorted box into two at the population-weighted median
(the running pixel-count total crosses half the box's total population),
clamped so both halves are non-empty. -/
private def splitAtMedian (sorted : Array (Color × Nat)) :
    Array (Color × Nat) × Array (Color × Nat) := Id.run do
  let total := sorted.foldl (fun acc p => acc + p.2) 0
  let half := total / 2
  let mut cum := 0
  let mut splitIdx := sorted.size
  for i in [0:sorted.size] do
    cum := cum + sorted[i]!.2
    if cum ≥ half then
      splitIdx := i + 1
      break
  let clamped := max 1 (min splitIdx (sorted.size - 1))
  return (sorted.extract 0 clamped, sorted.extract clamped sorted.size)

/-- Median-cut split `entries` (distinct colors with pixel counts) into at
most `targetBoxes` boxes: repeatedly split the box with the greatest
widest-channel range until there are enough boxes or no box has more than
one distinct color left. -/
private def medianCut (entries : Array (Color × Nat)) (targetBoxes : Nat) :
    Array (Array (Color × Nat)) := Id.run do
  let mut boxes : Array (Array (Color × Nat)) := #[entries]
  while boxes.size < targetBoxes do
    let mut bestIdx : Option Nat := none
    let mut bestRange : Nat := 0
    for idx in [0:boxes.size] do
      let b := boxes[idx]!
      if b.size > 1 then
        let range := channelRange b (match widestChannel b with
          | 0 => Color.r | 1 => Color.g | _ => Color.b)
        if bestIdx.isNone || range > bestRange then
          bestRange := range
          bestIdx := some idx
    match bestIdx with
    | none => break
    | some idx =>
      let b := boxes[idx]!
      let sorted := sortBoxByChannel b (widestChannel b)
      let (left, right) := splitAtMedian sorted
      boxes := (boxes.set! idx left).push right
  return boxes

/-- A box's palette entry: the population-weighted mean color (opaque). -/
private def averageColor (b : Array (Color × Nat)) : Color := Id.run do
  let mut rs : Nat := 0
  let mut gs : Nat := 0
  let mut bs : Nat := 0
  let mut total : Nat := 0
  for (c, n) in b do
    rs := rs + c.r.toNat * n
    gs := gs + c.g.toNat * n
    bs := bs + c.b.toNat * n
    total := total + n
  if total == 0 then
    return Color.black
  return ⟨UInt8.ofNat (rs / total), UInt8.ofNat (gs / total), UInt8.ofNat (bs / total), 255⟩

/-- Quantize to a `.palette`-mode image with at most `colors` palette
entries (`colors` clamped to `[1, 256]`). Exact palette when the image has
≤ `colors` distinct colors (RGB, alpha folded to opaque — see the module
docstring); median cut otherwise. Works on every input mode, including
`.palette` (re-quantized via RGBA promotion). -/
def quantize (img : Image) (colors : Nat := 256) : Image :=
  let targetColors := min 256 (max 1 colors)
  let width := img.width
  let height := img.height
  let pixelColors : Array Color := Id.run do
    let mut cs := Array.emptyWithCapacity (width * height)
    for y in [0:height] do
      for x in [0:width] do
        cs := cs.push (img.getPixel! x y)
    return cs
  let sorted := (pixelColors.map packRgbKey).qsort (· < ·)
  let distinct := (dedupCounts sorted).map (fun (k, n) => (unpackRgbKey k, n))
  let palette : Palette :=
    if distinct.size ≤ targetColors then
      Palette.ofColors (distinct.map Prod.fst)
    else
      Palette.ofColors ((medianCut distinct targetColors).map averageColor)
  let data : ByteArray := Id.run do
    let mut d := ByteArray.emptyWithCapacity (width * height)
    for c in pixelColors do
      d := d.push (UInt8.ofNat (palette.nearestIndex c))
    return d
  { width, height, mode := .palette, data, palette? := some palette }

end PILean.Image
