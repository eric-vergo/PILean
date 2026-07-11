import PILean.Core.Error

/-!
# PNG scanline filters

The five per-row filters (None/Sub/Up/Average/Paeth), encode and decode
(WP11). Paeth predictor selection uses `Int` arithmetic per the spec. This
module is deliberately isolated: `unfilterScanlines ∘ filterScanlines = id`
is property-tested on random rows before any PNG file exists.

Each raw scanline is prefixed by one filter-type byte; `bytesPerRow` is
the *unfiltered* row width (`width * bytesPerPixel`), so the filtered
buffer holds `height * (1 + bytesPerRow)` bytes.
-/

namespace PILean.Png

/-- Filter-choice heuristic for encoding. `.none` writes filter 0
everywhere (valid, fast); `.msad` picks per-row minimum sum of absolute
differences across all five filters (the spec-recommended default). -/
inductive FilterHeuristic where
  | none
  | msad
  deriving Repr, DecidableEq, Inhabited

/-- The PNG Paeth predictor (spec §9.2): pick whichever of `a` (left), `b`
(above), `c` (upper-left) is closest to `a + b - c`, ties broken toward
`a`, then `b`. Distances are computed in `Int` since `a + b - c` can be
negative or exceed 255. -/
private def paeth (a b c : UInt8) : UInt8 :=
  let ai : Int := a.toNat
  let bi : Int := b.toNat
  let ci : Int := c.toNat
  let p := ai + bi - ci
  let pa := (p - ai).natAbs
  let pb := (p - bi).natAbs
  let pc := (p - ci).natAbs
  if pa ≤ pb && pa ≤ pc then a
  else if pb ≤ pc then b
  else c

/-- Remove scanline filters: `raw` is `height` rows of
`1 + bytesPerRow` bytes each; the result is the plain pixel bytes.
`bpp` is the byte distance back to the "left" pixel used by Sub/Average/
Paeth (bit depth 8 only in v1, so `bpp = mode.bytesPerPixel`). Rejects any
filter-type byte outside `0..4` and any input whose size is not a whole
number of rows. -/
def unfilterScanlines (bpp bytesPerRow : Nat) (raw : ByteArray) : Except DecodeError ByteArray := do
  if bytesPerRow == 0 then
    return ByteArray.empty
  let rowLen := 1 + bytesPerRow
  if raw.size % rowLen != 0 then
    throw (.corrupt raw.size
      s!"PNG scanline data size {raw.size} is not a multiple of row length {rowLen}")
  let height := raw.size / rowLen
  let mut d := ByteArray.emptyWithCapacity (bytesPerRow * height)
  for y in [0:height] do
    let rowStart := y * rowLen
    let ft := raw.get! rowStart
    if ft > 4 then
      throw (.corrupt rowStart s!"invalid PNG filter type {ft}")
    for x in [0:bytesPerRow] do
      -- `d.size` is exactly `y * bytesPerRow + x` here: every earlier row is
      -- fully reconstructed and `x` bytes of this row have been pushed, so
      -- the reconstructed neighbors this filter needs are already in `d`.
      let base := d.size
      let filt := raw.get! (rowStart + 1 + x)
      let recon :=
        match ft with
        | 0 => filt
        | 1 => filt + (if x ≥ bpp then d.get! (base - bpp) else 0)
        | 2 => filt + (if y > 0 then d.get! (base - bytesPerRow) else 0)
        | 3 =>
          let a : UInt32 := if x ≥ bpp then (d.get! (base - bpp)).toUInt32 else 0
          let b : UInt32 := if y > 0 then (d.get! (base - bytesPerRow)).toUInt32 else 0
          filt + ((a + b) >>> 1).toUInt8
        | _ =>
          let a := if x ≥ bpp then d.get! (base - bpp) else 0
          let b := if y > 0 then d.get! (base - bytesPerRow) else 0
          let c := if x ≥ bpp && y > 0 then d.get! (base - bytesPerRow - bpp) else 0
          filt + paeth a b c
      d := d.push recon
  return d

/-- Apply filter type `ft` (`0..4`, taken mod 5) to row `y` of `pix`
(unfiltered pixel bytes), returning the `bytesPerRow`-byte filtered row. -/
private def filterRow (ft bpp bytesPerRow y : Nat) (pix : ByteArray) : ByteArray := Id.run do
  let rowStart := y * bytesPerRow
  let mut r := ByteArray.emptyWithCapacity bytesPerRow
  for x in [0:bytesPerRow] do
    let orig := pix.get! (rowStart + x)
    let a := if x ≥ bpp then pix.get! (rowStart + x - bpp) else 0
    let b := if y > 0 then pix.get! (rowStart - bytesPerRow + x) else 0
    let c := if x ≥ bpp && y > 0 then pix.get! (rowStart - bytesPerRow + x - bpp) else 0
    let out :=
      match ft with
      | 0 => orig
      | 1 => orig - a
      | 2 => orig - b
      | 3 => orig - ((a.toUInt32 + b.toUInt32) >>> 1).toUInt8
      | _ => orig - paeth a b c
    r := r.push out
  return r

/-- Force every row to filter type `ft % 5` (`0`=None `1`=Sub `2`=Up
`3`=Average `4`=Paeth) regardless of heuristic. `encodeWith` never calls
this directly — it exists so tests can round-trip each filter type
individually against `unfilterScanlines`. -/
def filterScanlinesForced (bpp bytesPerRow : Nat) (pix : ByteArray) (ft : Nat) : ByteArray :=
  if bytesPerRow == 0 then ByteArray.empty
  else Id.run do
    let ft := ft % 5
    let height := pix.size / bytesPerRow
    let mut out := ByteArray.emptyWithCapacity (height * (1 + bytesPerRow))
    for y in [0:height] do
      out := out.push (UInt8.ofNat ft)
      out := out ++ filterRow ft bpp bytesPerRow y pix
    return out

/-- Sum of absolute distances, scoring each byte as `min (v, 256 - v)`
(treating it as a signed magnitude) — the minimum-sum-of-absolute-
differences heuristic from the PNG spec, used to compare filter
candidates. -/
private def msadScore (row : ByteArray) : UInt32 := Id.run do
  let mut s : UInt32 := 0
  for i in [0:row.size] do
    let v := (row.get! i).toUInt32
    s := s + min v (256 - v)
  return s

/-- Apply scanline filters to plain pixel bytes (inverse of
`unfilterScanlines`). `.none` writes filter type 0 (identity) on every
row; `.msad` picks, independently per row, whichever of the five filter
types minimizes `msadScore`. -/
def filterScanlines (bpp bytesPerRow : Nat) (pix : ByteArray)
    (heuristic : FilterHeuristic := .msad) : ByteArray :=
  match heuristic with
  | .none => filterScanlinesForced bpp bytesPerRow pix 0
  | .msad =>
    if bytesPerRow == 0 then ByteArray.empty
    else Id.run do
      let height := pix.size / bytesPerRow
      let mut out := ByteArray.emptyWithCapacity (height * (1 + bytesPerRow))
      for y in [0:height] do
        let mut bestType := 0
        let mut bestRow := filterRow 0 bpp bytesPerRow y pix
        let mut bestScore := msadScore bestRow
        for ft in [1:5] do
          let cand := filterRow ft bpp bytesPerRow y pix
          let score := msadScore cand
          if score < bestScore then
            bestType := ft
            bestScore := score
            bestRow := cand
        out := out.push (UInt8.ofNat bestType)
        out := out ++ bestRow
      return out

end PILean.Png
