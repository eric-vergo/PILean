import PILean.Core.Color

/-!
# Palettes

Indexed-color palettes for `.palette`-mode images: up to 256 RGBA entries
stored flat in a `ByteArray` (4 bytes per entry).
-/

namespace PILean

/-- An indexed-color palette: up to 256 RGBA entries, 4 bytes each, stored
flat in `entries`. -/
structure Palette where
  entries : ByteArray
  deriving Inhabited

namespace Palette

/-- Number of entries. -/
def size (p : Palette) : Nat := p.entries.size / 4

/-- Append an entry (callers must keep the palette at ≤ 256 entries). -/
def push (p : Palette) (c : Color) : Palette :=
  ⟨p.entries |>.push c.r |>.push c.g |>.push c.b |>.push c.a⟩

/-- The color of entry `i`. Panics if out of range (palette indices in image
data must always be valid — a violation is a PILean bug). -/
def get! (p : Palette) (i : Nat) : Color :=
  if i < p.size then
    ⟨p.entries.get! (4 * i), p.entries.get! (4 * i + 1),
     p.entries.get! (4 * i + 2), p.entries.get! (4 * i + 3)⟩
  else
    panic! s!"Palette.get!: index {i} out of range (size {p.size})"

/-- Build a palette from an array of colors (truncated to 256 entries). -/
def ofColors (cs : Array Color) : Palette :=
  (cs.toSubarray 0 (min cs.size 256)).foldl push
    { entries := ByteArray.emptyWithCapacity (4 * min cs.size 256) }

/-- Index of the entry nearest to `c` in squared RGB distance (alpha
ignored). Linear scan; 0 for an empty palette. -/
def nearestIndex (p : Palette) (c : Color) : Nat := Id.run do
  let sq (a b : UInt8) : Nat :=
    let d := if a ≥ b then (a - b).toNat else (b - a).toNat
    d * d
  let mut best := 0
  let mut bestDist := 1000000
  for i in [0:p.size] do
    let e := p.get! i
    let dist := sq e.r c.r + sq e.g c.g + sq e.b c.b
    if dist < bestDist then
      best := i
      bestDist := dist
  return best

/-- The 216-color web-safe palette (all combinations of
0, 51, 102, 153, 204, 255 per channel). The default palette for new
`.palette`-mode images. -/
def webSafe : Palette := Id.run do
  let levels : Array UInt8 := #[0, 51, 102, 153, 204, 255]
  let mut p : Palette := { entries := ByteArray.emptyWithCapacity (216 * 4) }
  for r in levels do
    for g in levels do
      for b in levels do
        p := p.push ⟨r, g, b, 255⟩
  return p

end Palette

end PILean
