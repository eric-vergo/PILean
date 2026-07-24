import PILean
import Examples.PixelSort.Sort

/-!
# Verified pixel sort — proof-to-pixels plumbing

Renders the animation whose frames are successive applications of the
*proven* `pass` (see `Examples.PixelSort.Proofs`):

* The source image is quantized to ≤ 254 colors **once, up front**, then
  black and white are appended to the palette — every frame draws from
  this one fixed palette, so the GIF encodes losslessly and the
  permutation invariant (`passes_perm`) is visible as an identical color
  histogram in every frame.
* Each animation step applies `pass` to every pixel column (key = the
  luma of the pixel's palette color), so bright pixels sink like sediment.
* Captions are drawn on a *copy* of the sort state — the text never
  enters the data being sorted.
-/

namespace Examples.PixelSort

open PILean

/-- Luma key for each palette index, precomputed once. -/
private def lumaTable (p : Palette) : Array Nat := Id.run do
  let mut t := Array.emptyWithCapacity p.size
  for i in [0:p.size] do
    t := t.push (p.get! i).luma.toNat
  return t

/-- Apply one `pass` (the proven one — `Examples.PixelSort.pass`) to every
column of a `.palette`-mode image, top-to-bottom, keyed by palette luma. -/
def stepImage (luma : Array Nat) (img : Image) : Image :=
  let w := img.width
  let h := img.height
  img.modifyData fun data => Id.run do
    let mut d := data
    for x in [0:w] do
      -- build the column top→bottom (cons bottom-up so the head is the top)
      let mut col : List (Nat × UInt8) := []
      let mut y := h
      while y > 0 do
        y := y - 1
        let i := d.get! (y * w + x)
        col := (luma[i.toNat]!, i) :: col
      -- one proven bubble pass
      let sorted := pass col
      let mut yw := 0
      for (_, i) in sorted do
        d := d.set! (yw * w + x) i
        yw := yw + 1
    return d

/-- The sort state with a caption bar appended *below* the art (never
overlaid): every sorted pixel stays visible in every frame, so the
permutation invariant (`passes_perm`) can be observed directly from the
GIF — each frame's art region is the identical pixel multiset. -/
def frameWithCaption (state : Image) (label : String) : Image :=
  let barH := 18
  let blackIdx : UInt8 := match state.palette? with
    | some p => UInt8.ofNat (p.nearestIndex Color.black)
    | none => 0
  let bar := ByteArray.replicateByte (state.width * barH) blackIdx
  let f : Image :=
    { width := state.width, height := state.height + barH, mode := .palette
      data := state.data ++ bar, palette? := state.palette? }
  Draw.text f ⟨4, state.height + 1⟩ label Color.white

/-- Quantize to 254 colors and append true black and white to the palette
(indices 254/255), so captions have exact colors to snap to. -/
def prepare (img : Image) : Image :=
  let q := img.quantize 254
  match q.palette? with
  | some p => { q with palette? := some ((p.push Color.black).push Color.white) }
  | none => q

/-- The full animation: one frame per `stride` passes, plus a held final
frame. `sorted_passes` proves `height` passes suffice, so that is the
total; every frame's caption cites the theorem certifying it. -/
def gifFrames (src : Image) (stride : Nat := 2) : Array Gif.Frame := Id.run do
  let base := prepare src
  let total := base.height  -- sorted_passes: length passes always suffice
  let luma := match base.palette? with
    | some p => lumaTable p
    | none => #[]
  let mut frames : Array Gif.Frame := Array.emptyWithCapacity (total / stride + 2)
  let mut state := base
  frames := frames.push
    { image := frameWithCaption state "pass 0: original (perm: passes_perm)"
      durationMs := 800 }
  let mut k := 0
  while k < total do
    for _ in [0:stride] do
      state := stepImage luma state
    k := k + stride
    let label :=
      if k < total then
        s!"pass {k}/{total} (perm: passes_perm)"
      else
        "sorted: proved (sorted_passes) - QED"
    frames := frames.push
      { image := frameWithCaption state label
        durationMs := if k < total then 60 else 2500 }
  return frames

end Examples.PixelSort
