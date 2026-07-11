import PILean.Core.Mode
import PILean.Core.Color
import PILean.Core.Geometry
import PILean.Core.Palette

/-!
# The Image type

A raster image: `width × height` pixels stored row-major in a `ByteArray`
with `mode.bytesPerPixel` bytes per pixel, top-left origin, **no row
padding**.

Invariants (by convention — maintained by constructors and codecs, checked
by `Image.validate` in tests, not by proofs):
* `data.size = width * height * mode.bytesPerPixel`
* `mode = .palette → palette?.isSome`

## Mutation and performance

`Image.modifyData` is *the* mutation primitive: it steals the buffer so the
callback receives it with reference count 1, which makes `ByteArray.set!`
mutate in place. All in-place algorithms must route through it. Never write
`{ img with data := img.data.set! i v }` — that keeps a second live
reference and copies the whole buffer per write.
-/

namespace PILean

/-- A raster image. See the module docstring for invariants and the
mutation discipline. `info` carries ancillary metadata (gamma, DPI, text
chunks, …) as key/value pairs. -/
structure Image where
  width : Nat
  height : Nat
  mode : Mode
  data : ByteArray
  palette? : Option Palette := none
  info : List (String × String) := []
  deriving Inhabited

namespace Image

/-- Do the size/mode/palette invariants hold? (Test-time check.) -/
def validate (img : Image) : Bool :=
  img.data.size == img.width * img.height * img.mode.bytesPerPixel &&
  (img.mode != .palette || img.palette?.isSome)

/-- Is `(x, y)` inside the image? -/
def inBounds (img : Image) (x y : Int) : Bool :=
  0 ≤ x && x < (img.width : Int) && 0 ≤ y && y < (img.height : Int)

/-- Apply `f` to the backing buffer. The buffer is *stolen* — replaced by an
empty one before `f` runs — so `f` receives it unshared (refcount 1) and
`ByteArray.set!` inside `f` mutates in place. THE mutation primitive. -/
@[inline] def modifyData (img : Image) (f : ByteArray → ByteArray) : Image :=
  let data := img.data
  let img' := { img with data := ByteArray.empty }
  { img' with data := f data }

/-- Encode `c` in the storage format of `mode`, resolving `.palette` via
nearest palette entry. -/
private def pixelBytes (mode : Mode) (palette? : Option Palette) (c : Color) : Array UInt8 :=
  match mode with
  | .gray => #[c.luma]
  | .grayAlpha => #[c.luma, c.a]
  | .rgb => #[c.r, c.g, c.b]
  | .rgba => #[c.r, c.g, c.b, c.a]
  | .palette =>
    match palette? with
    | some p => #[UInt8.ofNat (p.nearestIndex c)]
    | none => panic! "PILean.Image: palette-mode image without palette"

/-- Create a solid-color image. `.palette`-mode images get the
`Palette.webSafe` palette. -/
def new (width height : Nat) (mode : Mode := .rgb) (fill : Color := Color.black) : Image :=
  let palette? := if mode == .palette then some Palette.webSafe else none
  let px := pixelBytes mode palette? fill
  let data := Id.run do
    let mut b := ByteArray.emptyWithCapacity (width * height * mode.bytesPerPixel)
    for _ in [0:width * height] do
      for v in px do
        b := b.push v
    return b
  { width, height, mode, data, palette? }

/-- Read a pixel, promoted to RGBA `Color` (grayscale gives `r = g = b`,
palette entries are resolved). Returns `none` out of bounds. -/
def getPixel? (img : Image) (x y : Int) : Option Color :=
  if img.inBounds x y then
    let off := (y.toNat * img.width + x.toNat) * img.mode.bytesPerPixel
    some <| match img.mode with
      | .gray => Color.gray (img.data.get! off)
      | .grayAlpha => ⟨img.data.get! off, img.data.get! off, img.data.get! off,
                       img.data.get! (off + 1)⟩
      | .rgb => ⟨img.data.get! off, img.data.get! (off + 1), img.data.get! (off + 2), 255⟩
      | .rgba => ⟨img.data.get! off, img.data.get! (off + 1), img.data.get! (off + 2),
                  img.data.get! (off + 3)⟩
      | .palette =>
        match img.palette? with
        | some p => p.get! (img.data.get! off).toNat
        | none => panic! "PILean.Image: palette-mode image without palette"
  else none

/-- Read a pixel; panics out of bounds (programmer-error path — prefer
`getPixel?` unless bounds are already established). -/
def getPixel! (img : Image) (x y : Int) : Color :=
  match img.getPixel? x y with
  | some c => c
  | none => panic! s!"Image.getPixel!: ({x}, {y}) out of bounds for {img.width}×{img.height}"

/-- Write a pixel, converting `c` to the image's mode (grayscale via
`Color.luma`, palette via nearest entry — the latter is a linear scan and
documented slow). **Silently no-ops out of bounds** — this is the clipping
primitive all drawing builds on. -/
def putPixel (img : Image) (x y : Int) (c : Color) : Image :=
  if img.inBounds x y then
    let bpp := img.mode.bytesPerPixel
    let off := (y.toNat * img.width + x.toNat) * bpp
    let px := pixelBytes img.mode img.palette? c
    img.modifyData fun data => Id.run do
      let mut d := data
      for i in [0:bpp] do
        d := d.set! (off + i) px[i]!
      return d
  else img

/-- Raw palette index at `(x, y)` for `.palette`-mode images; `none` out of
bounds or for other modes. -/
def getIndex? (img : Image) (x y : Int) : Option UInt8 :=
  if img.mode == .palette && img.inBounds x y then
    some (img.data.get! (y.toNat * img.width + x.toNat))
  else none

/-- Set the raw palette index at `(x, y)`; no-op out of bounds or for
non-palette modes. -/
def setIndex (img : Image) (x y : Int) (i : UInt8) : Image :=
  if img.mode == .palette && img.inBounds x y then
    let off := y.toNat * img.width + x.toNat
    img.modifyData (·.set! off i)
  else img

/-- Apply `f` to every pixel via RGBA promotion. On `.palette` images this
maps the palette entries, not the pixels. -/
def map (img : Image) (f : Color → Color) : Image :=
  match img.mode, img.palette? with
  | .palette, some p =>
    let entries := Id.run do
      let mut e := ByteArray.emptyWithCapacity p.entries.size
      for i in [0:p.size] do
        let c := f (p.get! i)
        e := e.push c.r |>.push c.g |>.push c.b |>.push c.a
      return e
    { img with palette? := some { entries := entries } }
  | .palette, none => img
  | .gray, _ =>
    img.modifyData fun data => Id.run do
      let mut d := data
      for i in [0:d.size] do
        d := d.set! i (f (Color.gray (d.get! i))).luma
      return d
  | .grayAlpha, _ =>
    img.modifyData fun data => Id.run do
      let mut d := data
      let n := d.size / 2
      for i in [0:n] do
        let off := 2 * i
        let c := f ⟨d.get! off, d.get! off, d.get! off, d.get! (off + 1)⟩
        d := d.set! off c.luma
        d := d.set! (off + 1) c.a
      return d
  | .rgb, _ =>
    img.modifyData fun data => Id.run do
      let mut d := data
      let n := d.size / 3
      for i in [0:n] do
        let off := 3 * i
        let c := f ⟨d.get! off, d.get! (off + 1), d.get! (off + 2), 255⟩
        d := d.set! off c.r
        d := d.set! (off + 1) c.g
        d := d.set! (off + 2) c.b
      return d
  | .rgba, _ =>
    img.modifyData fun data => Id.run do
      let mut d := data
      let n := d.size / 4
      for i in [0:n] do
        let off := 4 * i
        let c := f ⟨d.get! off, d.get! (off + 1), d.get! (off + 2), d.get! (off + 3)⟩
        d := d.set! off c.r
        d := d.set! (off + 1) c.g
        d := d.set! (off + 2) c.b
        d := d.set! (off + 3) c.a
      return d

end Image

end PILean
