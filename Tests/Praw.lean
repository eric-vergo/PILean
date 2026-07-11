import PILean
import PILean.Binary.Reader
import PILean.Binary.Writer

/-!
# `.praw` fixture format

`.praw` is the test-only pixel-truth interchange format shared with the
Python oracle (`tests/py/praw.py`): a minimal container that stores exactly
what a `PILean.Image` holds in memory, so any codec's decoder output can be
compared byte-for-byte against a fixed value without depending on any
*other* PILean codec.

Byte layout (all multi-byte integers little-endian):

```
offset  size  field
0       4     magic, ASCII "PRAW"
4       1     mode byte: 0=gray 1=grayAlpha 2=rgb 3=rgba 4=palette
5       4     width  (u32le)
9       4     height (u32le)
13      ...   [mode==4 only] paletteSize (u16le), then paletteSize * 4
              bytes of RGBA palette entries
...     ...   pixel data: width*height*bytesPerPixel(mode) bytes,
              row-major, top-to-bottom, tightly packed (no row padding)
```

This must match the Python writer in `tests/py/praw.py` byte-for-byte.
-/

namespace Tests.Praw

open PILean PILean.Binary

/-- The `.praw` magic bytes, ASCII `"PRAW"`. -/
def magic : ByteArray := ByteArray.mk #[0x50, 0x52, 0x41, 0x57]

/-- The one-byte mode code used on disk. Must match `tests/py/praw.py`'s
`MODE_*` constants and PILean's `Mode` order. -/
def modeCode : Mode → UInt8
  | .gray => 0
  | .grayAlpha => 1
  | .rgb => 2
  | .rgba => 3
  | .palette => 4

/-- Inverse of `modeCode`; `none` for unrecognized bytes. -/
def modeOfCode? : UInt8 → Option Mode
  | 0 => some .gray
  | 1 => some .grayAlpha
  | 2 => some .rgb
  | 3 => some .rgba
  | 4 => some .palette
  | _ => none

/-- Parse a `.praw` file body (see the module docstring for the layout). -/
def parser : ParseM Image := do
  ParseM.expectBytes magic "praw"
  let mc ← ParseM.u8
  let mode ← match modeOfCode? mc with
    | some m => pure m
    | none => throw (.corrupt (← ParseM.pos) s!"praw: unknown mode byte {mc}")
  let width ← ParseM.u32le
  let height ← ParseM.u32le
  let palette? ← do
    if mode == .palette then
      let n ← ParseM.u16le
      let raw ← ParseM.take (4 * n.toNat)
      pure (some (Palette.mk raw))
    else
      pure none
  let dataSize := width.toNat * height.toNat * mode.bytesPerPixel
  let data ← ParseM.take dataSize
  return { width := width.toNat, height := height.toNat, mode, data, palette? }

/-- Load a `.praw` fixture from disk. Failures (bad magic, truncation,
unknown mode byte) surface as `IO.userError`. -/
def load (path : System.FilePath) : IO Image := do
  let bytes ← IO.FS.readBinFile path
  match ParseM.run parser bytes with
  | .ok img => pure img
  | .error e => throw (IO.userError s!"Tests.Praw.load {path}: {e}")

/-- Encode an `Image` as `.praw` bytes (see the module docstring for the
layout). Inverse of `parser` (up to the palette's exact byte count, which
round-trips exactly since `Palette.entries` is already 4 bytes/entry). -/
def encode (img : Image) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (13 + img.data.size + 4 * 256)
  b := b ++ magic
  b := b.push (modeCode img.mode)
  b := b.pushU32le (UInt32.ofNat img.width)
  b := b.pushU32le (UInt32.ofNat img.height)
  if img.mode == .palette then
    let p := img.palette?.getD { entries := ByteArray.empty }
    b := b.pushU16le (UInt16.ofNat p.size)
    b := b ++ p.entries
  b := b ++ img.data
  return b

/-- Save an `Image` as a `.praw` fixture. Inverse of `load`. -/
def save (path : System.FilePath) (img : Image) : IO Unit :=
  IO.FS.writeBinFile path (encode img)

end Tests.Praw
