import Tests.Framework
import Tests.Prng
import Tests.Praw

/-!
# gif tests

GIF decode (disposal, interlace) and animated encode. Decode is owned by a
later work package (WP15, still a stub); this suite (WP16) exercises
`Gif.encodeFrames`/`Gif.saveGif` structurally (a hand-rolled `ParseM` walker
re-parses the encoded bytes: magic, Logical Screen Descriptor, global color
table, optional NETSCAPE2.0 loop extension, each frame's Graphic Control
Extension + Image Descriptor + LZW sub-blocks, and the trailer), and
round-trips the LZW payload through `Lzw.decompress` for the lossless
(already-`.palette`) path. `gif-encode-export` is the Pillow-oracle case:
see `testdata/golden/gif-encode/gen.py`.
-/

namespace Tests.GifTests

open PILean
open PILean.Binary
open PILean.Compress.Lzw (decompress)

/-! ## A test-only structural walker (independent of `Gif.decode`, which is
still a WP15 stub) -/

/-- One re-parsed frame's Graphic Control Extension + Image Descriptor +
concatenated (de-sub-blocked) LZW payload. -/
structure ParsedFrame where
  delayCs : Nat
  transparentFlag : Bool
  transparentIndex : UInt8
  width : Nat
  height : Nat
  minCodeSize : Nat
  lzwBytes : ByteArray
  deriving Inhabited

/-- The result of walking an entire encoded GIF byte stream. -/
structure ParsedGif where
  magic : String
  width : Nat
  height : Nat
  gctSizeField : Nat
  gctSize : Nat
  gct : Array (UInt8 × UInt8 × UInt8)
  hasNetscape : Bool
  loopCount : Option Nat
  frames : Array ParsedFrame
  deriving Inhabited

/-- Read one `0`-terminated run of length-prefixed sub-blocks, concatenated. -/
private def readSubBlocks : ParseM ByteArray := do
  let mut out := ByteArray.empty
  let mut n ← ParseM.u8
  while n != 0 do
    out := out ++ (← ParseM.take n.toNat)
    n ← ParseM.u8
  return out

/-- Decode 6 raw bytes as ASCII (the GIF magic is always plain ASCII). -/
private def asciiOfBytes (b : ByteArray) : String := Id.run do
  let mut s := ""
  for i in [0:b.size] do
    s := s.push (Char.ofNat (b.get! i).toNat)
  return s

/-- Structurally walk an encoded GIF: header, Logical Screen Descriptor,
global color table, then extensions/image blocks until the `0x3B` trailer.
Fails (`ParseM`'s `DecodeError`) on anything that doesn't parse as
well-formed GIF framing — the test suite's stand-in for a real decoder. -/
private def parseGif : ParseM ParsedGif := do
  let magic := asciiOfBytes (← ParseM.take 6)
  let width ← ParseM.u16le
  let height ← ParseM.u16le
  let flags ← ParseM.u8
  let _bg ← ParseM.u8
  let _aspect ← ParseM.u8
  let gctFlag := (flags &&& 0x80) != 0
  let gctSizeField := (flags &&& 0x07).toNat
  let gctSize := if gctFlag then 2 <<< gctSizeField else 0
  let gctBytes ← ParseM.take (gctSize * 3)
  let gct : Array (UInt8 × UInt8 × UInt8) := Id.run do
    let mut a := Array.emptyWithCapacity gctSize
    for i in [0:gctSize] do
      a := a.push (gctBytes.get! (3 * i), gctBytes.get! (3 * i + 1), gctBytes.get! (3 * i + 2))
    return a
  let mut hasNetscape := false
  let mut loopCount : Option Nat := none
  let mut frames : Array ParsedFrame := #[]
  let mut pendingDelay := 0
  let mut pendingTransFlag := false
  let mut pendingTransIndex : UInt8 := 0
  let mut done := false
  while !done do
    let introducer ← ParseM.u8
    if introducer == 0x21 then
      let label ← ParseM.u8
      if label == 0xF9 then
        let blockSize ← ParseM.u8
        unless blockSize.toNat == 4 do
          throw (.corrupt (← ParseM.pos) s!"GCE block size {blockSize} ≠ 4")
        let packed ← ParseM.u8
        let delay ← ParseM.u16le
        let transIdx ← ParseM.u8
        let terminator ← ParseM.u8
        unless terminator == 0 do
          throw (.corrupt (← ParseM.pos) "GCE missing block terminator")
        pendingDelay := delay.toNat
        pendingTransFlag := (packed &&& 0x01) != 0
        pendingTransIndex := transIdx
      else if label == 0xFF then
        let appIdSize ← ParseM.u8
        let appId ← ParseM.take appIdSize.toNat
        let subData ← readSubBlocks
        if appId == "NETSCAPE2.0".toUTF8 then
          hasNetscape := true
          if subData.size ≥ 3 then
            loopCount := some ((subData.get! 1).toNat ||| ((subData.get! 2).toNat <<< 8))
      else
        let _ ← readSubBlocks
    else if introducer == 0x2C then
      let _left ← ParseM.u16le
      let _top ← ParseM.u16le
      let w ← ParseM.u16le
      let h ← ParseM.u16le
      let imgFlags ← ParseM.u8
      let lctFlag := (imgFlags &&& 0x80) != 0
      if lctFlag then
        let lctSizeField := (imgFlags &&& 0x07).toNat
        let _lct ← ParseM.take (3 * (2 <<< lctSizeField))
      let minCodeSize ← ParseM.u8
      let lzwBytes ← readSubBlocks
      frames := frames.push
        { delayCs := pendingDelay, transparentFlag := pendingTransFlag,
          transparentIndex := pendingTransIndex, width := w.toNat, height := h.toNat,
          minCodeSize := minCodeSize.toNat, lzwBytes }
    else if introducer == 0x3B then
      done := true
    else
      throw (.corrupt (← ParseM.pos) s!"unexpected block introducer {introducer}")
  return { magic, width := width.toNat, height := height.toNat, gctSizeField, gctSize, gct,
           hasNetscape, loopCount, frames }

/-- Parse `bytes` with `parseGif`, failing the test on any parse error and
on trailing bytes after the trailer. -/
private def parseOrFail (bytes : ByteArray) : IO ParsedGif := do
  match ParseM.run parseGif bytes with
  | .error e => fail s!"GIF failed to parse structurally: {e}"
  | .ok g => pure g

/-! ## Fixture builders -/

/-- A `.palette`-mode `width × height` image using every index in
`[0, colors)` (cycling), for a chosen `colors`-entry palette. -/
private def paletteImage (width height colors : Nat) : Image := Id.run do
  let palette := Palette.ofColors <| (Array.range colors).map fun i =>
    Color.rgb (UInt8.ofNat ((i * 53) % 256)) (UInt8.ofNat ((i * 97) % 256))
      (UInt8.ofNat ((i * 181) % 256))
  let mut img : Image :=
    { width, height, mode := .palette,
      data := ByteArray.emptyWithCapacity (width * height), palette? := some palette }
  img := img.modifyData fun d => Id.run do
    let mut d := d
    for y in [0:height] do
      for x in [0:width] do
        d := d.push (UInt8.ofNat ((x + y * width) % colors))
    return d
  return img

/-! ## Structural tests -/

def structuralTests : List TestCase := [
  test "single-frame GIF: magic, LSD, global color table, no NETSCAPE, one frame, clean trailer" do
    let img := paletteImage 4 4 4
    match Gif.encodeFrames #[{ image := img }] with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      let g ← parseOrFail bytes
      assertEq g.magic "GIF89a" "magic"
      assertEq g.width 4 "canvas width"
      assertEq g.height 4 "canvas height"
      assertEq g.gctSize 4 "global color table size"
      assertEq g.hasNetscape false "single frame must not carry a loop extension"
      assertEq g.frames.size 1 "frame count",
  test "multi-frame GIF carries a NETSCAPE2.0 loop extension with the requested loop count" do
    let img := paletteImage 3 3 4
    let frames : Array Gif.Frame := #[{ image := img }, { image := img }, { image := img }]
    match Gif.encodeFrames frames { loopCount := 5 } with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      let g ← parseOrFail bytes
      assertEq g.hasNetscape true "multi-frame must carry a loop extension"
      assertEq g.loopCount (some 5) "loop count"
      assertEq g.frames.size 3 "frame count",
  test "loop count 0 (forever) round trips through the NETSCAPE extension" do
    let img := paletteImage 2 2 2
    match Gif.encodeFrames #[{ image := img }, { image := img }] { loopCount := 0 } with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      let g ← parseOrFail bytes
      assertEq g.loopCount (some 0) "loop count 0 = forever",
  test "sub-block chaining survives an LZW payload longer than 255 bytes" do
    -- 40x40 = 1600 indices over 16 colors is large enough that the LZW
    -- output (even compressed) exceeds 255 bytes, forcing ≥ 2 sub-blocks.
    -- Pseudo-random (SplitMix64) indices, not `paletteImage`'s cycling
    -- pattern, so LZW can't collapse it into a handful of long runs.
    let (img, _) := (SplitMix64.ofSeed 7777).image 40 40 .palette
    match Gif.encodeFrames #[{ image := img }] with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      let g ← parseOrFail bytes
      assertTrue (g.frames[0]!.lzwBytes.size > 255)
        s!"expected a payload spanning multiple sub-blocks, got {g.frames[0]!.lzwBytes.size} bytes"
]

/-! ## Duration → centisecond conversion -/

def durationTests : List TestCase := [
  test "80ms rounds to exactly 8 centiseconds" do
    let img := paletteImage 2 2 2
    match Gif.encodeFrames #[{ image := img, durationMs := 80 }] with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      let g ← parseOrFail bytes
      assertEq g.frames[0]!.delayCs 8 "delay centiseconds",
  test "74ms rounds down to 7 centiseconds, 75ms rounds up to 8" do
    let img := paletteImage 2 2 2
    match Gif.encodeFrames #[{ image := img, durationMs := 74 }, { image := img, durationMs := 75 }] with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      let g ← parseOrFail bytes
      assertEq g.frames[0]!.delayCs 7 "74ms"
      assertEq g.frames[1]!.delayCs 8 "75ms",
  test "a duration beyond UInt16 centiseconds is clamped, not wrapped" do
    let img := paletteImage 2 2 2
    match Gif.encodeFrames #[{ image := img, durationMs := 1000000 }] with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      let g ← parseOrFail bytes
      assertEq g.frames[0]!.delayCs 65535 "clamped to UInt16 max"
]

/-! ## Global palette power-of-two padding -/

def palettePaddingTests : List TestCase := [
  test "a 5-color palette pads the global color table to 8 with black" do
    let img := paletteImage 3 3 5
    match Gif.encodeFrames #[{ image := img }] with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      let g ← parseOrFail bytes
      assertEq g.gctSize 8 "padded global color table size"
      for i in [5:8] do
        assertEq g.gct[i]! ((0 : UInt8), (0 : UInt8), (0 : UInt8)) s!"pad entry {i} is black",
  test "an exact power-of-two palette (16 colors) needs no padding" do
    let img := paletteImage 4 4 16
    match Gif.encodeFrames #[{ image := img }] with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      let g ← parseOrFail bytes
      assertEq g.gctSize 16 "exact power-of-two global color table size"
]

/-! ## Lossless path: the LZW payload self-decodes to the exact remapped
index stream -/

def losslessRoundTripTests : List TestCase := [
  test "already-.palette frames use their palette directly, and the LZW payload decodes exactly" do
    let img := paletteImage 12 9 200
    match Gif.encodeFrames #[{ image := img }] with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      let g ← parseOrFail bytes
      let f := g.frames[0]!
      match decompress f.minCodeSize f.lzwBytes (img.width * img.height) with
      | .error e => fail s!"LZW payload failed to self-decode: {e}"
      | .ok indices => assertBytesEq indices img.data "decoded index stream matches the source exactly",
  test "minCodeSize is the bits actually needed by the palette, clamped to ≥ 2" do
    let img := paletteImage 6 6 3  -- 3 colors need 2 bits, already the GIF floor
    match Gif.encodeFrames #[{ image := img }] with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      let g ← parseOrFail bytes
      assertEq g.frames[0]!.minCodeSize 2 "minCodeSize floor",
  test "17-color palette needs 5-bit minCodeSize" do
    let img := paletteImage 6 6 17
    match Gif.encodeFrames #[{ image := img }] with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      let g ← parseOrFail bytes
      assertEq g.frames[0]!.minCodeSize 5 "minCodeSize for 17 colors"
]

/-! ## Error handling -/

def errorTests : List TestCase := [
  test "an empty frame array is rejected" do
    match Gif.encodeFrames (#[] : Array Gif.Frame) with
    | .error (.invalidArg _) => pure ()
    | .error e => fail s!"wrong error variant: {e}"
    | .ok _ => fail "expected an empty frame array to be rejected",
  test "mismatched frame sizes are rejected with a clear message" do
    let img1 := paletteImage 4 4 4
    let img2 := paletteImage 5 4 4
    match Gif.encodeFrames #[{ image := img1 }, { image := img2 }] with
    | .error (.invalidArg msg) =>
      assertTrue (strContains msg "4x4") s!"error message should mention the canvas size: {msg}"
    | .error e => fail s!"wrong error variant: {e}"
    | .ok _ => fail "expected mismatched frame sizes to be rejected",
  test "a zero-dimension frame is rejected" do
    let img := { width := 0, height := 0, mode := .rgb, data := ByteArray.empty : Image }
    match Gif.encodeFrames #[{ image := img }] with
    | .error (.invalidArg _) => pure ()
    | .error e => fail s!"wrong error variant: {e}"
    | .ok _ => fail "expected a zero-dimension frame to be rejected"
]

/-! ## Pillow oracle export (`testdata/golden/gif-encode/gen.py`) -/

/-- A `width × height` `.rgb` frame: a solid background with a `side ×
side` solid square at `(sx, sy)` — exactly 2 colors, so `Image.quantize`
takes its exact-palette fast path (lossless quantization) when frames are
stacked for the global palette. -/
private def squareFrame (width height sx sy side : Nat) (bg fg : Color) : Image := Id.run do
  let mut img := Image.new width height .rgb bg
  img := img.modifyData fun d => Id.run do
    let mut d := d
    for y in [0:height] do
      for x in [0:width] do
        if sx ≤ x && x < sx + side && sy ≤ y && y < sy + side then
          let off := (y * width + x) * 3
          d := d.set! off fg.r
          d := d.set! (off + 1) fg.g
          d := d.set! (off + 2) fg.b
    return d
  return img

/-- A `size × size` `.rgb` gradient with far more than 256 distinct
colors, forcing `Gif.encodeFrames`'s quantize (lossy) path. -/
private def gradientImage (size : Nat) : Image := Id.run do
  let mut img := Image.new size size .rgb
  img := img.modifyData fun d => Id.run do
    let mut d := d
    for y in [0:size] do
      for x in [0:size] do
        let off := (y * size + x) * 3
        d := d.set! off (UInt8.ofNat (x * 255 / max 1 (size - 1)))
        d := d.set! (off + 1) (UInt8.ofNat (y * 255 / max 1 (size - 1)))
        d := d.set! (off + 2) (UInt8.ofNat (((x + y) * 255 / max 1 (2 * (size - 1))) ))
    return d
  return img

def exportTests : List TestCase := [
  test "gif-encode-export" do
    let outDir : System.FilePath := System.FilePath.mk "testdata" / "out" / "gif-encode"
    IO.FS.createDirAll outDir
    -- (a) single-frame GIF from a 16-color .palette image. A `.praw`
    -- ground truth is written alongside so `gen.py` can check Pillow's
    -- decode is pixel-exact without depending on any other PILean codec.
    let img16 := paletteImage 20 20 16
    Gif.saveGif (outDir / "single_palette16.gif") #[{ image := img16 }]
    Tests.Praw.save (outDir / "single_palette16.praw") img16
    -- (b) 5-frame animated GIF: a 4x4 red square moving diagonally over a
    -- black 24x24 background (2 colors total, exact quantization),
    -- durationMs = 80, loopCount = 0. One `.praw` truth per frame.
    let animFrames : Array Gif.Frame := (Array.range 5).map fun i =>
      { image := squareFrame 24 24 (i * 3) (i * 3) 4 Color.black Color.red, durationMs := 80 }
    Gif.saveGif (outDir / "animated_5frame.gif") animFrames { loopCount := 0 }
    for i in [0:animFrames.size] do
      Tests.Praw.save (outDir / s!"animated_5frame_{i}.praw") animFrames[i]!.image
    -- (c) one RGB gradient frame, forcing the quantize path. `.praw` truth
    -- is the original (pre-quantization) gradient, for the mean-error bound.
    let grad := gradientImage 48
    Gif.saveGif (outDir / "gradient.gif") #[{ image := grad }]
    Tests.Praw.save (outDir / "gradient.praw") grad
    IO.println s!"       [gif-encode-export wrote fixtures under {outDir}]"
]

/-- The `gif` suite (WP15/16). -/
def suite : Tests.Suite :=
  { name := "gif"
    cases := structuralTests ++ durationTests ++ palettePaddingTests ++ losslessRoundTripTests ++
      errorTests ++ exportTests }

end Tests.GifTests
