import Tests.Framework
import Tests.Prng
import Tests.Praw

/-!
# png-encode tests

PNG chunks, scanline filters, encode goldens. Owned by WP11.

* `filterRoundTripTests` — `unfilterScanlines ∘ filterScanlines = id` for
  every forced single filter type and the `.msad` heuristic, on random rows
  across `bpp ∈ {1,2,3,4}`, including 1-pixel-wide and 1-row images.
* `chunkRoundTripTests`/`pngsuiteCrcTests` — the chunk/CRC layer: our own
  `appendChunk`/`readChunks` round trip, a corrupted CRC is rejected, a
  handful of vendored PngSuite files that are corrupt at the
  signature/chunk/CRC layer are rejected too.
* `guardTests`/`trnsTests`/`structuralTests` — the encoder's total-except-
  zero-dimension contract, `tRNS` emission, and structural sanity
  (signature, clean self-parse, correct IHDR, exactly one trailing IEND)
  across all five modes.
* `exportTest` ("png-encode-export") — encodes committed `.praw` fixtures
  to `testdata/out/png-encode/*.png`; `testdata/golden/png-encode/gen.py`
  Pillow-opens each and pixel-compares it against the same `.praw`.
-/

namespace Tests.PngEncodeTests

open PILean
open PILean.Png (Chunk)

/-- `n` deterministic bytes from a fresh `SplitMix64` seeded with `seed`. -/
private def randomBytes (seed n : Nat) : ByteArray :=
  ((SplitMix64.ofSeed seed).bytes n).1

/-- The five PNG filter type numbers. -/
private def allFilterTypes : List Nat := [0, 1, 2, 3, 4]

/-- `unfilterScanlines ∘ filterScanlines(Forced) = id` for every forced
filter type and the `.msad` heuristic, across a spread of `bpp`/width/
height combinations including 1-pixel-wide (`width = 1`) and 1-row
(`height = 1`) images. -/
def filterRoundTripTests : List TestCase :=
  let widths := [1, 2, 5, 17]
  let heights := [1, 3, 8]
  let bpps := [1, 2, 3, 4]
  bpps.flatMap fun bpp =>
    widths.flatMap fun width =>
      heights.map fun height =>
        test s!"filter round trip bpp={bpp} {width}x{height}" do
          let bytesPerRow := width * bpp
          let seed := 9000 + bpp * 977 + width * 31 + height
          let pix := randomBytes seed (bytesPerRow * height)
          for ft in allFilterTypes do
            let filtered := PILean.Png.filterScanlinesForced bpp bytesPerRow pix ft
            match PILean.Png.unfilterScanlines bpp bytesPerRow filtered with
            | .error e => fail s!"forced filter type {ft}: unfilterScanlines error: {e}"
            | .ok recon => assertBytesEq recon pix s!"forced filter type {ft} round trip"
          let filteredMsad := PILean.Png.filterScanlines bpp bytesPerRow pix .msad
          match PILean.Png.unfilterScanlines bpp bytesPerRow filteredMsad with
          | .error e => fail s!".msad: unfilterScanlines error: {e}"
          | .ok recon => assertBytesEq recon pix ".msad round trip"

/-- Round-trip and corruption tests for the chunk/CRC layer. -/
def chunkRoundTripTests : List TestCase :=
  [ test "readChunks(appendChunk-built stream) round trip" do
      let ihdrPayload := ByteArray.mk #[0, 0, 0, 4, 0, 0, 0, 3, 8, 2, 0, 0, 0]
      let idatPayload := ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8]
      let built :=
        PILean.Png.appendChunk
          (PILean.Png.appendChunk
            (PILean.Png.appendChunk PILean.Png.signature "IHDR" ihdrPayload)
            "IDAT" idatPayload)
          "IEND" ByteArray.empty
      match PILean.Png.readChunks built with
      | .error e => fail s!"readChunks failed on a stream we built ourselves: {e}"
      | .ok chunks =>
        assertEq chunks.size 3 "chunk count"
        assertEq chunks[0]!.typ "IHDR" "chunk 0 type"
        assertBytesEq chunks[0]!.data ihdrPayload "chunk 0 payload"
        assertEq chunks[1]!.typ "IDAT" "chunk 1 type"
        assertBytesEq chunks[1]!.data idatPayload "chunk 1 payload"
        assertEq chunks[2]!.typ "IEND" "chunk 2 type"
        assertBytesEq chunks[2]!.data ByteArray.empty "chunk 2 payload"

  , test "readChunks rejects a corrupted chunk CRC" do
      let payload := ByteArray.mk #[10, 20, 30, 40, 50]
      let built :=
        PILean.Png.appendChunk
          (PILean.Png.appendChunk PILean.Png.signature "IHDR" payload)
          "IEND" ByteArray.empty
      -- First byte of the IHDR payload, right after signature(8) + len(4) + type(4).
      let idx := 8 + 4 + 4
      let corrupted := built.set! idx ((built.get! idx) ^^^ 0xFF)
      match PILean.Png.readChunks corrupted with
      | .error _ => pure ()
      | .ok _ => fail "expected a CRC-mismatch error"

  , test "readChunks rejects a bad signature" do
      let built := PILean.Png.appendChunk PILean.Png.signature "IEND" ByteArray.empty
      let corrupted := built.set! 1 ((built.get! 1) ^^^ 0xFF)
      match PILean.Png.readChunks corrupted with
      | .error _ => pure ()
      | .ok _ => fail "expected a bad-signature error"

  , test "readChunks rejects a stream missing IEND (no chunks at all)" do
      match PILean.Png.readChunks PILean.Png.signature with
      | .error (.truncated _ _) => pure ()
      | .error e => fail s!"expected DecodeError.truncated, got {e}"
      | .ok _ => fail "expected an error for a stream with no chunks at all"

  , test "readChunks rejects a stream missing IEND (truncated after IHDR)" do
      let built := PILean.Png.appendChunk PILean.Png.signature "IHDR" (ByteArray.mk #[1, 2, 3])
      match PILean.Png.readChunks built with
      | .error (.truncated _ _) => pure ()
      | .error e => fail s!"expected DecodeError.truncated, got {e}"
      | .ok _ => fail "expected an error for a stream truncated right after IHDR"

  , test "readChunks rejects trailing garbage after IEND" do
      let built :=
        (PILean.Png.appendChunk PILean.Png.signature "IEND" ByteArray.empty).push 0
      match PILean.Png.readChunks built with
      | .error _ => pure ()
      | .ok _ => fail "expected an error for trailing garbage after IEND"
  ]

/-- Vendored PngSuite corpus directory. -/
def pngsuiteDir : System.FilePath := System.FilePath.mk "testdata" / "corpus" / "pngsuite"

/-- These PngSuite "x"-prefixed corrupt files are broken at the
signature/chunk/CRC layer specifically (as opposed to being merely
semantically invalid, which only a full decoder — WP12 — could catch), so
`readChunks` alone must already reject them. -/
def pngsuiteCrcTests : List TestCase :=
  ["xs1n0g01.png", "xs2n0g01.png", "xcrn0g04.png", "xhdn0g08.png"].map fun (name : String) =>
    test s!"pngsuite {name} fails at the chunk/CRC/signature layer" do
      let bytes ← IO.FS.readBinFile (pngsuiteDir / name)
      match PILean.Png.readChunks bytes with
      | .error _ => pure ()
      | .ok _ => fail s!"{name}: expected readChunks to reject this corrupt file"

/-- The encoder's guard rails: zero dimensions and a `.palette` image with
no palette both fail with `EncodeError.invalidArg` rather than panicking. -/
def guardTests : List TestCase :=
  [ test "zero-width image is EncodeError.invalidArg" do
      let img : Image := { width := 0, height := 5, mode := .gray, data := ByteArray.empty }
      match PILean.Png.encode img with
      | .error (.invalidArg _) => pure ()
      | .error e => fail s!"expected invalidArg, got {e}"
      | .ok _ => fail "expected an error for a zero-width image"

  , test "zero-height image is EncodeError.invalidArg" do
      let img : Image := { width := 5, height := 0, mode := .rgb, data := ByteArray.empty }
      match PILean.Png.encode img with
      | .error (.invalidArg _) => pure ()
      | .error e => fail s!"expected invalidArg, got {e}"
      | .ok _ => fail "expected an error for a zero-height image"

  , test "palette image without a palette is EncodeError.invalidArg" do
      let img : Image :=
        { width := 2, height := 2, mode := .palette
          data := ByteArray.mk #[0, 0, 0, 0], palette? := none }
      match PILean.Png.encode img with
      | .error (.invalidArg _) => pure ()
      | .error e => fail s!"expected invalidArg, got {e}"
      | .ok _ => fail "expected an error for a palette image without a palette"
  ]

/-- Does `chunks` contain a chunk of type `typ`? -/
private def hasChunk (chunks : Array Chunk) (typ : String) : Bool :=
  chunks.any fun c => c.typ == typ

/-- `tRNS` is emitted iff some palette entry has alpha `< 255`. -/
def trnsTests : List TestCase :=
  [ test "opaque palette produces no tRNS chunk" do
      let img := Image.new 3 3 .palette (Color.rgb 10 20 30)
      match PILean.Png.encode img with
      | .error e => fail s!"encode failed: {e}"
      | .ok bytes =>
        match PILean.Png.readChunks bytes with
        | .error e => fail s!"readChunks failed on our own output: {e}"
        | .ok chunks => assertTrue (!hasChunk chunks "tRNS") "no tRNS chunk expected"

  , test "palette with a transparent entry produces a tRNS chunk" do
      let pal := Palette.ofColors #[Color.rgba 1 2 3 0, Color.rgba 4 5 6 255]
      let img : Image :=
        { width := 2, height := 1, mode := .palette
          data := ByteArray.mk #[0, 1], palette? := some pal }
      match PILean.Png.encode img with
      | .error e => fail s!"encode failed: {e}"
      | .ok bytes =>
        match PILean.Png.readChunks bytes with
        | .error e => fail s!"readChunks failed on our own output: {e}"
        | .ok chunks =>
          assertTrue (hasChunk chunks "tRNS") "a tRNS chunk was expected"
          match chunks.find? fun c => c.typ == "tRNS" with
          | none => fail "unreachable: hasChunk found one"
          | some trns => assertBytesEq trns.data (ByteArray.mk #[0, 255]) "tRNS payload"
  ]

/-- PNG color type for each `Mode`, mirroring `PILean.Png.Encode`'s
(private) `colorTypeOf`, for verifying `IHDR` from the outside. -/
private def expectedColorType : Mode → UInt8
  | .gray => 0
  | .rgb => 2
  | .palette => 3
  | .grayAlpha => 4
  | .rgba => 6

/-- Parse `IHDR`'s 13-byte payload into `(width, height, bitDepth,
colorType)`. -/
private def parseIhdr (payload : ByteArray) : Except DecodeError (UInt32 × UInt32 × UInt8 × UInt8) :=
  PILean.Binary.ParseM.run (data := payload) do
    let w ← PILean.Binary.ParseM.u32be
    let h ← PILean.Binary.ParseM.u32be
    let bd ← PILean.Binary.ParseM.u8
    let ct ← PILean.Binary.ParseM.u8
    return (w, h, bd, ct)

/-- Structural sanity for the encoder's total (non-error) path, across
every mode and both a normal and a `1×1` size: the output starts with the
signature, our own `readChunks` parses it cleanly, `IHDR` fields are
correct, and there is exactly one `IEND`, at the end. This is the
"self round trip is NOT possible yet" fallback the work package calls
for — no PNG decoder exists yet to check pixel content against. -/
def structuralTests : List TestCase :=
  let modes : List Mode := [.gray, .grayAlpha, .rgb, .rgba, .palette]
  let sizes : List (Nat × Nat) := [(9, 5), (1, 1)]
  modes.flatMap fun mode =>
    sizes.map fun (w, h) =>
      test s!"encode structural sanity ({mode}, {w}x{h})" do
        let (img, _) := (SplitMix64.ofSeed (600 + mode.bytesPerPixel * 131 + w * 17 + h)).image w h mode
        match PILean.Png.encode img with
        | .error e => fail s!"{mode} {w}x{h}: encode failed: {e}"
        | .ok bytes =>
          assertBytesEq (bytes.extract 0 8) PILean.Png.signature s!"{mode} {w}x{h}: signature"
          match PILean.Png.readChunks bytes with
          | .error e => fail s!"{mode} {w}x{h}: readChunks failed on our own output: {e}"
          | .ok chunks =>
            assertTrue (chunks.size ≥ 3) s!"{mode} {w}x{h}: expected ≥ 3 chunks (IHDR/IDAT/IEND)"
            assertEq chunks[0]!.typ "IHDR" s!"{mode} {w}x{h}: first chunk type"
            assertEq chunks[chunks.size - 1]!.typ "IEND" s!"{mode} {w}x{h}: last chunk type"
            let iendCount := (chunks.filter fun c => c.typ == "IEND").size
            assertEq iendCount 1 s!"{mode} {w}x{h}: exactly one IEND chunk"
            match parseIhdr chunks[0]!.data with
            | .error e => fail s!"{mode} {w}x{h}: malformed IHDR payload: {e}"
            | .ok (width, height, bitDepth, colorType) =>
              assertEq width (UInt32.ofNat w) s!"{mode} {w}x{h}: IHDR width"
              assertEq height (UInt32.ofNat h) s!"{mode} {w}x{h}: IHDR height"
              assertEq bitDepth 8 s!"{mode} {w}x{h}: IHDR bit depth"
              assertEq colorType (expectedColorType mode) s!"{mode} {w}x{h}: IHDR color type"

/-- Directory the export test writes PNGs into; `testdata/golden/png-encode/gen.py`
Pillow-opens everything here. -/
def exportOutDir : System.FilePath := System.FilePath.mk "testdata" / "out" / "png-encode"

/-- `(.praw fixture, expected mode)` pairs the export test encodes, chosen
to cover all four exported modes (`.grayAlpha` is exercised by the other
suites above but not by the Pillow oracle — see the module docstring) and
all three required sizes (`16×16`, `33×17`, `1×1`) with varied pixel
content (checkerboard, noise, and a flat fill). -/
private def exportCases : List (String × Mode) :=
  [ ("checker8_l_16x16", .gray), ("noise_l_33x17", .gray), ("flat_l_1x1", .gray)
  , ("checker8_rgb_16x16", .rgb), ("noise_rgb_33x17", .rgb), ("flat_rgb_1x1", .rgb)
  , ("checker8_rgba_16x16", .rgba), ("noise_rgba_33x17", .rgba), ("flat_rgba_1x1", .rgba)
  , ("checker8_p_16x16", .palette), ("noise_p_33x17", .palette), ("flat_p_1x1", .palette)
  ]

/-- Encodes every fixture in `exportCases` (loaded via `Tests.Praw.load`
from the committed golden `.praw`) and writes the PNG to
`testdata/out/png-encode/<name>.png`. `testdata/golden/png-encode/gen.py`
then Pillow-opens each file and pixel-compares it against the same
`.praw`, closing the loop with an independent decoder. -/
def exportTest : TestCase :=
  test "png-encode-export" do
    IO.FS.createDirAll exportOutDir
    for (name, mode) in exportCases do
      let path := goldenDir / s!"{name}.praw"
      let img ← Tests.Praw.load path
      assertEq img.mode mode s!"{name}: fixture mode"
      match PILean.Png.encode img with
      | .error e => fail s!"{name}: encode failed: {e}"
      | .ok bytes => IO.FS.writeBinFile (exportOutDir / s!"{name}.png") bytes

/-- The `png-encode` suite (WP11). -/
def suite : Tests.Suite :=
  { name := "png-encode"
    cases :=
      filterRoundTripTests ++ chunkRoundTripTests ++ pngsuiteCrcTests ++
      guardTests ++ trnsTests ++ structuralTests ++ [exportTest] }

end Tests.PngEncodeTests
