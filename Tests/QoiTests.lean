import Tests.Framework
import Tests.Prng
import Tests.Praw

/-!
# qoi tests

QOI encode/decode round trip and goldens. Owned by WP13.

`testdata/golden/qoi/` holds real Pillow-encoded `.qoi` reference files
(`testdata/golden/qoi/gen.py`) plus their `.praw` ground truth, so PILean's
decoder is checked against an independent encoder, not just against itself.
The hand-crafted op tests below additionally pin exact encoded byte counts,
verified against the spec by hand and cross-checked against Pillow's own
QOI writer on the same pixel data (see WP13 notes) — a strong signal that
op selection (`RUN`/`DIFF`/`LUMA`/`INDEX`/`RGB`/`RGBA`) matches the
reference algorithm exactly, not just that round trips happen to work.
-/

namespace Tests.QoiTests

open PILean

/-- Read a committed `.qoi` fixture from `testdata/golden/qoi/`. -/
private def qoiFixture (name : String) : IO ByteArray :=
  IO.FS.readBinFile (Tests.goldenDir / "qoi" / (name ++ ".qoi"))

/-- Load the `.praw` ground truth alongside a `.qoi` fixture. -/
private def qoiTruth (name : String) : IO Image :=
  Tests.Praw.load (Tests.goldenDir / "qoi" / (name ++ ".praw"))

/-- Build a `.rgb` image from a flat list of RGB triples, row-major. -/
private def rgbImage (width height : Nat) (px : List (UInt8 × UInt8 × UInt8)) : Image :=
  Id.run do
    let mut img := Image.new width height .rgb
    let mut i := 0
    for y in [0:height] do
      for x in [0:width] do
        if h : i < px.length then
          let (r, g, b) := px[i]
          img := img.putPixel x y (Color.rgb r g b)
        i := i + 1
    return img

/-- Compare pixel colors only (ignoring `mode`, since encoding a non-rgb/rgba
image legitimately changes it — QOI has no gray/palette encoding). -/
private def assertColorsEq (actual expected : Image) (label : String := "image") : IO Unit := do
  unless actual.width == expected.width && actual.height == expected.height do
    fail (s!"{label}: size mismatch — got {actual.width}×{actual.height}, " ++
      s!"expected {expected.width}×{expected.height}")
  for y in [0:actual.height] do
    for x in [0:actual.width] do
      assertEq (actual.getPixel! x y) (expected.getPixel! x y) s!"{label} ({x},{y})"

/-- Every strict prefix of `bytes` must fail to decode (never panic). QOI
always ends with a fixed 8-byte end marker, so any strict prefix is missing
at least part of it (or earlier structure) and must be rejected. -/
private def truncationFuzz (bytes : ByteArray) : IO Unit := do
  for n in [0:bytes.size] do
    match Qoi.decode (bytes.extract 0 n) with
    | .ok _ => fail s!"prefix of length {n} unexpectedly decoded"
    | .error _ => pure ()

def referenceTests : List TestCase := [
  test "ref_rgb.qoi decodes to its .praw truth" do
    let bytes ← qoiFixture "ref_rgb"
    let truth ← qoiTruth "ref_rgb"
    match Qoi.decode bytes with
    | .error e => fail s!"decode failed: {e}"
    | .ok img => assertImagesEq img truth "ref_rgb",
  test "ref_rgba.qoi decodes to its .praw truth" do
    let bytes ← qoiFixture "ref_rgba"
    let truth ← qoiTruth "ref_rgba"
    match Qoi.decode bytes with
    | .error e => fail s!"decode failed: {e}"
    | .ok img => assertImagesEq img truth "ref_rgba",
  test "ref_1x1.qoi decodes to its .praw truth" do
    let bytes ← qoiFixture "ref_1x1"
    let truth ← qoiTruth "ref_1x1"
    match Qoi.decode bytes with
    | .error e => fail s!"decode failed: {e}"
    | .ok img =>
      assertEq img.width 1 "width"
      assertEq img.height 1 "height"
      assertImagesEq img truth "ref_1x1"
]

def roundTripTests : List TestCase := [
  test "rgb round trips (1x1)" do
    let (img, _) := (SplitMix64.ofSeed 4001).image 1 1 .rgb
    match Qoi.encode img with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      match Qoi.decode bytes with
      | .error e => fail s!"decode failed: {e}"
      | .ok img' => assertImagesEq img' img "rgb 1x1",
  test "rgb round trips (33x17)" do
    let (img, _) := (SplitMix64.ofSeed 4002).image 33 17 .rgb
    match Qoi.encode img with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      match Qoi.decode bytes with
      | .error e => fail s!"decode failed: {e}"
      | .ok img' => assertImagesEq img' img "rgb 33x17",
  test "rgba round trips (1x1)" do
    let (img, _) := (SplitMix64.ofSeed 4003).image 1 1 .rgba
    match Qoi.encode img with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      match Qoi.decode bytes with
      | .error e => fail s!"decode failed: {e}"
      | .ok img' => assertImagesEq img' img "rgba 1x1",
  test "rgba round trips (33x17)" do
    let (img, _) := (SplitMix64.ofSeed 4004).image 33 17 .rgba
    match Qoi.encode img with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      match Qoi.decode bytes with
      | .error e => fail s!"decode failed: {e}"
      | .ok img' => assertImagesEq img' img "rgba 33x17",
  test "gray converts to rgba and round trips by pixel color" do
    let (img, _) := (SplitMix64.ofSeed 4005).image 12 9 .gray
    match Qoi.encode img with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      match Qoi.decode bytes with
      | .error e => fail s!"decode failed: {e}"
      | .ok img' =>
        assertEq img'.mode Mode.rgba "decodes as rgba"
        assertColorsEq img' img "gray colors preserved",
  test "palette converts to rgba and round trips by pixel color" do
    let (img, _) := (SplitMix64.ofSeed 4006).image 10 10 .palette
    match Qoi.encode img with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      match Qoi.decode bytes with
      | .error e => fail s!"decode failed: {e}"
      | .ok img' =>
        assertEq img'.mode Mode.rgba "decodes as rgba"
        assertColorsEq img' img "palette colors preserved"
]

/-- Build a `.rgb` image directly (row-major) for the hand-verified op
tests below, and encode/decode/size-check it in one place. -/
private def checkOp (label : String) (width height expectedSize : Nat)
    (px : List (UInt8 × UInt8 × UInt8)) : IO Unit := do
  let img := rgbImage width height px
  match Qoi.encode img with
  | .error e => fail s!"{label}: encode failed: {e}"
  | .ok bytes =>
    assertEq bytes.size expectedSize s!"{label}: encoded size"
    match Qoi.decode bytes with
    | .error e => fail s!"{label}: decode failed: {e}"
    | .ok img' => assertImagesEq img' img label

def opTests : List TestCase := [
  test "QOI_OP_RUN: 64 identical pixels, including the 62-pixel cap split" do
    -- pixel 0 is a genuine literal (far from the decoder's initial (0,0,0)
    -- previous pixel); pixels 1..63 are all identical to it, forcing one
    -- RUN(62) then one RUN(1) — 14-byte header + 4-byte QOI_OP_RGB +
    -- 1-byte RUN(62) + 1-byte RUN(1) + 8-byte end marker = 28.
    checkOp "RUN" 64 1 28 (List.replicate 64 (123, 45, 200)),
  test "QOI_OP_INDEX: a color repeats after an unrelated pixel in between" do
    -- pixel 0 and pixel 2 are the same color but not adjacent, so pixel 2
    -- must hit the seen-pixel table, not a run — 14 + 4 (RGB) + 4 (RGB) +
    -- 1 (INDEX) + 8 = 31; the deliberately-computed hash slot for (10,20,30)
    -- lands at index 9 (verified against the spec's hash formula by hand).
    checkOp "INDEX" 3 1 31 [(10, 20, 30), (200, 150, 100), (10, 20, 30)],
  test "QOI_OP_LUMA: green delta 20, red/blue deltas relative to green" do
    -- pixel 0 = (0,0,0) exactly matches the decoder's initial previous
    -- pixel, so it costs one RUN(1) chunk (1 byte) once pixel 1 breaks the
    -- run; pixel 1's deltas (dr=15, dg=20, db=18) are too big for
    -- QOI_OP_DIFF but fit QOI_OP_LUMA (vg=20 ∈ [-32,31], dr-dg=-5 and
    -- db-dg=-2, both ∈ [-8,7]) — 14 + 1 (RUN) + 2 (LUMA) + 8 = 25.
    checkOp "LUMA" 2 1 25 [(0, 0, 0), (15, 20, 18)],
  test "QOI_OP_DIFF: per-channel delta within [-2, 1]" do
    -- pixel 0 = (0,0,0) again costs one RUN(1); pixel 1's delta (+1, -2,
    -- +1) is within QOI_OP_DIFF's range — 14 + 1 (RUN) + 1 (DIFF) + 8 = 24.
    checkOp "DIFF" 2 1 24 [(0, 0, 0), (1, 254, 1)],
  test "QOI_OP_RGBA: an alpha-only change forces a literal RGBA chunk" do
    let img := Id.run do
      let mut i := Image.new 2 1 .rgba
      i := i.putPixel 0 0 ⟨0, 0, 0, 255⟩
      i := i.putPixel 1 0 ⟨0, 0, 0, 100⟩
      return i
    match Qoi.encode img with
    | .error e => fail s!"RGBA: encode failed: {e}"
    | .ok bytes =>
      -- 14 + 1 (RUN(1) for pixel 0, matching the initial previous pixel) +
      -- 5 (QOI_OP_RGBA: tag + r + g + b + a) + 8 = 28.
      assertEq bytes.size 28 "RGBA: encoded size"
      match Qoi.decode bytes with
      | .error e => fail s!"RGBA: decode failed: {e}"
      | .ok img' => assertImagesEq img' img "RGBA"
]

def errorTests : List TestCase := [
  test "bad magic bytes" do
    match Qoi.decode "not-a-qoi-file!!".toUTF8 with
    | .error _ => pure ()
    | .ok _ => fail "expected an error for non-QOI bytes",
  test "empty input errors, never panics" do
    match Qoi.decode ByteArray.empty with
    | .error _ => pure ()
    | .ok _ => fail "expected empty input to be rejected",
  test "unsupported channel count" do
    let hdr := ByteArray.empty
      |>.pushAscii "qoif" |>.pushU32be 1 |>.pushU32be 1 |>.push 5 |>.push 0
    match Qoi.decode hdr with
    | .error (.unsupported "qoi" _) => pure ()
    | .error e => fail s!"wrong error variant: {e}"
    | .ok _ => fail "expected a 5-channel header to be rejected",
  test "invalid colorspace byte" do
    let hdr := ByteArray.empty
      |>.pushAscii "qoif" |>.pushU32be 1 |>.pushU32be 1 |>.push 3 |>.push 2
    match Qoi.decode hdr with
    | .error (.corrupt _ _) => pure ()
    | .error e => fail s!"wrong error variant: {e}"
    | .ok _ => fail "expected an invalid colorspace byte to be rejected",
  test "declared dimensions vastly exceeding the available chunk data" do
    -- A tiny file claiming a huge image: must fail cleanly (truncated),
    -- not attempt a huge allocation or loop forever.
    let hdr := ByteArray.empty
      |>.pushAscii "qoif" |>.pushU32be 0xFFFFFFFF |>.pushU32be 0xFFFFFFFF
      |>.push 3 |>.push 0 |>.push 0xC0
    match Qoi.decode hdr with
    | .error _ => pure ()
    | .ok _ => fail "expected a bogus huge header to be rejected",
  test "missing end marker" do
    let img := rgbImage 2 2 [(1, 2, 3), (4, 5, 6), (7, 8, 9), (10, 11, 12)]
    match Qoi.encode img with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      let truncated := bytes.extract 0 (bytes.size - 4)  -- chop part of the end marker
      match Qoi.decode truncated with
      | .error _ => pure ()
      | .ok _ => fail "expected a missing end marker to be rejected"
]

def fuzzTests : List TestCase := [
  test "every strict prefix of ref_rgb.qoi errors" do
    let bytes ← qoiFixture "ref_rgb"
    truncationFuzz bytes,
  test "every strict prefix of ref_1x1.qoi errors" do
    let bytes ← qoiFixture "ref_1x1"
    truncationFuzz bytes,
  test "every strict prefix of a RUN-heavy encode errors" do
    let img := rgbImage 64 1 (List.replicate 64 (123, 45, 200))
    match Qoi.encode img with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes => truncationFuzz bytes
]

/-- The `qoi` suite (WP13). -/
def suite : Tests.Suite :=
  { name := "qoi"
    cases := referenceTests ++ roundTripTests ++ opTests ++ errorTests ++ fuzzTests }

end Tests.QoiTests
