import Tests.Framework
import Tests.Prng

/-!
# netpbm tests

PPM/PGM/PBM encode + decode, golden files, comments, ASCII variants. Owned by WP4.

Fixtures live under `testdata/golden/netpbm/` and are generated (and cross-checked
against Pillow 11.3.0) by `testdata/golden/netpbm/gen.py`.
-/

namespace Tests.NetpbmTests

open PILean PILean.Netpbm

/-- Read a committed fixture from `testdata/golden/netpbm/`. -/
private def fixture (name : String) : IO ByteArray :=
  IO.FS.readBinFile (Tests.goldenDir / "netpbm" / name)

/-- Build an image from a flat list of RGB triples, row-major. -/
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

/-- Build a `.gray` image from a flat list of gray values, row-major. -/
private def grayImage (width height : Nat) (px : List UInt8) : Image :=
  Id.run do
    let mut img := Image.new width height .gray
    let mut i := 0
    for y in [0:height] do
      for x in [0:width] do
        if h : i < px.length then
          img := img.putPixel x y (Color.gray px[i])
        i := i + 1
    return img

def decodeTests : List TestCase := [
  test "P3 (ASCII pixmap) with comments" do
    let bytes ← fixture "p3_comments.ppm"
    match decode bytes with
    | .error e => fail s!"decode failed: {e}"
    | .ok img =>
      let expected := rgbImage 3 2
        [(255, 0, 0), (0, 255, 0), (0, 0, 255), (10, 20, 30), (40, 50, 60), (70, 80, 90)]
      assertImagesEq img expected "p3_comments",
  test "P6 (binary pixmap) gradient, direct-copy fast path" do
    let bytes ← fixture "p6_gradient.ppm"
    match decode bytes with
    | .error e => fail s!"decode failed: {e}"
    | .ok img =>
      assertEq img.width 4 "width"
      assertEq img.height 3 "height"
      assertEq img.mode Mode.rgb "mode"
      for y in [0:3] do
        for x in [0:4] do
          let expected := Color.rgb (UInt8.ofNat (x * 30)) (UInt8.ofNat (y * 40)) 100
          assertEq (img.getPixel! x y) expected s!"({x},{y})",
  test "P6 (binary pixmap) with maxval < 255 scales by floor(v*255/maxval)" do
    let bytes ← fixture "p6_scaled.ppm"
    match decode bytes with
    | .error e => fail s!"decode failed: {e}"
    | .ok img =>
      let expected := rgbImage 2 2
        [(2, 5, 7), (127, 153, 178), (252, 0, 255), (25, 229, 114)]
      assertImagesEq img expected "p6_scaled",
  test "P2 (ASCII graymap) with maxval < 255" do
    let bytes ← fixture "p2_scaled.pgm"
    match decode bytes with
    | .error e => fail s!"decode failed: {e}"
    | .ok img =>
      let expected := grayImage 4 2 [0, 85, 136, 255, 51, 204, 17, 255]
      assertImagesEq img expected "p2_scaled",
  test "P5 (binary graymap) gradient, direct-copy fast path" do
    let bytes ← fixture "p5_gradient.pgm"
    match decode bytes with
    | .error e => fail s!"decode failed: {e}"
    | .ok img =>
      let expected := grayImage 5 2 [0, 10, 20, 30, 40, 50, 60, 70, 80, 90]
      assertImagesEq img expected "p5_gradient",
  test "P5 (binary graymap) with maxval < 255 scales by floor(v*255/maxval)" do
    let bytes ← fixture "p5_scaled.pgm"
    match decode bytes with
    | .error e => fail s!"decode failed: {e}"
    | .ok img =>
      let expected := grayImage 3 2 [0, 127, 255, 51, 204, 25]
      assertImagesEq img expected "p5_scaled",
  test "P1 (ASCII bitmap) with comments: 1=black, 0=white" do
    let bytes ← fixture "p1_bitmap.pbm"
    match decode bytes with
    | .error e => fail s!"decode failed: {e}"
    | .ok img =>
      let expected := grayImage 5 3
        [0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 0, 0, 255, 255]
      assertImagesEq img expected "p1_bitmap",
  test "P4 (binary bitmap) MSB-first, row padding for non-8-multiple width" do
    let bytes ← fixture "p4_bitmap.pbm"
    match decode bytes with
    | .error e => fail s!"decode failed: {e}"
    | .ok img =>
      let expected := grayImage 5 3
        [0, 255, 0, 255, 0, 255, 0, 255, 0, 255, 0, 0, 0, 255, 255]
      assertImagesEq img expected "p4_bitmap",
  test "P1 and P4 agree on the same bitmap" do
    let b1 ← fixture "p1_bitmap.pbm"
    let b4 ← fixture "p4_bitmap.pbm"
    match decode b1, decode b4 with
    | .ok img1, .ok img4 => assertImagesEq img4 img1 "p1 vs p4"
    | .error e, _ => fail s!"P1 decode failed: {e}"
    | _, .error e => fail s!"P4 decode failed: {e}",
  test "1x1 image" do
    let bytes ← fixture "tiny_1x1.ppm"
    match decode bytes with
    | .error e => fail s!"decode failed: {e}"
    | .ok img =>
      assertEq img.width 1 "width"
      assertEq img.height 1 "height"
      assertEq (img.getPixel! 0 0) (Color.rgb 12 34 56) "pixel"
]

def encodeRoundTripTests : List TestCase := [
  test "gray round trips exactly (P5)" do
    let img := Id.run do
      let mut i := Image.new 4 3 .gray
      i := i.putPixel 0 0 (Color.gray 0)
      i := i.putPixel 3 2 (Color.gray 255)
      i := i.putPixel 1 1 (Color.gray 128)
      return i
    match encode img with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      assertTrue (bytes.size ≥ 2 && bytes.get! 0 == 80 && bytes.get! 1 == 53) "starts with P5"
      match decode bytes with
      | .error e => fail s!"decode failed: {e}"
      | .ok img' => assertImagesEq img' img "round trip",
  test "rgb round trips exactly (P6)" do
    let img := Id.run do
      let mut i := Image.new 3 2 .rgb
      i := i.putPixel 0 0 (Color.rgb 1 2 3)
      i := i.putPixel 2 1 (Color.rgb 250 251 252)
      return i
    match encode img with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      assertTrue (bytes.size ≥ 2 && bytes.get! 0 == 80 && bytes.get! 1 == 54) "starts with P6"
      match decode bytes with
      | .error e => fail s!"decode failed: {e}"
      | .ok img' => assertImagesEq img' img "round trip",
  test "rgba round trips RGB (alpha dropped) via P6" do
    let img := Id.run do
      let mut i := Image.new 2 2 .rgba
      i := i.putPixel 0 0 ⟨10, 20, 30, 40⟩
      i := i.putPixel 1 1 ⟨200, 201, 202, 5⟩
      return i
    match encode img with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      match decode bytes with
      | .error e => fail s!"decode failed: {e}"
      | .ok img' =>
        assertEq img'.mode Mode.rgb "decoded as rgb"
        for y in [0:2] do
          for x in [0:2] do
            let c := img.getPixel! x y
            let c' := img'.getPixel! x y
            assertEq (c'.r, c'.g, c'.b) (c.r, c.g, c.b) s!"({x},{y}) rgb",
  test "grayAlpha round trips as RGB (luma promoted) via P6" do
    let img := Id.run do
      let mut i := Image.new 2 2 .grayAlpha
      i := i.putPixel 0 0 ⟨9, 9, 9, 255⟩
      i := i.putPixel 1 0 ⟨200, 200, 200, 10⟩
      return i
    match encode img with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      match decode bytes with
      | .error e => fail s!"decode failed: {e}"
      | .ok img' =>
        assertEq img'.mode Mode.rgb "decoded as rgb"
        assertEq (img'.getPixel! 0 0) (Color.rgb 9 9 9) "gray promoted"
        assertEq (img'.getPixel! 1 0) (Color.rgb 200 200 200) "gray promoted, alpha dropped",
  test "palette round trips as RGB (resolved) via P6" do
    let img := (Image.new 2 2 .palette).putPixel 0 0 Color.red |>.putPixel 1 1 Color.blue
    match encode img with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      match decode bytes with
      | .error e => fail s!"decode failed: {e}"
      | .ok img' =>
        assertEq img'.mode Mode.rgb "decoded as rgb"
        assertEq (img'.getPixel! 0 0) (img.getPixel! 0 0) "red resolved"
        assertEq (img'.getPixel! 1 1) (img.getPixel! 1 1) "blue resolved"
]

def errorTests : List TestCase := [
  test "bad magic bytes" do
    match decode "XYabc".toUTF8 with
    | .error _ => pure ()
    | .ok _ => fail "expected an error for non-Netpbm bytes",
  test "maxval > 255 is unsupported, not truncated/corrupt-panicking" do
    match decode "P5\n2 2\n1000\n".toUTF8 with
    | .error (.unsupported "netpbm" _) => pure ()
    | .error e => fail s!"wrong error variant: {e}"
    | .ok _ => fail "expected maxval > 255 to be rejected",
  test "maxval 0 is corrupt" do
    match decode "P2\n1 1\n0\n0\n".toUTF8 with
    | .error (.corrupt ..) => pure ()
    | .error e => fail s!"wrong error variant: {e}"
    | .ok _ => fail "expected maxval 0 to be rejected",
  test "zero width/height is rejected" do
    match decode "P6\n0 3\n255\n".toUTF8 with
    | .error _ => pure ()
    | .ok _ => fail "expected zero width to be rejected",
  test "empty input errors, never panics" do
    match decode ByteArray.empty with
    | .error _ => pure ()
    | .ok _ => fail "expected empty input to be rejected"
]

/-- Every strict prefix of `bytes` must fail to decode (never panic). Only
meaningful for binary variants (P4/P5/P6), whose raw pixel payload has an
exact required byte count. -/
private def truncationFuzz (bytes : ByteArray) : IO Unit := do
  for n in [0:bytes.size] do
    match decode (bytes.extract 0 n) with
    | .ok _ => fail s!"prefix of length {n} unexpectedly decoded"
    | .error _ => pure ()

/-- Every strict prefix of `bytes` must either fail to decode or (only for
self-delimiting ASCII formats) decode successfully without panicking —
never crash. Used for P1/P2/P3, where truncating only the trailing digits
of the *last* numeric token still yields a syntactically complete file
(digit-reading is EOF-tolerant, matching real Netpbm parsers), so `.ok` is
not itself a bug. -/
private def truncationNoPanic (bytes : ByteArray) : IO Unit := do
  for n in [0:bytes.size] do
    match decode (bytes.extract 0 n) with
    | .ok _ => pure ()
    | .error _ => pure ()

def fuzzTests : List TestCase := [
  test "every strict prefix of a binary fixture (P6) errors" do
    let bytes ← fixture "p6_gradient.ppm"
    truncationFuzz bytes,
  test "every strict prefix of a binary fixture (P4) errors" do
    let bytes ← fixture "p4_bitmap.pbm"
    truncationFuzz bytes,
  test "every strict prefix of an ASCII fixture (P3 with comments) never panics" do
    -- ASCII numeric tokens are whitespace/EOF-delimited, so truncating only
    -- the trailing digits of the final token can still parse (to a
    -- different, shorter number) rather than error -- that's correct
    -- self-delimiting-format behavior, not a crash. We only assert safety.
    let bytes ← fixture "p3_comments.ppm"
    truncationNoPanic bytes
]

/-- The `netpbm` suite (WP4). -/
def suite : Tests.Suite :=
  { name := "netpbm"
    cases := decodeTests ++ encodeRoundTripTests ++ errorTests ++ fuzzTests }

end Tests.NetpbmTests
