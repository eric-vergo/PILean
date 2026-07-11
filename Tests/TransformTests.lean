import Tests.Framework
import Tests.Prng

/-!
# transform tests

Flips, rotations, transpose, nearest/bilinear resize. Owned by WP7 — that work package fills in `cases`.
-/

namespace Tests.TransformTests

open PILean

/-- A 3×2 RGB image with every pixel a distinct color (`r = 1..6`, row-major:
`A B C / D E F`), used to check the exact hand-derived output layout of
every orientation transform. Values were cross-checked against
`Image.transpose(...)` in Pillow 11.3.0 directly. -/
private def markedImage : Image :=
  (Image.new 3 2 .rgb)
    |>.putPixel 0 0 (Color.rgb 1 0 0)  -- A
    |>.putPixel 1 0 (Color.rgb 2 0 0)  -- B
    |>.putPixel 2 0 (Color.rgb 3 0 0)  -- C
    |>.putPixel 0 1 (Color.rgb 4 0 0)  -- D
    |>.putPixel 1 1 (Color.rgb 5 0 0)  -- E
    |>.putPixel 2 1 (Color.rgb 6 0 0)  -- F

private def allModes : List Mode := [.gray, .grayAlpha, .rgb, .rgba, .palette]

def involutionTests : List TestCase := [
  test "flipH is an involution across all modes" do
    for mode in allModes do
      let (img, _) := (SplitMix64.ofSeed 101).image 5 4 mode
      assertImagesEq img.flipH.flipH img s!"flipH² {mode}",
  test "flipV is an involution across all modes" do
    for mode in allModes do
      let (img, _) := (SplitMix64.ofSeed 102).image 5 4 mode
      assertImagesEq img.flipV.flipV img s!"flipV² {mode}",
  test "rotate180 is an involution across all modes" do
    for mode in allModes do
      let (img, _) := (SplitMix64.ofSeed 103).image 5 4 mode
      assertImagesEq img.rotate180.rotate180 img s!"rotate180² {mode}",
  test "transpose is an involution across all modes" do
    for mode in allModes do
      let (img, _) := (SplitMix64.ofSeed 104).image 5 4 mode
      assertImagesEq img.transpose.transpose img s!"transpose² {mode}",
  test "rotate90 ∘ rotate270 = id across all modes" do
    for mode in allModes do
      let (img, _) := (SplitMix64.ofSeed 105).image 5 4 mode
      assertImagesEq img.rotate90.rotate270 img s!"rotate90 then rotate270 {mode}"
      assertImagesEq img.rotate270.rotate90 img s!"rotate270 then rotate90 {mode}"
]

def orientationTests : List TestCase := [
  test "rotate90 (CCW / PIL ROTATE_90) matches the hand-derived 3×2 → 2×3 layout" do
    let r := markedImage.rotate90
    assertEq r.width 2 "width"
    assertEq r.height 3 "height"
    assertEq (r.getPixel! 0 0) (Color.rgb 3 0 0) "(0,0) = C"
    assertEq (r.getPixel! 1 0) (Color.rgb 6 0 0) "(1,0) = F"
    assertEq (r.getPixel! 0 1) (Color.rgb 2 0 0) "(0,1) = B"
    assertEq (r.getPixel! 1 1) (Color.rgb 5 0 0) "(1,1) = E"
    assertEq (r.getPixel! 0 2) (Color.rgb 1 0 0) "(0,2) = A"
    assertEq (r.getPixel! 1 2) (Color.rgb 4 0 0) "(1,2) = D",
  test "rotate270 matches the hand-derived 3×2 → 2×3 layout" do
    let r := markedImage.rotate270
    assertEq r.width 2 "width"
    assertEq r.height 3 "height"
    assertEq (r.getPixel! 0 0) (Color.rgb 4 0 0) "(0,0) = D"
    assertEq (r.getPixel! 1 0) (Color.rgb 1 0 0) "(1,0) = A"
    assertEq (r.getPixel! 0 1) (Color.rgb 5 0 0) "(0,1) = E"
    assertEq (r.getPixel! 1 1) (Color.rgb 2 0 0) "(1,1) = B"
    assertEq (r.getPixel! 0 2) (Color.rgb 6 0 0) "(0,2) = F"
    assertEq (r.getPixel! 1 2) (Color.rgb 3 0 0) "(1,2) = C",
  test "rotate180 matches the hand-derived layout" do
    let r := markedImage.rotate180
    assertEq r.width 3 "width"
    assertEq r.height 2 "height"
    assertEq (r.getPixel! 0 0) (Color.rgb 6 0 0) "(0,0) = F"
    assertEq (r.getPixel! 1 0) (Color.rgb 5 0 0) "(1,0) = E"
    assertEq (r.getPixel! 2 0) (Color.rgb 4 0 0) "(2,0) = D"
    assertEq (r.getPixel! 0 1) (Color.rgb 3 0 0) "(0,1) = C"
    assertEq (r.getPixel! 1 1) (Color.rgb 2 0 0) "(1,1) = B"
    assertEq (r.getPixel! 2 1) (Color.rgb 1 0 0) "(2,1) = A",
  test "transpose matches the hand-derived layout" do
    let r := markedImage.transpose
    assertEq r.width 2 "width"
    assertEq r.height 3 "height"
    assertEq (r.getPixel! 0 0) (Color.rgb 1 0 0) "(0,0) = A"
    assertEq (r.getPixel! 1 0) (Color.rgb 4 0 0) "(1,0) = D"
    assertEq (r.getPixel! 0 1) (Color.rgb 2 0 0) "(0,1) = B"
    assertEq (r.getPixel! 1 1) (Color.rgb 5 0 0) "(1,1) = E"
    assertEq (r.getPixel! 0 2) (Color.rgb 3 0 0) "(0,2) = C"
    assertEq (r.getPixel! 1 2) (Color.rgb 6 0 0) "(1,2) = F",
  test "flipH matches the hand-derived layout" do
    let r := markedImage.flipH
    assertEq (r.getPixel! 0 0) (Color.rgb 3 0 0) "(0,0) = C"
    assertEq (r.getPixel! 1 0) (Color.rgb 2 0 0) "(1,0) = B"
    assertEq (r.getPixel! 2 0) (Color.rgb 1 0 0) "(2,0) = A"
    assertEq (r.getPixel! 0 1) (Color.rgb 6 0 0) "(0,1) = F"
    assertEq (r.getPixel! 1 1) (Color.rgb 5 0 0) "(1,1) = E"
    assertEq (r.getPixel! 2 1) (Color.rgb 4 0 0) "(2,1) = D",
  test "flipV matches the hand-derived layout" do
    let r := markedImage.flipV
    assertEq (r.getPixel! 0 0) (Color.rgb 4 0 0) "(0,0) = D"
    assertEq (r.getPixel! 1 0) (Color.rgb 5 0 0) "(1,0) = E"
    assertEq (r.getPixel! 2 0) (Color.rgb 6 0 0) "(2,0) = F"
    assertEq (r.getPixel! 0 1) (Color.rgb 1 0 0) "(0,1) = A"
    assertEq (r.getPixel! 1 1) (Color.rgb 2 0 0) "(1,1) = B"
    assertEq (r.getPixel! 2 1) (Color.rgb 3 0 0) "(2,1) = C",
  test "flipV equals the row-reversed raw buffer" do
    let (img, _) := (SplitMix64.ofSeed 7).image 6 5 .rgba
    let w := img.width
    let h := img.height
    let bpp := img.mode.bytesPerPixel
    let rowBytes := w * bpp
    let expected := Id.run do
      let mut out := ByteArray.empty
      for y in [0:h] do
        let srcY := h - 1 - y
        out := out ++ img.data.extract (srcY * rowBytes) (srcY * rowBytes + rowBytes)
      return out
    assertBytesEq img.flipV.data expected "flipV row reversal"
]

def resizeTests : List TestCase := [
  test "nearest 2× upscale of a 2×2 pattern is the exact 4×4 block pattern" do
    let img :=
      (Image.new 2 2 .gray)
        |>.putPixel 0 0 (Color.gray 10) |>.putPixel 1 0 (Color.gray 20)
        |>.putPixel 0 1 (Color.gray 30) |>.putPixel 1 1 (Color.gray 40)
    let r := img.resize 4 4 .nearest
    assertEq r.width 4 "width"
    assertEq r.height 4 "height"
    for y in [0:4] do
      for x in [0:4] do
        let expected : UInt8 := if y < 2 then (if x < 2 then 10 else 20) else (if x < 2 then 30 else 40)
        assertEq (r.getPixel! x y) (Color.gray expected) s!"({x},{y})",
  test "nearest downscale picks the expected pixels" do
    let img := Id.run do
      let mut im := Image.new 4 4 .gray
      let mut v : UInt8 := 1
      for y in [0:4] do
        for x in [0:4] do
          im := im.putPixel x y (Color.gray v)
          v := v + 1
      return im
    let r := img.resize 2 2 .nearest
    -- src = floor((dst+0.5)*2): dst 0 → src 1, dst 1 → src 3
    assertEq (r.getPixel! 0 0) (Color.gray 6) "(0,0) = src(1,1)"
    assertEq (r.getPixel! 1 0) (Color.gray 8) "(1,0) = src(3,1)"
    assertEq (r.getPixel! 0 1) (Color.gray 14) "(0,1) = src(1,3)"
    assertEq (r.getPixel! 1 1) (Color.gray 16) "(1,1) = src(3,3)",
  test "bilinear of a solid image is identical" do
    let c := Color.rgb 50 60 70
    let img := Image.new 3 3 .rgb c
    let r := img.resize 5 5 .bilinear
    for y in [0:5] do
      for x in [0:5] do
        assertEq (r.getPixel! x y) c s!"({x},{y})",
  test "bilinear 2× of a 2×1 black|white gives the hand-derived blend column" do
    let img := (Image.new 2 1 .gray) |>.putPixel 0 0 (Color.gray 0) |>.putPixel 1 0 (Color.gray 255)
    let r := img.resize 4 1 .bilinear
    -- src = (dst+0.5)*0.5-0.5: dst0 → -0.25 (clamps to 0,0 both → 0);
    -- dst1 → 0.25 (0.75·0+0.25·255=63.75→64); dst2 → 0.75 (0.25·0+0.75·255=191.25→191);
    -- dst3 → 1.25 (clamps x1 to 1 → both indices 1 → 255)
    assertEq (r.getPixel! 0 0) (Color.gray 0) "col0"
    assertEq (r.getPixel! 1 0) (Color.gray 64) "col1"
    assertEq (r.getPixel! 2 0) (Color.gray 191) "col2"
    assertEq (r.getPixel! 3 0) (Color.gray 255) "col3",
  test "resize to the same size returns the image unchanged" do
    let (img, _) := (SplitMix64.ofSeed 55).image 6 5 .rgba
    assertImagesEq (img.resize 6 5 .bilinear) img "identity resize (bilinear)"
    assertImagesEq (img.resize 6 5 .nearest) img "identity resize (nearest)",
  test "resize to 0×N or N×0 yields an empty-data image" do
    let (img, _) := (SplitMix64.ofSeed 56).image 4 4 .rgb
    let r1 := img.resize 0 4 .bilinear
    assertEq r1.width 0 "0×4 width"
    assertEq r1.height 4 "0×4 height"
    assertEq r1.data.size 0 "0×4 data empty"
    let r2 := img.resize 4 0 .nearest
    assertEq r2.width 4 "4×0 width"
    assertEq r2.height 0 "4×0 height"
    assertEq r2.data.size 0 "4×0 data empty",
  test "bilinear on .palette falls back to nearest" do
    let img := (Image.new 2 1 .palette) |>.setIndex 0 0 0 |>.setIndex 1 0 215
    assertImagesEq (img.resize 4 1 .bilinear) (img.resize 4 1 .nearest) "palette bilinear == nearest"
]

/-- The `transform` suite (WP7). -/
def suite : Tests.Suite :=
  { name := "transform"
    cases := involutionTests ++ orientationTests ++ resizeTests }

end Tests.TransformTests
