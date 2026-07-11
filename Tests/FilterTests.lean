import Tests.Framework
import Tests.Prng

/-!
# filter tests

Point operations: invert, brightness, contrast, threshold. Owned by WP7 — that work package fills in `cases`.
-/

namespace Tests.FilterTests

open PILean

private def allModes : List Mode := [.gray, .grayAlpha, .rgb, .rgba, .palette]

def involutionTests : List TestCase := [
  test "invert² = id across all modes" do
    for mode in allModes do
      let (img, _) := (SplitMix64.ofSeed 201).image 5 4 mode
      assertImagesEq img.invert.invert img s!"invert² {mode}",
  test "adjustBrightness with factor 1.0 = id across all modes" do
    for mode in allModes do
      let (img, _) := (SplitMix64.ofSeed 202).image 5 4 mode
      assertImagesEq (img.adjustBrightness 1.0) img s!"brightness 1.0 {mode}",
  test "adjustContrast with factor 1.0 = id across all modes" do
    for mode in allModes do
      let (img, _) := (SplitMix64.ofSeed 203).image 5 4 mode
      assertImagesEq (img.adjustContrast 1.0) img s!"contrast 1.0 {mode}"
]

def thresholdTests : List TestCase := [
  test "threshold on a gradient splits at the right column" do
    let img := Id.run do
      let mut im := Image.new 256 1 .gray
      for x in [0:256] do
        im := im.putPixel x 0 (Color.gray (UInt8.ofNat x))
      return im
    let r := img.threshold 128
    for x in [0:256] do
      let expected : UInt8 := if x ≥ 128 then 255 else 0
      assertEq (r.getPixel! x 0) (Color.gray expected) s!"x={x}",
  test "threshold on .palette converts pixel-wise to .gray (v1 behavior)" do
    let img := (Image.new 2 1 .palette) |>.setIndex 0 0 0 |>.setIndex 1 0 215
    -- webSafe index 0 = black (luma 0 < 128), index 215 = white (luma 255 ≥ 128)
    let r := img.threshold 128
    assertEq r.mode Mode.gray "output mode"
    assertEq (r.getPixel! 0 0) Color.black "black stays below threshold"
    assertEq (r.getPixel! 1 0) Color.white "white stays at/above threshold"
]

def brightnessContrastTests : List TestCase := [
  test "adjustBrightness scales and clamps" do
    let img := Image.new 2 1 .rgb |>.putPixel 0 0 (Color.rgb 100 100 100)
      |>.putPixel 1 0 (Color.rgb 200 10 250)
    let r := img.adjustBrightness 0.5
    assertEq (r.getPixel! 0 0) (Color.rgb 50 50 50) "halved"
    assertEq (r.getPixel! 1 0) (Color.rgb 100 5 125) "halved, mixed"
    let bright := img.adjustBrightness 2.0
    assertEq (bright.getPixel! 0 0) (Color.rgb 200 200 200) "doubled"
    assertEq (bright.getPixel! 1 0) (Color.rgb 255 20 255) "doubled, clamps to 255",
  test "adjustContrast pivots on the mean luma and clamps" do
    -- two pixels, luma 18 and 255 (channel-uniform so luma = the value);
    -- mean = round((18+255)/2) = round(136.5) = 137 (round-half-away-from-zero)
    let img := Image.new 2 1 .gray |>.putPixel 0 0 (Color.gray 18) |>.putPixel 1 0 (Color.gray 255)
    let r := img.adjustContrast 2.0
    -- (18-137)*2+137 = -119*2+137 = -238+137 = -101 → clamp 0
    assertEq (r.getPixel! 0 0) (Color.gray 0) "low pixel clamps to 0"
    -- (255-137)*2+137 = 118*2+137 = 236+137 = 373 → clamp 255
    assertEq (r.getPixel! 1 0) (Color.gray 255) "high pixel clamps to 255"
]

def alphaPreservationTests : List TestCase := [
  test "point filters preserve alpha on rgba" do
    let img := Id.run do
      let mut im := Image.new 6 5 .rgba
      for y in [0:5] do
        for x in [0:6] do
          let a : UInt8 := UInt8.ofNat ((x * 37 + y * 53 + 11) % 256)
          im := im.putPixel x y ⟨UInt8.ofNat (x * 20), UInt8.ofNat (y * 20), 100, a⟩
      return im
    let checkAlphaPreserved (out : Image) (label : String) : IO Unit := do
      for y in [0:5] do
        for x in [0:6] do
          assertEq (out.getPixel! x y).a (img.getPixel! x y).a s!"{label} alpha ({x},{y})"
    checkAlphaPreserved img.invert "invert"
    checkAlphaPreserved (img.adjustBrightness 0.5) "brightness"
    checkAlphaPreserved (img.adjustContrast 1.5) "contrast"
    checkAlphaPreserved (img.threshold 128) "threshold"
]

/-- The `filter` suite (WP7). -/
def suite : Tests.Suite :=
  { name := "filter"
    cases := involutionTests ++ thresholdTests ++ brightnessContrastTests ++ alphaPreservationTests }

end Tests.FilterTests
