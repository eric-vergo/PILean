import Tests.Framework
import Tests.Prng

/-!
# core tests

Image core: map, crop, paste, alphaComposite, convert, palette ops. Owned by WP1 — that work package fills in `cases`.
-/

namespace Tests.CoreTests

open PILean

/-- A 4×4 RGB image with a distinct color per pixel: `(10+x, 20+y, 30+x+y)`.
Used by the crop tests so every pixel is individually identifiable. -/
def gradient4x4 : Image := Id.run do
  let mut img := Image.new 4 4 .rgb
  for y in [0:4] do
    for x in [0:4] do
      img := img.putPixel x y
        (Color.rgb (UInt8.ofNat (10 + x)) (UInt8.ofNat (20 + y)) (UInt8.ofNat (30 + x + y)))
  return img

/-- A 2×2 RGB image with a distinct color per pixel, used as a paste/composite
source. -/
def smallSrc : Image := Id.run do
  let mut img := Image.new 2 2 .rgb
  for y in [0:2] do
    for x in [0:2] do
      img := img.putPixel x y
        (Color.rgb (UInt8.ofNat (100 + x)) (UInt8.ofNat (110 + y)) 120)
  return img

/-- The color read back from a zeroed `.rgb` pixel (alpha promotes to opaque). -/
def rgbZero : Color := Color.rgb 0 0 0

/-- Invert the RGB channels, keeping alpha. -/
def invertRGB (c : Color) : Color := ⟨255 - c.r, 255 - c.g, 255 - c.b, c.a⟩

def convertTests : List TestCase := [
  test "identity conversion returns the image unchanged" do
    let (img, _) := (SplitMix64.ofSeed 404).image 4 4 .rgba
    let same := img.convert .rgba
    assertBytesEq same.data img.data "identity data"
    assertEq same.mode img.mode "identity mode",
  test "rgb -> rgba -> rgb is byte-identical" do
    let (img, _) := (SplitMix64.ofSeed 101).image 5 5 .rgb
    let back := (img.convert .rgba).convert .rgb
    assertBytesEq back.data img.data "rgb→rgba→rgb",
  test "gray -> rgb -> gray is byte-identical" do
    let (img, _) := (SplitMix64.ofSeed 202).image 6 4 .gray
    let back := (img.convert .rgb).convert .gray
    assertBytesEq back.data img.data "gray→rgb→gray",
  test "gray -> grayAlpha -> gray is byte-identical" do
    let (img, _) := (SplitMix64.ofSeed 303).image 3 3 .gray
    let back := (img.convert .grayAlpha).convert .gray
    assertBytesEq back.data img.data "gray→grayAlpha→gray",
  test "luma parity matches Pillow (via convert to gray)" do
    assertEq ((Image.new 2 2 .rgb Color.red).convert .gray |>.getPixel! 0 0) (Color.gray 76) "red"
    assertEq ((Image.new 2 2 .rgb Color.green).convert .gray |>.getPixel! 0 0) (Color.gray 150) "green"
    assertEq ((Image.new 2 2 .rgb Color.blue).convert .gray |>.getPixel! 0 0) (Color.gray 29) "blue",
  test "rgba -> grayAlpha uses luma for gray, keeps alpha" do
    let img := Image.new 1 1 .rgba ⟨255, 0, 0, 200⟩
    assertEq (img.convert .grayAlpha |>.getPixel! 0 0) ⟨76, 76, 76, 200⟩ "red@200",
  test "convert to palette snaps to nearest web-safe entry" do
    let img := Image.new 2 2 .rgb (Color.rgb 50 52 100)
    let p := img.convert .palette
    assertEq p.mode .palette "mode"
    assertTrue p.palette?.isSome "has palette"
    assertEq (p.getPixel! 0 0) ⟨51, 51, 102, 255⟩ "snapped"
    assertTrue p.validate "validate",
  test "convert from palette resolves through its own palette" do
    let img := Image.new 2 2 .palette  -- black fill => index 0
    let redIdx := UInt8.ofNat (Palette.webSafe.nearestIndex Color.red)
    let img := img.setIndex 0 0 redIdx
    let rgbImg := img.convert .rgb
    assertEq (rgbImg.getPixel! 0 0) Color.red "red resolved"
    assertEq (rgbImg.getPixel! 1 0) Color.black "unaffected pixel stays black",
  test "convert is total across all 25 mode pairs" do
    let modes := [Mode.gray, .grayAlpha, .rgb, .rgba, .palette]
    for m1 in modes do
      let (img, _) := (SplitMix64.ofSeed 7).image 3 3 m1
      for m2 in modes do
        let out := img.convert m2
        assertTrue out.validate s!"{m1} -> {m2} validates"
        assertEq out.mode m2 s!"{m1} -> {m2} mode"
]

def cropTests : List TestCase := [
  test "crop fully inside source" do
    let img := gradient4x4
    let r := Rect.ofSize ⟨1, 1⟩ 2 2
    let c := img.crop r
    assertEq c.width 2 "width"
    assertEq c.height 2 "height"
    for y in [0:2] do
      for x in [0:2] do
        assertEq (c.getPixel! x y) (img.getPixel! (x + 1) (y + 1)) s!"({x},{y})",
  test "crop overlapping top-left edge zero-fills the outside part" do
    let img := gradient4x4
    let r : Rect := ⟨-1, -1, 3, 3⟩
    let c := img.crop r
    assertEq c.width 4 "width"
    assertEq c.height 4 "height"
    assertEq (c.getPixel! 0 0) rgbZero "outside both axes"
    assertEq (c.getPixel! 2 0) rgbZero "outside row (y=-1)"
    assertEq (c.getPixel! 0 2) rgbZero "outside column (x=-1)"
    assertEq (c.getPixel! 1 1) (img.getPixel! 0 0) "maps to source (0,0)"
    assertEq (c.getPixel! 3 3) (img.getPixel! 2 2) "maps to source (2,2)",
  test "crop fully outside source is all zero" do
    let img := gradient4x4
    let r : Rect := ⟨10, 10, 14, 14⟩
    let c := img.crop r
    assertEq c.width 4 "width"
    assertEq c.height 4 "height"
    for y in [0:4] do
      for x in [0:4] do
        assertEq (c.getPixel! x y) rgbZero s!"({x},{y}) zero",
  test "crop with an empty rect yields 0×N with empty data" do
    let img := gradient4x4
    let r : Rect := ⟨2, 2, 2, 5⟩
    let c := img.crop r
    assertEq c.width 0 "width"
    assertEq c.height 3 "height"
    assertEq c.data.size 0 "data empty",
  test "crop keeps the palette on .palette images" do
    let img := (Image.new 4 4 .palette).setIndex 1 1 215
    let c := img.crop (Rect.ofSize ⟨1, 1⟩ 2 2)
    assertTrue c.palette?.isSome "has palette"
    assertEq (c.getIndex? 0 0) (some 215) "index carried over"
    assertEq (c.getPixel! 0 0) Color.white "resolves via palette"
]

def pasteTests : List TestCase := [
  test "paste fully inside overwrites exactly that block" do
    let dst := Image.new 4 4 .rgb
    let p := dst.paste smallSrc ⟨1, 1⟩
    for y in [0:2] do
      for x in [0:2] do
        assertEq (p.getPixel! (1 + x) (1 + y)) (smallSrc.getPixel! x y) s!"({x},{y})"
    assertEq (p.getPixel! 0 0) rgbZero "top-left corner untouched"
    assertEq (p.getPixel! 3 3) rgbZero "bottom-right corner untouched",
  test "paste with negative position clips at the top/left edges" do
    let dst := Image.new 4 4 .rgb
    let p := dst.paste smallSrc ⟨-1, -1⟩
    assertEq (p.getPixel! 0 0) (smallSrc.getPixel! 1 1) "only src(1,1) lands"
    assertEq (p.getPixel! 1 0) rgbZero "clipped away"
    assertEq (p.getPixel! 0 1) rgbZero "clipped away",
  test "paste clips at the bottom/right edges" do
    let dst := Image.new 4 4 .rgb
    let p := dst.paste smallSrc ⟨3, 3⟩
    assertEq (p.getPixel! 3 3) (smallSrc.getPixel! 0 0) "only src(0,0) lands"
    assertEq (p.getPixel! 2 2) rgbZero "clipped away",
  test "paste fully outside the destination is a no-op" do
    let dst := Image.new 4 4 .rgb (Color.rgb 7 8 9)
    let p := dst.paste smallSrc ⟨10, 10⟩
    assertImagesEq p dst "unchanged",
  test "paste converts src to dst's mode first" do
    let graySrc := Image.new 2 2 .gray (Color.gray 42)
    let dst := Image.new 3 3 .rgb (Color.rgb 1 2 3)
    let p := dst.paste graySrc ⟨0, 0⟩
    assertEq (p.getPixel! 0 0) (Color.gray 42) "promoted to rgb"
    assertEq (p.getPixel! 2 2) (Color.rgb 1 2 3) "untouched area keeps dst color"
]

def alphaCompositeTests : List TestCase := [
  test "alphaComposite blends per Color.over" do
    let dst := Image.new 4 4 .rgba (Color.rgba 0 0 255 255)
    let src := Image.new 2 2 .rgba ⟨255, 0, 0, 128⟩
    let c := dst.alphaComposite src ⟨1, 1⟩
    let expected : Color := ⟨128, 0, 127, 255⟩  -- hand-computed Color.over ⟨255,0,0,128⟩ ⟨0,0,255,255⟩
    for y in [0:2] do
      for x in [0:2] do
        assertEq (c.getPixel! (1 + x) (1 + y)) expected s!"({x},{y})"
    assertEq (c.getPixel! 0 0) (Color.rgba 0 0 255 255) "outside area unchanged",
  test "fully transparent source is a no-op" do
    let dst := Image.new 4 4 .rgba (Color.rgba 0 0 255 255)
    let src := Image.new 2 2 .rgba ⟨9, 9, 9, 0⟩
    let c := dst.alphaComposite src ⟨1, 1⟩
    assertImagesEq c dst "unchanged",
  test "fully opaque source fully overwrites" do
    let dst := Image.new 4 4 .rgba (Color.rgba 0 0 255 255)
    let src := Image.new 2 2 .rgba ⟨9, 8, 7, 255⟩
    let c := dst.alphaComposite src ⟨1, 1⟩
    assertEq (c.getPixel! 1 1) ⟨9, 8, 7, 255⟩ "overwritten",
  test "alphaComposite clips at all four edges" do
    let dst := Image.new 4 4 .rgba (Color.rgba 0 0 255 255)
    let src := Image.new 2 2 .rgba ⟨255, 0, 0, 128⟩
    let expected : Color := ⟨128, 0, 127, 255⟩
    let cTopLeft := dst.alphaComposite src ⟨-1, -1⟩
    assertEq (cTopLeft.getPixel! 0 0) expected "top-left clip blends"
    assertEq (cTopLeft.getPixel! 1 0) (Color.rgba 0 0 255 255) "unaffected"
    let cBotRight := dst.alphaComposite src ⟨3, 3⟩
    assertEq (cBotRight.getPixel! 3 3) expected "bottom-right clip blends"
    assertEq (cBotRight.getPixel! 2 2) (Color.rgba 0 0 255 255) "unaffected"
]

def mapTests : List TestCase := [
  test "invert via map twice is the identity on rgb" do
    let (img, _) := (SplitMix64.ofSeed 55).image 5 4 .rgb
    let back := (img.map invertRGB).map invertRGB
    assertImagesEq back img "double invert",
  test "map id is the identity for every mode" do
    for m in [Mode.gray, .grayAlpha, .rgb, .rgba, .palette] do
      let (img, _) := (SplitMix64.ofSeed 66).image 4 3 m
      assertImagesEq (img.map id) img s!"id on {m}",
  test "palette map changes palette entries, not indices" do
    let img0 := (Image.new 2 2 .palette).setIndex 0 0
      (UInt8.ofNat (Palette.webSafe.nearestIndex Color.red))
    let before0 := img0.getIndex? 0 0
    let before1 := img0.getIndex? 1 0
    let mapped := img0.map invertRGB
    assertEq (mapped.getIndex? 0 0) before0 "index (0,0) unchanged"
    assertEq (mapped.getIndex? 1 0) before1 "index (1,0) unchanged"
    assertEq (mapped.getPixel! 0 0) (invertRGB Color.red) "color at (0,0) reflects new palette entry"
    assertEq (mapped.getPixel! 1 0) (invertRGB Color.black) "color at (1,0) reflects new palette entry"
]

/-- The `core` suite (WP1). -/
def suite : Tests.Suite :=
  { name := "core"
    cases := convertTests ++ cropTests ++ pasteTests ++ alphaCompositeTests ++ mapTests }

end Tests.CoreTests
