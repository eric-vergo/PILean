import Tests.Framework
import Tests.Prng

/-!
# Scaffold tests

Tests for the Wave-0 implementations: Color, Geometry, Palette, the Image
accessor layer, binary reader/writer, and the PRNG. Owned by the
integrator.
-/

namespace Tests.ScaffoldTests

open PILean PILean.Binary

def colorTests : List TestCase := [
  test "luma matches Pillow rounding" do
    assertEq Color.white.luma 255 "white"
    assertEq Color.black.luma 0 "black"
    assertEq Color.red.luma 76 "red"
    assertEq Color.green.luma 150 "green"
    assertEq Color.blue.luma 29 "blue",
  test "ofHex? forms" do
    assertEq (Color.ofHex? "#ff0000") (some Color.red) "#ff0000"
    assertEq (Color.ofHex? "00ff00") (some Color.green) "00ff00 (no hash)"
    assertEq (Color.ofHex? "#abc") (some ⟨0xaa, 0xbb, 0xcc, 255⟩) "#abc shorthand"
    assertEq (Color.ofHex? "#12345678") (some ⟨0x12, 0x34, 0x56, 0x78⟩) "#rrggbbaa"
    assertEq (Color.ofHex? "#xyz") none "invalid digits"
    assertEq (Color.ofHex? "#12345") none "bad length",
  test "over compositing" do
    assertEq (Color.over Color.red Color.white) Color.red "opaque src wins"
    assertEq (Color.over Color.transparent Color.blue) Color.blue "transparent src keeps dst"
    assertEq (Color.over ⟨255, 0, 0, 128⟩ Color.white) ⟨255, 127, 127, 255⟩ "half red on white"
]

def geometryTests : List TestCase := [
  test "rect basics" do
    let r : Rect := ⟨2, 3, 10, 8⟩
    assertEq r.width 8 "width"
    assertEq r.height 5 "height"
    assertTrue (!r.isEmpty) "nonempty"
    assertTrue (⟨-1, -1, 5, -1⟩ : Rect).isEmpty "empty when bottom ≤ top"
    assertEq (⟨5, 5, 2, 9⟩ : Rect).width 0 "width clamps to 0",
  test "rect intersect and contains" do
    let r : Rect := ⟨0, 0, 10, 10⟩
    let s : Rect := ⟨5, -3, 15, 7⟩
    assertEq (r.intersect s) ⟨5, 0, 10, 7⟩ "intersect"
    assertTrue (r.contains ⟨0, 0⟩) "contains top-left"
    assertTrue (!r.contains ⟨10, 5⟩) "half-open: right edge excluded"
    assertTrue (!r.contains ⟨5, 10⟩) "half-open: bottom edge excluded"
]

def paletteTests : List TestCase := [
  test "webSafe palette" do
    assertEq Palette.webSafe.size 216 "size"
    assertEq (Palette.webSafe.get! 0) Color.black "first entry"
    assertEq (Palette.webSafe.get! 215) Color.white "last entry",
  test "nearestIndex finds exact colors" do
    let p := Palette.webSafe
    assertEq (p.get! (p.nearestIndex Color.red)) Color.red "red is web-safe"
    assertEq (p.get! (p.nearestIndex ⟨50, 52, 100, 255⟩)) ⟨51, 51, 102, 255⟩ "near miss snaps"
]

def imageTests : List TestCase := [
  test "new + validate for every mode" do
    for mode in [Mode.gray, .grayAlpha, .rgb, .rgba, .palette] do
      let img := Image.new 4 3 mode
      assertTrue img.validate s!"validate {mode}"
      assertEq img.data.size (4 * 3 * mode.bytesPerPixel) s!"data size {mode}",
  test "putPixel/getPixel round trip per mode" do
    -- gray: color is stored as luma, read back as gray
    let g := (Image.new 4 4 .gray).putPixel 1 2 Color.red
    assertEq (g.getPixel! 1 2) (Color.gray 76) "gray stores luma"
    -- rgb
    let c := Color.rgb 12 34 56
    assertEq ((Image.new 4 4 .rgb).putPixel 3 0 c |>.getPixel! 3 0) c "rgb"
    -- rgba
    let ca : Color := ⟨12, 34, 56, 78⟩
    assertEq ((Image.new 4 4 .rgba).putPixel 0 3 ca |>.getPixel! 0 3) ca "rgba"
    -- grayAlpha
    assertEq ((Image.new 4 4 .grayAlpha).putPixel 2 2 ⟨0, 0, 255, 9⟩ |>.getPixel! 2 2)
      ⟨29, 29, 29, 9⟩ "grayAlpha stores luma + alpha"
    -- palette snaps to web-safe
    assertEq ((Image.new 4 4 .palette).putPixel 1 1 ⟨50, 52, 100, 255⟩ |>.getPixel! 1 1)
      ⟨51, 51, 102, 255⟩ "palette snaps",
  test "out-of-bounds clips" do
    let img := Image.new 4 4 .rgb (Color.gray 7)
    let img := img.putPixel (-1) 0 Color.red |>.putPixel 4 0 Color.red |>.putPixel 0 99 Color.red
    assertEq (img.getPixel? (-1) 0) none "getPixel? OOB"
    -- no pixel changed
    for y in [0:4] do
      for x in [0:4] do
        assertEq (img.getPixel! x y) (Color.gray 7) s!"({x},{y}) untouched",
  test "fill color respected" do
    let img := Image.new 3 2 .rgba ⟨1, 2, 3, 4⟩
    assertEq (img.getPixel! 2 1) ⟨1, 2, 3, 4⟩ "fill",
  test "palette index access" do
    let img := Image.new 3 3 .palette
    let img := img.setIndex 1 1 215
    assertEq (img.getIndex? 1 1) (some 215) "setIndex/getIndex"
    assertEq (img.getPixel! 1 1) Color.white "index 215 = white"
    assertEq ((Image.new 2 2 .rgb).getIndex? 0 0) none "getIndex? on non-palette"
]

def binaryTests : List TestCase := [
  test "writer/reader round trip" do
    let b := ByteArray.empty
      |>.pushU16le 0x1234 |>.pushU16be 0x1234
      |>.pushU32le 0xDEADBEEF |>.pushU32be 0xDEADBEEF
      |>.pushAscii "PIL"
    assertEq b.size 15 "size"
    let r : Except DecodeError (UInt16 × UInt16 × UInt32 × UInt32 × String) :=
      ParseM.run (data := b) do
        let a ← ParseM.u16le
        let b' ← ParseM.u16be
        let c ← ParseM.u32le
        let d ← ParseM.u32be
        let s ← ParseM.asciiToken
        return (a, b', c, d, s)
    match r with
    | .ok (a, b', c, d, s) =>
      assertEq a 0x1234 "u16le"
      assertEq b' 0x1234 "u16be"
      assertEq c 0xDEADBEEF "u32le"
      assertEq d 0xDEADBEEF "u32be"
      assertEq s "PIL" "asciiToken"
    | .error e => fail s!"parse failed: {e}",
  test "truncation errors, never panics" do
    let r := ParseM.run ParseM.u32be (ByteArray.empty.push 1)
    match r with
    | .ok _ => fail "expected truncation error"
    | .error (.truncated ..) => pure ()
    | .error e => fail s!"wrong error: {e}",
  test "asciiNat and whitespace" do
    let b := "  \t\n 6789 xx".toUTF8
    match ParseM.run (data := b) (do
      let n ← ParseM.asciiNat
      let t ← ParseM.asciiToken
      return (n, t)) with
    | .ok (n, t) =>
      assertEq n 6789 "asciiNat"
      assertEq t "xx" "token after"
    | .error e => fail s!"parse failed: {e}",
  test "expectBytes magic" do
    let png := PILean.Png.signature
    match ParseM.run (ParseM.expectBytes png "png") (png ++ "rest".toUTF8) with
    | .ok _ => pure ()
    | .error e => fail s!"good magic rejected: {e}"
    match ParseM.run (ParseM.expectBytes png "png") ("XXXXXXXX".toUTF8) with
    | .error (.badMagic "png") => pure ()
    | .error e => fail s!"wrong error: {e}"
    | .ok _ => fail "bad magic accepted",
  test "replicateByte" do
    let b := ByteArray.replicateByte 5 0xAB
    assertEq b.size 5 "size"
    assertEq (b.get! 4) 0xAB "content"
]

def prngTests : List TestCase := [
  test "splitmix64 reference vector (seed 0)" do
    let (v, _) := (SplitMix64.ofSeed 0).next
    assertEq v 0xE220A8397B1DCDAF "first output",
  test "deterministic bytes" do
    let (a, _) := (SplitMix64.ofSeed 42).bytes 64
    let (b, _) := (SplitMix64.ofSeed 42).bytes 64
    assertBytesEq a b "same seed, same bytes",
  test "random image validates" do
    for mode in [Mode.gray, .grayAlpha, .rgb, .rgba, .palette] do
      let (img, _) := (SplitMix64.ofSeed 7).image 16 9 mode
      assertTrue img.validate s!"validate {mode}"
      let _ := img.getPixel! 15 8  -- palette indices must be in range
      pure ()
]

/-- Wave-0 scaffold suite. -/
def suite : Suite :=
  { name := "scaffold"
    cases := colorTests ++ geometryTests ++ paletteTests ++ imageTests ++
             binaryTests ++ prngTests }

end Tests.ScaffoldTests
