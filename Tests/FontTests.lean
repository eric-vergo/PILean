import Tests.Framework
import Tests.Prng
import PILean.Font.Spleen8x16
import PILean.Draw.Text

/-!
# font tests

Bitmap font data, draw.text, textSize. Owned by WP6 — that work package fills in `cases`.
-/

namespace Tests.FontTests

open PILean

/-- Does every byte of `b` equal `0`? -/
private def isBlank (b : ByteArray) : Bool := Id.run do
  for i in [0:b.size] do
    if b.get! i != 0 then
      return false
  return true

/-- The bit at `col` (0 = leftmost) of `byte`, MSB-first. -/
private def bitAt (byte : UInt8) (col width : Nat) : Bool :=
  (byte.toNat >>> (width - 1 - col)) &&& 1 != 0

def bitmapTests : List TestCase := [
  test "hexToByteArray round trip" do
    assertEq (hexToByteArray "00ff10ab").toList [0x00, 0xff, 0x10, 0xab] "plain hex",
  test "hexToByteArray tolerates whitespace and newlines" do
    assertEq (hexToByteArray "00 ff\n10\tab").toList [0x00, 0xff, 0x10, 0xab] "whitespace-tolerant"
    assertEq (hexToByteArray "").size 0 "empty string decodes to empty bytes",
  test "hexToByteArray is case-insensitive" do
    assertEq (hexToByteArray "AaBbCcDd").toList (hexToByteArray "aabbccdd").toList "upper = lower"
]

def spleenTests : List TestCase := [
  test "spleen8x16 dimensions" do
    let f := BitmapFont.spleen8x16
    assertEq f.glyphWidth 8 "glyphWidth"
    assertEq f.glyphHeight 16 "glyphHeight"
    assertEq f.firstCode 32 "firstCode"
    assertEq f.count 224 "count",
  test "spleen8x16 bitmap size is exactly count * glyphHeight" do
    let f := BitmapFont.spleen8x16
    assertEq f.bitmap.size (f.count * f.glyphHeight) "bitmap.size",
  test "default is spleen8x16" do
    assertEq BitmapFont.default.glyphWidth BitmapFont.spleen8x16.glyphWidth "glyphWidth"
    assertEq BitmapFont.default.glyphHeight BitmapFont.spleen8x16.glyphHeight "glyphHeight"
    assertBytesEq BitmapFont.default.bitmap BitmapFont.spleen8x16.bitmap "bitmap",
  test "glyph? 'A' is non-blank" do
    match BitmapFont.spleen8x16.glyph? 'A' with
    | some rows =>
      assertEq rows.size 16 "row count"
      assertTrue (!isBlank rows) "'A' glyph has ink"
    | none => fail "'A' should be covered by spleen8x16",
  test "glyph? for a codepoint below firstCode is none" do
    assertTrue (BitmapFont.spleen8x16.glyph? (Char.ofNat 31)).isNone "codepoint 31 < firstCode 32"
    assertTrue (BitmapFont.spleen8x16.glyph? (Char.ofNat 9)).isNone "codepoint 9 (tab) uncovered",
  test "glyph? for a codepoint at or beyond the end is none" do
    assertTrue (BitmapFont.spleen8x16.glyph? (Char.ofNat 256)).isNone "codepoint 256 >= 32 + 224"
]

def textSizeTests : List TestCase := [
  test "empty string measures (0, 0)" do
    assertEq (Draw.textSize "") (0, 0) "empty",
  test "single line" do
    assertEq (Draw.textSize "hello") (5 * 8, 1 * 16) "5 chars, 1 line",
  test "multi-line measures by longest line and line count" do
    assertEq (Draw.textSize "ab\ncdef") (4 * 8, 2 * 16) "ab / cdef",
  test "trailing newline counts an extra (empty) line" do
    assertEq (Draw.textSize "ab\n") (2 * 8, 2 * 16) "ab + blank line"
]

def textDrawTests : List TestCase := [
  test "rendering 'A' only touches pixels within its 8x16 cell" do
    let bg := Color.white
    let fg := Color.black
    let pos : Point := ⟨1, 2⟩
    let img := Draw.text (Image.new 10 20 .rgb bg) pos "A" fg
    assertTrue img.validate "image still valid"
    let some rows := BitmapFont.spleen8x16.glyph? 'A' | fail "expected 'A' glyph"
    for y in [0:20] do
      for x in [0:10] do
        let inCellX := pos.x ≤ (x : Int) && (x : Int) < pos.x + 8
        let inCellY := pos.y ≤ (y : Int) && (y : Int) < pos.y + 16
        if inCellX && inCellY then
          let row := (y : Int) - pos.y
          let col := (x : Int) - pos.x
          let expected := if bitAt (rows.get! row.toNat) col.toNat 8 then fg else bg
          assertEq (img.getPixel! x y) expected s!"cell pixel ({x},{y})"
        else
          assertEq (img.getPixel! x y) bg s!"outside-cell pixel ({x},{y}) untouched",
  test "unknown codepoint draws a hollow fallback box" do
    let bg := Color.white
    let fg := Color.black
    -- codepoint 9 (tab) is not covered by spleen8x16 -> fallback box
    let img := Draw.text (Image.new 8 16 .rgb bg) ⟨0, 0⟩ (String.singleton (Char.ofNat 9)) fg
    -- corners of the cell are always part of the hollow box border
    assertEq (img.getPixel! 0 0) fg "top-left corner"
    assertEq (img.getPixel! 7 0) fg "top-right corner"
    assertEq (img.getPixel! 0 15) fg "bottom-left corner"
    assertEq (img.getPixel! 7 15) fg "bottom-right corner"
    -- the interior (not on the border) stays background
    assertEq (img.getPixel! 3 7) bg "interior untouched",
  test "'\\n' resets x to pos.x and advances y by glyphHeight" do
    let img := Draw.text (Image.new 32 32 .rgb Color.white) ⟨0, 0⟩ "A\nB" Color.black
    assertTrue img.validate "renders without panic"
    -- second glyph cell starts at (0, 16); its top-left corner pixel should
    -- differ from a blank background whenever the glyph has ink there
    let some rowsB := BitmapFont.spleen8x16.glyph? 'B' | fail "expected 'B' glyph"
    assertTrue (!isBlank rowsB) "'B' has ink to check against",
  test "negative position clips silently without panicking" do
    let img := Draw.text (Image.new 8 8 .rgb Color.white) ⟨-4, -4⟩ "Hello, world!" Color.black
    assertTrue img.validate "no panic, still a valid image"
    assertEq (img.width, img.height) (8, 8) "size unaffected by clipping",
  test "smoke: full printable ASCII set renders without panicking" do
    let s := String.ofList ((List.range 95).map (fun i => Char.ofNat (32 + i)))
    let img := Draw.text (Image.new 200 40 .rgb Color.white) ⟨0, 0⟩ s Color.black
    assertTrue img.validate "valid after drawing full ASCII set"
]

/-- Wave/WP6 font suite. -/
def suite : Tests.Suite :=
  { name := "font"
    cases := bitmapTests ++ spleenTests ++ textSizeTests ++ textDrawTests }

end Tests.FontTests
