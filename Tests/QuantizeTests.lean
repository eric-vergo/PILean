import Tests.Framework
import Tests.Prng

/-!
# quantize tests

Median-cut properties (never compared to Pillow's quantizer — see
`PILean.Color.Quantize`'s module docstring). Owned by WP13.
-/

namespace Tests.QuantizeTests

open PILean

/-- Compare pixel colors only (`Image.quantize` always produces `.palette`
mode, so a mode-checking comparison would never apply here). -/
private def assertColorsEq (actual expected : Image) (label : String := "image") : IO Unit := do
  unless actual.width == expected.width && actual.height == expected.height do
    fail (s!"{label}: size mismatch — got {actual.width}×{actual.height}, " ++
      s!"expected {expected.width}×{expected.height}")
  for y in [0:actual.height] do
    for x in [0:actual.width] do
      assertEq (actual.getPixel! x y) (expected.getPixel! x y) s!"{label} ({x},{y})"

/-- Squared distance between two colors' RGB channels (alpha ignored — see
`Image.quantize`'s "alpha folded to 255" note). -/
private def sqDist (a b : Color) : Nat :=
  let d (u v : UInt8) : Nat := let n := if u ≥ v then (u - v).toNat else (v - u).toNat; n * n
  d a.r b.r + d a.g b.g + d a.b b.b

/-- Mean squared per-channel error between `img` and `img.quantize colors`,
comparing every pixel's promoted RGB color. -/
private def quantizeMse (img : Image) (colors : Nat) : Float := Id.run do
  let q := img.quantize colors
  let mut se : Nat := 0
  let mut n : Nat := 0
  for y in [0:img.height] do
    for x in [0:img.width] do
      se := se + sqDist (img.getPixel! x y) (q.getPixel! x y)
      n := n + 3
  return if n == 0 then 0.0 else Float.ofNat se / Float.ofNat n

/-- A `width × height` image cycling through exactly `n` distinct grayscale
shades (`n ≤ 16` keeps the shades ≤ 255 apart), for exact-fast-path tests. -/
private def cyclingShades (width height n : Nat) : Image := Id.run do
  let mut img := Image.new width height .rgb
  for y in [0:height] do
    for x in [0:width] do
      let idx := (x + y * width) % n
      let v := UInt8.ofNat (idx * (255 / (max 1 (n - 1))))
      img := img.putPixel x y (Color.rgb v v v)
  return img

/-- A `size × size` gradient with exactly `size * size` distinct colors
(the `r` channel alone is a bijection with the pixel index). -/
private def distinctGradient (size : Nat) : Image := Id.run do
  let mut img := Image.new size size .rgb
  for y in [0:size] do
    for x in [0:size] do
      let idx := y * size + x
      let r := UInt8.ofNat idx
      let g := UInt8.ofNat (255 - idx % 256)
      let b := UInt8.ofNat ((idx * 3) % 256)
      img := img.putPixel x y (Color.rgb r g b)
  return img

def exactPaletteTests : List TestCase := [
  test "16-color image quantized to 16 colors: exact palette, exact reconstruction" do
    let img := cyclingShades 8 8 16
    let q := img.quantize 16
    assertEq q.mode Mode.palette "mode"
    match q.palette? with
    | none => fail "expected a palette"
    | some p => assertEq p.size 16 "palette size"
    assertColorsEq q img "exact reconstruction",
  test "image smaller than the requested color count uses the exact fast path" do
    -- Only 3 distinct colors, but 200 requested: palette must not be padded.
    let img := cyclingShades 5 5 3
    let q := img.quantize 200
    match q.palette? with
    | none => fail "expected a palette"
    | some p => assertEq p.size 3 "palette size (not padded to 200)"
    assertColorsEq q img "exact reconstruction",
  test "single-pixel image" do
    let img := Image.new 1 1 .rgb Color.red
    let q := img.quantize 256
    match q.palette? with
    | none => fail "expected a palette"
    | some p => assertEq p.size 1 "palette size"
    assertColorsEq q img "exact reconstruction"
]

def clampTests : List TestCase := [
  test "colors = 0 clamps to a legal 1-color quantize" do
    let img := distinctGradient 6
    let q := img.quantize 0
    match q.palette? with
    | none => fail "expected a palette"
    | some p => assertEq p.size 1 "palette size",
  test "colors = 1 is a legal 1-color quantize" do
    let img := distinctGradient 6
    let q := img.quantize 1
    match q.palette? with
    | none => fail "expected a palette"
    | some p => assertEq p.size 1 "palette size"
]

def paletteSizeBoundTests : List TestCase := [
  test "palette size never exceeds `colors`, across modes and targets" do
    let modes : List Mode := [.gray, .grayAlpha, .rgb, .rgba, .palette]
    let targets : List Nat := [1, 2, 5, 16, 64, 300]
    let mut g := SplitMix64.ofSeed 5001
    for m in modes do
      for target in targets do
        let (img, g') := g.image 17 13 m
        g := g'
        let q := img.quantize target
        match q.palette? with
        | none => fail s!"mode {m} target {target}: expected a palette"
        | some p =>
          assertTrue (p.size ≤ min 256 target)
            s!"mode {m} target {target}: palette size {p.size} exceeds {min 256 target}"
          assertTrue (p.size ≥ 1) s!"mode {m} target {target}: palette must have ≥ 1 entry"
]

def modeTests : List TestCase := [
  test "quantize works on every input mode" do
    let modes : List Mode := [.gray, .grayAlpha, .rgb, .rgba, .palette]
    let mut g := SplitMix64.ofSeed 5002
    for m in modes do
      let (img, g') := g.image 10 10 m
      g := g'
      let q := img.quantize 8
      assertEq q.mode Mode.palette s!"mode {m}: output mode"
      assertTrue q.validate s!"mode {m}: output image validates"
      match q.palette? with
      | none => fail s!"mode {m}: expected a palette"
      | some p => assertTrue (p.size ≤ 8) s!"mode {m}: palette size ≤ 8",
  test "re-quantizing a .palette image (promotion round trip)" do
    let (img, _) := (SplitMix64.ofSeed 5003).image 20 20 .palette
    let q := img.quantize 32
    assertEq q.mode Mode.palette "mode"
    match q.palette? with
    | none => fail "expected a palette"
    | some p => assertTrue (p.size ≤ 32) "palette size ≤ 32"
]

def mseTests : List TestCase := [
  test "256-color gradient quantized to 16 colors stays under a loose MSE bound" do
    let img := distinctGradient 16  -- 16x16 = 256 distinct colors
    let mse := quantizeMse img 16
    assertTrue (mse < 500.0) s!"MSE {mse} exceeds the loose bound of 500"
]

/-- The `quantize` suite (WP13). -/
def suite : Tests.Suite :=
  { name := "quantize"
    cases := exactPaletteTests ++ clampTests ++ paletteSizeBoundTests ++ modeTests ++ mseTests }

end Tests.QuantizeTests
