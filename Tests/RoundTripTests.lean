import Tests.Framework
import Tests.Prng
import Tests.Praw

/-!
# roundtrip tests

Cross-format decode-encode-decode properties, plus the `.praw` fixture
format's own round trip and a sanity check against a committed golden
fixture.

Owned by the `WP8` oracle/fixtures work package; the integrator may extend
`cases` with additional cross-codec properties as more codecs land.
-/

namespace Tests.RoundTripTests

open PILean

/-- `testdata/out/` is gitignored scratch space shared by every suite that
needs a real file on disk. -/
def scratchDir : System.FilePath := System.FilePath.mk "tests" / "out"

/-- `Tests.Praw.save` then `Tests.Praw.load` reconstructs an image with
identical dimensions, mode, pixel data, and (for `.palette`) palette —
for a deterministically-random image of every `Mode`. -/
def prawRoundTripTests : List TestCase :=
  [Mode.gray, .grayAlpha, .rgb, .rgba, .palette].map fun mode =>
    test s!"praw save/load round trip ({mode})" do
      IO.FS.createDirAll scratchDir
      let (img, _) := (SplitMix64.ofSeed (17 + mode.bytesPerPixel)).image 11 7 mode
      let path := scratchDir / s!"praw_roundtrip_{mode}.praw"
      Tests.Praw.save path img
      let img' ← Tests.Praw.load path
      assertEq img'.width img.width "width"
      assertEq img'.height img.height "height"
      assertEq img'.mode img.mode "mode"
      assertBytesEq img'.data img.data "pixel data"
      match img.palette?, img'.palette? with
      | some p, some p' => assertBytesEq p'.entries p.entries "palette entries"
      | none, none => pure ()
      | _, _ => fail "palette-presence mismatch after round trip"
      assertImagesEq img' img "pixel-exact (RGBA promotion)"

/-- `Tests.Praw.load` on a committed golden fixture matches specific pixel
values recorded by `testdata/py/gen_golden.py` (see
`testdata/golden/MANIFEST.md`, "Hardcoded pixel values" — regenerate that
table and update this test together if the pattern generator ever
changes). -/
def goldenLoadTest : TestCase :=
  test "load committed golden hgradient_rgb_16x16.praw" do
    let img ← Tests.Praw.load (goldenDir / "hgradient_rgb_16x16.praw")
    assertEq img.width 16 "width"
    assertEq img.height 16 "height"
    assertEq img.mode Mode.rgb "mode"
    assertEq (img.getPixel! 0 0) (Color.rgb 0 85 170) "(0,0)"
    assertEq (img.getPixel! 15 0) (Color.rgb 255 84 169) "(15,0)"
    assertEq (img.getPixel! 0 15) (Color.rgb 0 85 170) "(0,15)"
    assertEq (img.getPixel! 15 15) (Color.rgb 255 84 169) "(15,15)"
    assertEq (img.getPixel! 7 3) (Color.rgb 119 204 33) "(7,3)"

/-- The `roundtrip` suite. -/
def suite : Tests.Suite :=
  { name := "roundtrip"
    cases := prawRoundTripTests ++ [goldenLoadTest] }

end Tests.RoundTripTests
