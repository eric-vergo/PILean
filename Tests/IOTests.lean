import Tests.Framework
import Tests.Prng
import Tests.Praw

/-!
# io tests

Sniffing dispatch, extension fallback, load/save through the real end-to-end
`PILean.IO` layer (`Image.load`/`Image.save`/`Image.decodeAuto`/
`Codec.forExtension?`), plus the `export-for-crosscheck` case that feeds
`testdata/py/crosscheck.py`. Owned by WP13.

Every codec's own `sniff` here is a strict subset of what its `decode`
requires (every codec checks its magic bytes as literally the first parse
step), so genuinely valid content for a format *always* sniffs successfully
— there is no way to construct real, decodable content that reaches the
extension-fallback branch of `Image.load`. The extension-fallback tests
below instead use bytes that satisfy no codec's `sniff` (so the fallback
branch is what runs) and check that the *extension*-selected codec's own
decoder is what reports the resulting error (not a generic "unrecognized
format"), which is what actually demonstrates the fallback dispatch working.
-/

namespace Tests.IOTests

open PILean

/-- Scratch directory for this suite's own read/write round trips. -/
def ioScratchDir : System.FilePath := System.FilePath.mk "testdata" / "out" / "io"

def roundTripTests : List TestCase := [
  test "ppm round trip (.rgb)" do
    IO.FS.createDirAll ioScratchDir
    let (img, _) := (SplitMix64.ofSeed 6001).image 9 7 .rgb
    let path := ioScratchDir / "roundtrip_rgb.ppm"
    img.save path
    let img' ← Image.load path
    assertImagesEq img' img "ppm round trip",
  test "pgm round trip (.gray)" do
    IO.FS.createDirAll ioScratchDir
    let (img, _) := (SplitMix64.ofSeed 6002).image 8 6 .gray
    let path := ioScratchDir / "roundtrip_gray.pgm"
    img.save path
    let img' ← Image.load path
    assertImagesEq img' img "pgm round trip",
  test "bmp round trip (.rgba)" do
    IO.FS.createDirAll ioScratchDir
    let (img, _) := (SplitMix64.ofSeed 6003).image 5 5 .rgba
    let path := ioScratchDir / "roundtrip_rgba.bmp"
    img.save path
    let img' ← Image.load path
    assertImagesEq img' img "bmp round trip",
  test "qoi round trip (.rgba)" do
    IO.FS.createDirAll ioScratchDir
    let (img, _) := (SplitMix64.ofSeed 6004).image 11 9 .rgba
    let path := ioScratchDir / "roundtrip_rgba.qoi"
    img.save path
    let img' ← Image.load path
    assertImagesEq img' img "qoi round trip",
  test "qoi round trip (.rgb)" do
    IO.FS.createDirAll ioScratchDir
    let (img, _) := (SplitMix64.ofSeed 6005).image 6 13 .rgb
    let path := ioScratchDir / "roundtrip_rgb.qoi"
    img.save path
    let img' ← Image.load path
    assertImagesEq img' img "qoi round trip"
]

def sniffDispatchTests : List TestCase := [
  test "decodeAuto picks the qoi codec by content alone" do
    let (img, _) := (SplitMix64.ofSeed 6011).image 6 4 .rgb
    match Qoi.encode img with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      match Image.decodeAuto bytes with
      | .error e => fail s!"decodeAuto failed: {e}"
      | .ok img' => assertImagesEq img' img "decodeAuto qoi bytes",
  test "decodeAuto picks the bmp codec by content alone" do
    let (img, _) := (SplitMix64.ofSeed 6012).image 6 4 .rgb
    match Bmp.encode img with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      match Image.decodeAuto bytes with
      | .error e => fail s!"decodeAuto failed: {e}"
      | .ok img' => assertImagesEq img' img "decodeAuto bmp bytes",
  test "Image.load ignores a misleading extension when content sniffs unambiguously" do
    IO.FS.createDirAll ioScratchDir
    let (img, _) := (SplitMix64.ofSeed 6013).image 7 5 .rgb
    match Qoi.encode img with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      -- Real QOI bytes, saved with a deliberately wrong ".bmp" extension.
      let path := ioScratchDir / "misleading.bmp"
      IO.FS.writeBinFile path bytes
      let img' ← Image.load path
      assertImagesEq img' img "load via content sniff despite .bmp extension",
  test "Image.load ignores an unregistered extension when content sniffs unambiguously" do
    IO.FS.createDirAll ioScratchDir
    let (img, _) := (SplitMix64.ofSeed 6014).image 4 4 .rgba
    match Qoi.encode img with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      let path := ioScratchDir / "no_extension_hint.bin"
      IO.FS.writeBinFile path bytes
      let img' ← Image.load path
      assertImagesEq img' img "load via content sniff with an unregistered extension"
]

def extensionLookupTests : List TestCase := [
  test "Codec.forExtension? resolves every registered extension, case-insensitively" do
    assertEq ((Codec.forExtension? ".ppm").map (·.name)) (some "netpbm") "ppm"
    assertEq ((Codec.forExtension? "pgm").map (·.name)) (some "netpbm") "pgm (no leading dot)"
    assertEq ((Codec.forExtension? ".BMP").map (·.name)) (some "bmp") "bmp (case-insensitive)"
    assertEq ((Codec.forExtension? ".Qoi").map (·.name)) (some "qoi") "qoi (mixed case)"
    assertTrue (Codec.forExtension? ".xyz").isNone "unregistered extension resolves to none"
]

def errorPathTests : List TestCase := [
  test "content that sniffs as nothing, with an unregistered extension, is unknownFormat" do
    IO.FS.createDirAll ioScratchDir
    let garbage : ByteArray := "this is definitely not an image".toUTF8
    let path := ioScratchDir / "garbage.xyz"
    IO.FS.writeBinFile path garbage
    try
      let _ ← Image.load path
      fail "expected load to fail for unrecognized content and extension"
    catch e =>
      assertTrue (strContains (toString e) "unrecognized image format")
        s!"expected an unknownFormat error, got: {e}",
  test "extension fallback: content that sniffs as nothing still reaches that \
        extension's own decoder (not a generic unknownFormat)" do
    IO.FS.createDirAll ioScratchDir
    let garbage : ByteArray := ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    let path := ioScratchDir / "fallback.bmp"
    IO.FS.writeBinFile path garbage
    try
      let _ ← Image.load path
      fail "expected load to fail for garbage bmp content"
    catch e =>
      assertTrue (strContains (toString e) "bmp")
        s!"expected a bmp-specific error (extension fallback reached Bmp.decode), got: {e}",
  test "correct extension, truncated content errors cleanly (never panics)" do
    IO.FS.createDirAll ioScratchDir
    let (img, _) := (SplitMix64.ofSeed 6020).image 4 4 .rgb
    match Qoi.encode img with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes =>
      let truncated := bytes.extract 0 (bytes.size / 2)
      let path := ioScratchDir / "truncated.qoi"
      IO.FS.writeBinFile path truncated
      try
        let _ ← Image.load path
        fail "expected load to fail on truncated content"
      catch _ => pure ()
]

def formatOverrideTests : List TestCase := [
  test "Image.save format? override writes qoi content to a non-.qoi path" do
    IO.FS.createDirAll ioScratchDir
    let (img, _) := (SplitMix64.ofSeed 6030).image 5 5 .rgba
    let path := ioScratchDir / "override.bin"
    img.save path (format? := some "qoi")
    let bytes ← IO.FS.readBinFile path
    assertTrue (Qoi.codec.sniff bytes) "output sniffs as qoi despite the .bin path"
    -- The extension isn't registered, but content sniffing finds it anyway.
    let img' ← Image.load path
    assertImagesEq img' img "round trip via format override"
]

/-- Does every entry of `p` have full opacity? BMP's 8-bit palette has no
alpha channel at all (its 4th palette byte is a reserved/ignored field, not
opacity — see `PILean.Bmp`'s module docstring), so a `.palette` image with
any non-opaque entry (the `*_transparency` golden variants) cannot round
trip through BMP losslessly; only fully-opaque palettes can. -/
private def isFullyOpaquePalette (p : Palette) : Bool := Id.run do
  for i in [0:p.size] do
    if (p.get! i).a != 255 then
      return false
  return true

/-- Which extensions `img` can be losslessly written to today (matching
what each codec can actually round-trip exactly): `.rgb` → ppm/bmp/qoi,
`.gray` → pgm/bmp, `.palette` → bmp (only if every entry is opaque — see
`isFullyOpaquePalette`), `.rgba` → qoi. `.grayAlpha` has no lossless target
yet, so it exports nothing (see `crosscheckExportTest`). -/
private def exportTargets (img : Image) : List String :=
  match img.mode with
  | .rgb => ["ppm", "bmp", "qoi"]
  | .gray => ["pgm", "bmp"]
  | .palette =>
    match img.palette? with
    | some p => if isFullyOpaquePalette p then ["bmp"] else []
    | none => []
  | .rgba => ["qoi"]
  | .grayAlpha => []

/-- Loads every `testdata/golden/*.praw` fixture and re-saves each through
every format it can round-trip losslessly today, into
`testdata/out/<goldenname>.<ext>`, so `python3 testdata/py/crosscheck.py`
can validate PILean's writers against Pillow. `.grayAlpha` goldens produce
no exports (no lossless `.grayAlpha` writer exists yet) — that's expected,
not a failure. -/
def crosscheckExportTest : TestCase :=
  test "export-for-crosscheck" do
    let crosscheckOutDir := System.FilePath.mk "testdata" / "out"
    IO.FS.createDirAll crosscheckOutDir
    let entries ← Tests.goldenDir.readDir
    let prawEntries := entries.filter fun e => e.fileName.endsWith ".praw"
    assertTrue (prawEntries.size > 0) "expected committed golden .praw fixtures to exist"
    let mut exported := 0
    for e in prawEntries do
      match e.path.fileStem with
      | none => fail s!"golden fixture with no file stem: {e.path}"
      | some stem =>
        let img ← Tests.Praw.load e.path
        for ext in exportTargets img do
          img.save (crosscheckOutDir / s!"{stem}.{ext}")
          exported := exported + 1
    IO.println s!"       [exported {exported} file(s) from {prawEntries.size} golden fixture(s)]"

/-- The `io` suite (WP13). -/
def suite : Tests.Suite :=
  { name := "io"
    cases := roundTripTests ++ sniffDispatchTests ++ extensionLookupTests ++
      errorPathTests ++ formatOverrideTests ++ [crosscheckExportTest] }

end Tests.IOTests
