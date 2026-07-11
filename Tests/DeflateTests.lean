import Tests.Framework
import Tests.Prng

/-!
# deflate tests

DEFLATE staged output, in-Lean inflate round trip across data classes and
levels, `Zlib` round trip, and a compression-ratio tripwire.
-/

namespace Tests.DeflateTests

open PILean
open PILean.Compress

/-! ## Data classes -/

/-- ~170-byte English-ish paragraph, repeated and trimmed to build longer
English-like text samples. -/
def sampleParagraph : String :=
  "The quick brown fox jumps over the lazy dog while the deflate window " ++
  "slides across a stream of repeated English prose, testing match-finding " ++
  "and Huffman coding at every offset and every symbol frequency it can reach. "

/-- `sampleParagraph`, repeated and trimmed to exactly `n` bytes. -/
def englishText (n : Nat) : ByteArray := Id.run do
  let para := sampleParagraph.toUTF8
  let mut out := ByteArray.emptyWithCapacity (n + para.size)
  while out.size < n do
    out := out ++ para
  return out.extract 0 n

/-- `"abc"` repeated, trimmed to exactly `n` bytes. -/
def abcRepeated (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (n + 3)
  while out.size < n do
    out := ((out.push 97).push 98).push 99
  return out.extract 0 n

/-- The data classes every round-trip/ratio test runs against. -/
def dataClasses : List (String × ByteArray) := [
  ("empty", ByteArray.empty),
  ("1 byte", ByteArray.mk #[0x42]),
  ("zeros 100k", ByteArray.replicateByte 100000 0),
  ("random 50k", ((Tests.SplitMix64.ofSeed 424242).bytes 50000).1),
  ("\"abc\" × ~3.3k (10k bytes)", abcRepeated 10000),
  ("english text ~2k", englishText 2048)
]

/-- The compression levels every round-trip test runs against. -/
def levels : List Nat := [0, 1, 6, 9]

/-! ## In-Lean round trip: `inflate (deflate d lvl) = d` -/

def deflateRoundTripTests : List TestCase :=
  dataClasses.flatMap fun (label, data) =>
    levels.map fun lvl =>
      test s!"inflate(deflate(\"{label}\", level {lvl})) = data" do
        let compressed := deflate data lvl
        match inflate compressed data.size with
        | .ok got => assertBytesEq got data s!"{label} level {lvl}"
        | .error e => fail s!"{label} level {lvl}: inflate failed: {e}"

/-! ## Zlib round trip: `Zlib.decompress (Zlib.compress d lvl) = d` -/

def zlibRoundTripTests : List TestCase :=
  dataClasses.flatMap fun (label, data) =>
    levels.map fun lvl =>
      test s!"Zlib.decompress(Zlib.compress(\"{label}\", level {lvl})) = data" do
        let compressed := Zlib.compress data lvl
        match Zlib.decompress compressed with
        | .ok got => assertBytesEq got data s!"{label} level {lvl} (zlib)"
        | .error e => fail s!"{label} level {lvl} (zlib): decompress failed: {e}"

/-! ## Compression ratio tripwires (level 6) -/

def ratioTests : List TestCase := [
  test "level-6 deflate of ~2k English text compresses to < 60% of input size" do
    let data := englishText 2048
    let compressed := deflate data 6
    assertTrue (compressed.size * 100 < data.size * 60)
      s!"compressed {compressed.size} bytes vs input {data.size} bytes (want < 60%)",
  test "level-6 deflate of 100k zeros compresses to < 1% of input size" do
    let data := ByteArray.replicateByte 100000 0
    let compressed := deflate data 6
    assertTrue (compressed.size * 100 < data.size * 1)
      s!"compressed {compressed.size} bytes vs input {data.size} bytes (want < 1%)"
]

/-- The `deflate` suite. -/
def suite : Tests.Suite :=
  { name := "deflate", cases := deflateRoundTripTests ++ zlibRoundTripTests ++ ratioTests }

end Tests.DeflateTests
