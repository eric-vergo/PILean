import Tests.Framework
import Tests.Prng

/-!
# checksum tests

CRC-32 and Adler-32 (known vectors, chaining, BitReader/BitWriter). Owned by WP2 — that work package fills in `cases`.
-/

namespace Tests.ChecksumTests

open PILean PILean.Compress

/-- ASCII bytes of a `String` (test convenience). -/
private def bytesOf (s : String) : ByteArray := s.toUTF8

def knownVectorTests : List TestCase := [
  test "crc32 \"123456789\" matches the CRC-32/ISO-HDLC check value" do
    assertEq (crc32 (bytesOf "123456789")) 0xCBF43926 "crc32",
  test "adler32 \"123456789\" matches zlib.adler32" do
    -- python3: zlib.adler32(b"123456789") == 0x091e01de
    assertEq (adler32 (bytesOf "123456789")) 0x091E01DE "adler32",
  test "empty input" do
    assertEq (crc32 ByteArray.empty) 0 "crc32 empty"
    assertEq (adler32 ByteArray.empty) 1 "adler32 empty",
  test "single byte 'a'" do
    -- python3: zlib.crc32(b"a") == 0xe8b7be43, zlib.adler32(b"a") == 0x00620062
    assertEq (crc32 (bytesOf "a")) 0xE8B7BE43 "crc32 'a'"
    assertEq (adler32 (bytesOf "a")) 0x00620062 "adler32 'a'"
]

def chainingTests : List TestCase := [
  test "crc32 chains across buffers" do
    let mut g := SplitMix64.ofSeed 101
    for trial in [0:20] do
      let (data, g') := g.bytes (200 + trial * 37)
      g := g'
      let k := data.size / 2
      let a := data.extract 0 k
      let b := data.extract k data.size
      let whole := crc32 data
      let chained := crc32 b (crc32 a)
      assertEq chained whole s!"trial {trial}: crc32 chaining",
  test "adler32 chains across buffers" do
    let mut g := SplitMix64.ofSeed 202
    for trial in [0:20] do
      let (data, g') := g.bytes (200 + trial * 41)
      g := g'
      let k := data.size / 3
      let a := data.extract 0 k
      let b := data.extract k data.size
      let whole := adler32 data
      let chained := adler32 b (adler32 a)
      assertEq chained whole s!"trial {trial}: adler32 chaining",
  test "chaining holds at every split point of one buffer" do
    let (data, _) := (SplitMix64.ofSeed 303).bytes 300
    let whole := crc32 data
    let wholeA := adler32 data
    for k in [0:301] do
      let a := data.extract 0 k
      let b := data.extract k data.size
      assertEq (crc32 b (crc32 a)) whole s!"split at {k}: crc32"
      assertEq (adler32 b (adler32 a)) wholeA s!"split at {k}: adler32"
]

def largeBufferTests : List TestCase := [
  test "256 KiB random buffer completes quickly and is self-consistent" do
    let (data, _) := (SplitMix64.ofSeed 7).bytes (256 * 1024)
    let t0 ← IO.monoMsNow
    let c := crc32 data
    let a := adler32 data
    let t1 ← IO.monoMsNow
    -- Sanity: chaining still holds on a real-sized buffer.
    let half := data.size / 2
    let lo := data.extract 0 half
    let hi := data.extract half data.size
    assertEq (crc32 hi (crc32 lo)) c "crc32 chaining on 256 KiB buffer"
    assertEq (adler32 hi (adler32 lo)) a "adler32 chaining on 256 KiB buffer"
    -- A table-driven crc32 and NMAX-batched adler32 over 256 KiB should
    -- take single-digit milliseconds; a per-byte allocating loop would not.
    assertTrue (t1 - t0 < 2000) s!"crc32+adler32 over 256 KiB took {t1 - t0}ms (suspiciously slow)"
]

/-- The `checksum` suite (WP2). -/
def suite : Tests.Suite :=
  { name := "checksum"
    cases := knownVectorTests ++ chainingTests ++ largeBufferTests }

end Tests.ChecksumTests
