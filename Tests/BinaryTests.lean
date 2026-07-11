import Tests.Framework
import Tests.Prng

/-!
# binary tests

Extra Binary reader/writer coverage beyond the scaffold suite. Owned by WP2 — that work package fills in `cases`.
-/

namespace Tests.BinaryTests

open PILean PILean.Binary PILean.Compress

def bitStreamKnownValueTests : List TestCase := [
  test "byte 0b10110010 decomposes as 3+5 bits LSB-first" do
    let data := ByteArray.empty.push 0b10110010
    let r : BitReader := { data := data }
    match r.readBits 3 with
    | .error e => fail s!"unexpected error on first read: {e}"
    | .ok (v3, r1) =>
      assertEq v3 2 "low 3 bits"
      match r1.readBits 5 with
      | .error e => fail s!"unexpected error on second read: {e}"
      | .ok (v5, r2) =>
        assertEq v5 22 "high 5 bits"
        assertEq r2.pos 1 "fully consumed the one byte",
  test "readBits 0 never fails and never advances" do
    let r : BitReader := { data := ByteArray.empty }
    match r.readBits 0 with
    | .ok (v, r') =>
      assertEq v 0 "zero-width read yields 0"
      assertEq r'.pos 0 "position unchanged"
      assertEq r'.bitCnt 0 "bit count unchanged"
    | .error e => fail s!"unexpected error: {e}",
  test "readBits spanning multiple bytes" do
    -- 0x01, 0x02: bits (LSB-first) are byte0's 8 bits then byte1's 8 bits.
    -- Reading 12 bits should yield byte0 in the low 8 bits and the low
    -- nibble of byte1 in the high 4 bits: 0x01 | (0x02 << 8) = 0x201.
    let data := ByteArray.empty.push 0x01 |>.push 0x02
    let r : BitReader := { data := data }
    match r.readBits 12 with
    | .ok (v, r') =>
      assertEq v 0x201 "12-bit value spans both bytes"
      assertEq r'.pos 2 "both bytes loaded"
      assertEq r'.bitCnt 4 "4 leftover bits buffered"
    | .error e => fail s!"unexpected error: {e}"
]

def bitStreamRoundTripTests : List TestCase := [
  test "BitWriter -> BitReader round trip of random (value, width) pairs" do
    let mut g := SplitMix64.ofSeed 55
    let mut widths : Array Nat := #[]
    let mut values : Array UInt32 := #[]
    let mut w : BitWriter := {}
    for _ in [0:500] do
      let (wr, g1) := g.next
      let width := wr.toNat % 25  -- 0..24
      let (vr, g2) := g1.next
      let mask : UInt32 := if width == 0 then 0 else ((1 : UInt32) <<< UInt32.ofNat width) - 1
      let value := vr.toUInt32 &&& mask
      widths := widths.push width
      values := values.push value
      w := w.writeBits value width
      g := g2
    let bytes := w.toByteArray
    let mut r : BitReader := { data := bytes }
    for i in [0:widths.size] do
      match r.readBits widths[i]! with
      | .ok (v, r') =>
        assertEq v values[i]! s!"pair {i} (width {widths[i]!})"
        r := r'
      | .error e => fail s!"pair {i}: unexpected error {e}",
  test "many small writes pack tightly (bit count matches byte count)" do
    -- 800 single bits should pack into exactly 100 bytes.
    let mut w : BitWriter := {}
    let mut g := SplitMix64.ofSeed 9
    let mut bits : Array UInt32 := #[]
    for _ in [0:800] do
      let (v, g') := g.next
      g := g'
      let bit := v.toUInt32 &&& 1
      bits := bits.push bit
      w := w.writeBits bit 1
    let bytes := w.toByteArray
    assertEq bytes.size 100 "tightly packed size"
    let mut r : BitReader := { data := bytes }
    for i in [0:bits.size] do
      match r.readBits 1 with
      | .ok (v, r') => assertEq v bits[i]! s!"bit {i}"; r := r'
      | .error e => fail s!"bit {i}: unexpected error {e}"
]

def alignByteTests : List TestCase := [
  test "BitReader.alignByte discards partial-byte bits then reads whole bytes" do
    let data := ByteArray.empty.push 0xAB |>.push 0x12 |>.push 0x34 |>.push 0x56
    let r : BitReader := { data := data }
    match r.readBits 3 with
    | .error e => fail s!"unexpected error: {e}"
    | .ok (_, r1) =>
      let r2 := r1.alignByte
      assertEq r2.bitCnt 0 "no buffered bits after align"
      match r2.readBytes 3 with
      | .ok (bs, _) =>
        assertBytesEq bs (ByteArray.empty.push 0x12 |>.push 0x34 |>.push 0x56) "bytes after align"
      | .error e => fail s!"unexpected error: {e}",
  test "BitReader.alignByte is a no-op already on a byte boundary" do
    let r : BitReader := { data := ByteArray.empty.push 1 |>.push 2 }
    let r' := r.alignByte
    assertEq r'.bitCnt 0 "still zero"
    assertEq r'.pos r.pos "position unchanged",
  test "BitWriter.alignByte flushes a zero-padded partial byte" do
    let w : BitWriter := {}
    let w1 := w.writeBits 5 3    -- 0b101 in the low 3 bits
    let w2 := w1.alignByte
    assertEq w2.out.size 1 "one byte flushed"
    assertEq (w2.out.get! 0) 5 "high bits zero-padded"
    let w3 := w2.writeBits 6 3
    let final := w3.toByteArray
    assertBytesEq final (ByteArray.empty.push 5 |>.push 6) "second byte flushed by toByteArray",
  test "BitWriter.alignByte is a no-op already on a byte boundary" do
    let w : BitWriter := {}
    let w1 := w.alignByte
    assertEq w1.out.size 0 "nothing flushed"
    assertEq w1.bitCnt 0 "still zero"
]

def truncationTests : List TestCase := [
  test "BitReader.readBits past end truncates" do
    let r : BitReader := { data := ByteArray.empty }
    match r.readBits 5 with
    | .error (.truncated ..) => pure ()
    | .error e => fail s!"wrong error: {e}"
    | .ok _ => fail "expected truncation on empty input",
  test "BitReader.readBits truncates when only a partial byte remains" do
    let r : BitReader := { data := ByteArray.empty.push 0xFF }
    match r.readBits 10 with
    | .error (.truncated ..) => pure ()
    | .error e => fail s!"wrong error: {e}"
    | .ok _ => fail "expected truncation with only 8 bits available",
  test "BitReader.readBytes past end truncates" do
    let r : BitReader := { data := ByteArray.empty.push 1 |>.push 2 }
    match r.readBytes 5 with
    | .error (.truncated ..) => pure ()
    | .error e => fail s!"wrong error: {e}"
    | .ok _ => fail "expected truncation"
]

def parseEdgeTests : List TestCase := [
  test "remaining/isEof track position" do
    let b := ByteArray.empty.push 1 |>.push 2 |>.push 3
    match ParseM.run (data := b) (do
      let r0 ← ParseM.remaining
      let e0 ← ParseM.isEof
      let _ ← ParseM.u8
      let r1 ← ParseM.remaining
      let _ ← ParseM.take 2
      let e1 ← ParseM.isEof
      return (r0, e0, r1, e1)) with
    | .ok (r0, e0, r1, e1) =>
      assertEq r0 3 "remaining before read"
      assertEq e0 false "not eof initially"
      assertEq r1 2 "remaining after one byte"
      assertEq e1 true "eof after consuming all"
    | .error e => fail s!"parse failed: {e}",
  test "peek? does not advance, none at eof" do
    match ParseM.run (data := ByteArray.empty.push 9) (do
      let p0 ← ParseM.peek?
      let p1 ← ParseM.peek?
      let _ ← ParseM.u8
      let p2 ← ParseM.peek?
      return (p0, p1, p2)) with
    | .ok (p0, p1, p2) =>
      assertEq p0 (some 9) "peek before consume"
      assertEq p1 (some 9) "peek does not advance"
      assertEq p2 none "peek at eof"
    | .error e => fail s!"parse failed: {e}",
  test "skip past end truncates" do
    match ParseM.run (ParseM.skip 5) (ByteArray.empty.push 1 |>.push 2) with
    | .ok _ => fail "expected truncation"
    | .error (.truncated ..) => pure ()
    | .error e => fail s!"wrong error: {e}",
  test "take exact remaining succeeds; take past end truncates" do
    let b := ByteArray.empty.push 1 |>.push 2 |>.push 3
    match ParseM.run (ParseM.take 3) b with
    | .ok bs => assertBytesEq bs b "take all"
    | .error e => fail s!"unexpected error: {e}"
    match ParseM.run (ParseM.take 4) b with
    | .ok _ => fail "expected truncation"
    | .error (.truncated ..) => pure ()
    | .error e => fail s!"wrong error: {e}",
  test "expectBytes on short input reports badMagic, not truncated" do
    match ParseM.run (ParseM.expectBytes (ByteArray.empty.push 1 |>.push 2 |>.push 3) "test")
        (ByteArray.empty.push 1) with
    | .error (.badMagic "test") => pure ()
    | .error e => fail s!"wrong error: {e}"
    | .ok _ => fail "short input accepted",
  test "asciiToken on all-whitespace input fails" do
    match ParseM.run ParseM.asciiToken "   \t\n".toUTF8 with
    | .error (.corrupt ..) => pure ()
    | .error e => fail s!"wrong error: {e}"
    | .ok t => fail s!"unexpectedly parsed token {t}",
  test "asciiNat fails with no digits" do
    match ParseM.run ParseM.asciiNat "  xyz".toUTF8 with
    | .error (.corrupt ..) => pure ()
    | .error e => fail s!"wrong error: {e}"
    | .ok n => fail s!"unexpectedly parsed {n}",
  test "skipAsciiWhitespace is idempotent at eof" do
    match ParseM.run (data := "   ".toUTF8) (do
      ParseM.skipAsciiWhitespace
      ParseM.skipAsciiWhitespace
      ParseM.isEof) with
    | .ok eof => assertTrue eof "eof after double skip"
    | .error e => fail s!"parse failed: {e}"
]

/-- The `binary` suite (WP2). -/
def suite : Tests.Suite :=
  { name := "binary"
    cases := bitStreamKnownValueTests ++ bitStreamRoundTripTests ++ alignByteTests ++
             truncationTests ++ parseEdgeTests }

end Tests.BinaryTests
