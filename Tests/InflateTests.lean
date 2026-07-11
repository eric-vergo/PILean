import Tests.Framework
import Tests.Prng

/-!
# inflate tests

INFLATE vs Python-zlib corpus, hostile vectors, truncation fuzz.
-/

namespace Tests.InflateTests

open PILean
open PILean.Compress

/-! ## A tiny, independent LSB-first bit packer

Used only to hand-construct hostile bit sequences field-by-field (BFINAL,
BTYPE, HLIT, ...) without doing the byte-boundary arithmetic by hand.
Deliberately a *separate* implementation from `PILean.Compress.BitWriter`
(same well-known packing convention — DEFLATE's own, RFC 1951 §3.1.1 — but
freshly written here), so a hostile vector never depends on the encoder
under test elsewhere in this work package. -/
structure BitPack where
  bytes : Array UInt8 := #[]
  cur : UInt32 := 0
  cnt : Nat := 0
  deriving Inhabited

/-- A fresh, empty bit packer. -/
def BitPack.empty : BitPack := {}

/-- Append the low `n` bits of `v`, LSB-first (bit 0 of `v` lands earliest
in the stream), flushing whole bytes as they fill. -/
def BitPack.bits (p : BitPack) (v n : Nat) : BitPack := Id.run do
  let mut cur := p.cur ||| ((UInt32.ofNat v) <<< (UInt32.ofNat p.cnt))
  let mut cnt := p.cnt + n
  let mut bytes := p.bytes
  while cnt ≥ 8 do
    bytes := bytes.push cur.toUInt8
    cur := cur >>> 8
    cnt := cnt - 8
  return { bytes, cur, cnt }

/-- Append a single bit (convenience for hand-writing a Huffman codeword's
bits one at a time, MSB-first per RFC 1951, matching `Huffman.decodeSym`'s
read order exactly — the caller supplies the codeword's bits in that
order). -/
def BitPack.bit (p : BitPack) (b : Nat) : BitPack := p.bits b 1

/-- Flush any partial trailing byte (zero-padded) and return the bytes. -/
def BitPack.finish (p : BitPack) : ByteArray := Id.run do
  let mut bytes := p.bytes
  if p.cnt > 0 then
    bytes := bytes.push p.cur.toUInt8
  return ByteArray.mk bytes

/-! ## Golden corpus: `testdata/golden/zlib/<class>.{bin,z0..z9,raw9}` -/

/-- Every data class in the zlib golden corpus (see
`testdata/golden/MANIFEST.md`). -/
def zlibClasses : List String :=
  ["b65535", "b65536", "empty", "one", "random100k", "random4k", "text", "zeros"]

/-- Directory holding the zlib corpus. -/
def zlibDir : System.FilePath := Tests.goldenDir / "zlib"

/-- For one data class: every `.z0`…`.z9` (via `Zlib.decompress`) and
`.raw9` (via `inflate`) must byte-exactly reproduce `.bin`. -/
def corpusTest (cls : String) : TestCase :=
  test s!"corpus class \"{cls}\": zlib levels 0–9 and raw9 all decode to .bin" do
    let expected ← IO.FS.readBinFile (zlibDir / s!"{cls}.bin")
    for lvl in [0:10] do
      let compressed ← IO.FS.readBinFile (zlibDir / s!"{cls}.z{lvl}")
      match Zlib.decompress compressed with
      | .ok got => assertBytesEq got expected s!"{cls}.z{lvl}"
      | .error e => fail s!"{cls}.z{lvl}: Zlib.decompress failed: {e}"
    let raw9 ← IO.FS.readBinFile (zlibDir / s!"{cls}.raw9")
    match inflate raw9 expected.size with
    | .ok got => assertBytesEq got expected s!"{cls}.raw9"
    | .error e => fail s!"{cls}.raw9: inflate failed: {e}"

def corpusTests : List TestCase := zlibClasses.map corpusTest

/-! ## Hostile vectors: hand-crafted malformed/hostile bit streams that
must all be rejected with `.error`, never accepted and never panic/hang. -/

/-- Stored block (`BFINAL=1,BTYPE=00`) whose `LEN`/`NLEN` fields are not
complements: `LEN=5`, `NLEN=0` (should be `0xFFFA`). -/
def badNlenVector : ByteArray :=
  (BitPack.empty.bit 1 |>.bits 0 2 -- BFINAL=1, BTYPE=00 (stored)
    |>.bits 0 5 -- pad remaining bits of the header byte to the boundary
    |>.bits 5 16 -- LEN = 5
    |>.bits 0 16 -- NLEN = 0 (wrong; should be ~5 & 0xFFFF = 0xFFFA)
  ).finish

/-- Dynamic block whose code-length-code (the 19-symbol alphabet used to
Huffman-code the litlen/dist length sequences) is over-subscribed: three
symbols (16, 17, 18 — the first three in transmission order) are all given
length 1, for a Kraft sum of `3 × 1/2 = 1.5 > 1`. -/
def oversubscribedVector : ByteArray :=
  let clLens : List Nat := [1, 1, 1] ++ List.replicate 16 0  -- 19 entries, transmission order
  let hdr := BitPack.empty.bit 1 |>.bits 2 2 -- BFINAL=1, BTYPE=10 (dynamic)
    |>.bits 0 5 -- HLIT = 0 → nLitLen = 257
    |>.bits 0 5 -- HDIST = 0 → nDist = 1
    |>.bits 15 4 -- HCLEN = 15 → nCLen = 19 (transmit all)
  (clLens.foldl (fun p l => p.bits l 3) hdr).finish

/-- Dynamic block whose code-length-code assigns *only* symbol 16 (the
"repeat previous length" code) a codeword, and whose very first code-length
symbol is that codeword — i.e. `repeat-16` appears before any real code
length has been transmitted, which is undefined (there is no "previous
length" to repeat). -/
def repeat16FirstVector : ByteArray :=
  let clLens : List Nat := [1] ++ List.replicate 18 0  -- only symbol 16 (position 0) used
  let hdr := BitPack.empty.bit 1 |>.bits 2 2 -- BFINAL=1, BTYPE=10 (dynamic)
    |>.bits 0 5 -- HLIT = 0 → nLitLen = 257
    |>.bits 0 5 -- HDIST = 0 → nDist = 1
    |>.bits 15 4 -- HCLEN = 15 → nCLen = 19
  ((clLens.foldl (fun p l => p.bits l 3) hdr).bit 0 -- the (only) codeword for code-length symbol 16
  ).finish

/-- Fixed-Huffman block whose first (and only) token is a length/distance
back-reference to distance 1, decoded with nothing yet in the output
buffer — "distance too far back". Length code 257 (base length 3, 0 extra
bits) is `0000001` MSB-first (RFC 1951's fixed table); distance code 0
(base distance 1, 0 extra bits) is `00000`. -/
def distTooFarVector : ByteArray :=
  (BitPack.empty.bit 1 |>.bit 1 |>.bit 0 -- BFINAL=1, BTYPE=01 (fixed)
    |>.bit 0 |>.bit 0 |>.bit 0 |>.bit 0 |>.bit 0 |>.bit 0 |>.bit 1 -- litlen 257, 7 bits MSB-first
    |>.bit 0 |>.bit 0 |>.bit 0 |>.bit 0 |>.bit 0 -- dist 0, 5 bits MSB-first
  ).finish

/-- Fixed-Huffman block whose first token is literal/length symbol 286 —
one of the two symbols (286, 287) that have a valid fixed codeword but are
never legal for a compressor to emit. Code 286 is `11000110` MSB-first. -/
def litlen286Vector : ByteArray :=
  (BitPack.empty.bit 1 |>.bit 1 |>.bit 0 -- BFINAL=1, BTYPE=01 (fixed)
    |>.bit 1 |>.bit 1 |>.bit 0 |>.bit 0 |>.bit 0 |>.bit 1 |>.bit 1 |>.bit 0 -- litlen 286, 8 bits MSB-first
  ).finish

/-- Fixed-Huffman block whose first token is a valid length code (257)
followed by a 5-bit distance field of all 1s — the bit pattern a complete
32-entry distance alphabet would assign to reserved symbol 31. Since the
fixed distance table here only has 30 entries (symbols 0–29), no codeword
matches. -/
def dist31Vector : ByteArray :=
  (BitPack.empty.bit 1 |>.bit 1 |>.bit 0 -- BFINAL=1, BTYPE=01 (fixed)
    |>.bit 0 |>.bit 0 |>.bit 0 |>.bit 0 |>.bit 0 |>.bit 0 |>.bit 1 -- litlen 257, 7 bits MSB-first
    |>.bit 1 |>.bit 1 |>.bit 1 |>.bit 1 |>.bit 1 -- 5 bits, all 1
  ).finish

/-- Assert `inflate` rejects `v` with `.error` (never `.ok`, and by
returning at all, never hangs). -/
def assertInflateRejects (v : ByteArray) (label : String) : IO Unit := do
  match inflate v with
  | .error _ => pure ()
  | .ok _ => fail s!"{label}: inflate unexpectedly accepted a hostile vector"

def hostileVectorTests : List TestCase := [
  test "stored block: LEN/NLEN complement mismatch is rejected" do
    assertInflateRejects badNlenVector "bad NLEN",
  test "dynamic block: over-subscribed code-length code is rejected" do
    assertInflateRejects oversubscribedVector "oversubscribed",
  test "dynamic block: repeat-16 before any code length is rejected" do
    assertInflateRejects repeat16FirstVector "repeat-16-first",
  test "fixed block: back-reference distance exceeding output size is rejected" do
    assertInflateRejects distTooFarVector "dist-too-far",
  test "fixed block: literal/length symbol 286 is rejected" do
    assertInflateRejects litlen286Vector "litlen 286",
  test "fixed block: distance symbol 31 (no matching codeword) is rejected" do
    assertInflateRejects dist31Vector "dist 31",
  test "empty input is rejected (cannot even read BFINAL/BTYPE)" do
    assertInflateRejects ByteArray.empty "empty",
  test "single-byte stored-block header with no LEN/NLEN is rejected" do
    assertInflateRejects (ByteArray.mk #[0x01]) "truncated stored header",
  test "dynamic block header truncated mid-HCLEN-table is rejected" do
    let v := (BitPack.empty.bit 1 |>.bits 2 2 |>.bits 5 5 |>.bits 5 5 |>.bits 10 4 |>.bits 3 3).finish
    assertInflateRejects v "truncated dynamic header"
]

/-! ## Truncation fuzz

Every strict prefix (at a stride of 7 bytes) of a real compressed file
must be rejected — never accepted, never panic, never hang. -/

def truncationFuzzTests : List TestCase := [
  test "every 7-byte-stride prefix of random4k.z6 is rejected" do
    let full ← IO.FS.readBinFile (zlibDir / "random4k.z6")
    let n := full.size
    let mut i := 0
    while i < n do
      match Zlib.decompress (full.extract 0 i) with
      | .ok _ => fail s!"prefix of length {i}/{n} unexpectedly decoded successfully"
      | .error _ => pure ()
      i := i + 7
]

/-- The `inflate` suite. -/
def suite : Tests.Suite :=
  { name := "inflate", cases := corpusTests ++ hostileVectorTests ++ truncationFuzzTests }

end Tests.InflateTests
