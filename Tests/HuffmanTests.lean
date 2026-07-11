import Tests.Framework
import Tests.Prng

/-!
# huffman tests

Canonical Huffman codes, decoder, package-merge, LZ77 round trip. Owned by WP3 — that work package fills in `cases`.
-/

namespace Tests.HuffmanTests

open PILean
open PILean.Compress
open PILean.Compress.Huffman

/-! ## canonicalCodes -/

/-- RFC 1951 §3.2.2's own worked example: alphabet with lengths
`(3,3,3,3,3,2,4,4)` canonicalizes to `(010,011,100,101,110,00,1110,1111)`. -/
def canonicalCodesTests : List TestCase := [
  test "RFC 1951 worked example" do
    let lens : Array UInt8 := #[3, 3, 3, 3, 3, 2, 4, 4]
    match canonicalCodes lens with
    | .ok codes =>
      assertEq codes #[0b010, 0b011, 0b100, 0b101, 0b110, 0b00, 0b1110, 0b1111] "codes"
    | .error e => fail s!"unexpected error: {e}",
  test "fixed literal/length table (RFC 1951 §3.2.6)" do
    -- 0–143 ↦ 8 bits, 144–255 ↦ 9 bits, 256–279 ↦ 7 bits, 280–287 ↦ 8 bits.
    let lens : Array UInt8 := (Array.range 288).map fun i =>
      if i ≤ 143 then 8 else if i ≤ 255 then 9 else if i ≤ 279 then 7 else 8
    match canonicalCodes lens with
    | .ok codes =>
      -- Known boundary codes from the RFC's own table.
      assertEq codes[0]! 0b00110000 "sym 0"
      assertEq codes[143]! 0b10111111 "sym 143"
      assertEq codes[144]! 0b110010000 "sym 144"
      assertEq codes[255]! 0b111111111 "sym 255"
      assertEq codes[256]! 0b0000000 "sym 256"
      assertEq codes[279]! 0b0010111 "sym 279"
      assertEq codes[280]! 0b11000000 "sym 280"
      assertEq codes[287]! 0b11000111 "sym 287"
    | .error e => fail s!"unexpected error: {e}",
  test "over-subscribed lengths are rejected" do
    -- Three symbols of length 1: Kraft sum = 3 × 1/2 = 1.5 > 1.
    match canonicalCodes #[1, 1, 1] with
    | .error (.corrupt ..) => pure ()
    | .error e => fail s!"wrong error: {e}"
    | .ok _ => fail "over-subscribed lengths accepted",
  test "over-subscribed lengths are rejected (mixed lengths)" do
    -- Kraft sum = 1/2 + 3 × 1/4 = 1.25 > 1.
    match canonicalCodes #[1, 2, 2, 2] with
    | .error (.corrupt ..) => pure ()
    | .error e => fail s!"wrong error: {e}"
    | .ok _ => fail "over-subscribed lengths accepted",
  test "code length beyond 15 is rejected" do
    match canonicalCodes #[16] with
    | .error _ => pure ()
    | .ok _ => fail "length 16 accepted",
  test "complete set (Kraft = 1) is accepted" do
    -- 1/2 + 1/4 + 1/4 = 1, exactly complete.
    match canonicalCodes #[1, 2, 2] with
    | .ok codes => assertEq codes #[0b0, 0b10, 0b11] "codes"
    | .error e => fail s!"unexpected error: {e}",
  test "incomplete sets are legal" do
    -- A single length-1 symbol leaves half the code space unused.
    match canonicalCodes #[1] with
    | .ok codes => assertEq codes #[0] "codes"
    | .error e => fail s!"incomplete set rejected: {e}",
  test "empty length array" do
    match canonicalCodes #[] with
    | .ok codes => assertEq codes.size 0 "no codes"
    | .error e => fail s!"unexpected error: {e}"
]

/-! ## buildDecoder -/

def buildDecoderTests : List TestCase := [
  test "RFC worked example: counts and symbols tables" do
    let lens : Array UInt8 := #[3, 3, 3, 3, 3, 2, 4, 4]
    match buildDecoder lens with
    | .ok d =>
      assertEq d.counts.size 16 "counts sized 0..15"
      assertEq d.counts[1]! 0 "no length-1 codes"
      assertEq d.counts[2]! 1 "one length-2 code"
      assertEq d.counts[3]! 5 "five length-3 codes"
      assertEq d.counts[4]! 2 "two length-4 codes"
      -- Symbols ordered by (length, symbol): length 2 → {5}; length 3 →
      -- {0,1,2,3,4}; length 4 → {6,7}.
      assertEq d.symbols #[5, 0, 1, 2, 3, 4, 6, 7] "symbols"
    | .error e => fail s!"unexpected error: {e}",
  test "over-subscribed lengths are rejected" do
    match buildDecoder #[1, 1, 1] with
    | .error (.corrupt ..) => pure ()
    | .error e => fail s!"wrong error: {e}"
    | .ok _ => fail "over-subscribed lengths accepted",
  test "incomplete sets are legal" do
    match buildDecoder #[2] with
    | .ok d =>
      assertEq d.symbols #[0] "single symbol"
      assertEq d.counts[2]! 1 "one length-2 code"
    | .error e => fail s!"incomplete set rejected: {e}",
  test "all-unused alphabet builds an empty decoder" do
    match buildDecoder #[0, 0, 0] with
    | .ok d => assertEq d.symbols.size 0 "no symbols"
    | .error e => fail s!"unexpected error: {e}"
]

/-! ## Decoder.decodeSym

`decodeSym` consumes bits via `BitReader.readBits`, which is still a WP2
stub in this worktree (`readBits`/`alignByte`/`readBytes` all raise
"not implemented yet"), so it cannot be exercised end-to-end here. Its
count/offset walk is exactly the algorithm cross-checked below via
`decodeBits` (a `List Bool`-driven copy of the same arithmetic, bypassing
`BitReader` entirely) — that gives strong indirect evidence `decodeSym`
itself is correct once WP2 lands. Direct, end-to-end coverage of
`decodeSym` comes from INFLATE's corpus tests in Wave 2. -/

/-- Mirrors `Decoder.decodeSym`'s count/offset walk, but consumes bits from
a plain `List Bool` (MSB first) instead of a `BitReader`, so it can
validate `buildDecoder`'s tables without a live bit stream. Test-only. -/
def decodeBits (d : Decoder) (bits : List Bool) : Option UInt16 := Id.run do
  let mut code := 0
  let mut first := 0
  let mut index := 0
  let mut rest := bits
  for len in [1:16] do
    match rest with
    | [] => return none
    | b :: rest' =>
      rest := rest'
      code := code * 2 + (if b then 1 else 0)
      let count := if len < d.counts.size then (d.counts[len]!).toNat else 0
      if code < first + count then
        let symIdx := index + (code - first)
        return if symIdx < d.symbols.size then some d.symbols[symIdx]! else none
      index := index + count
      first := (first + count) * 2
  return none

/-- The MSB-first bits of `code` (a `len`-bit value). -/
def codeBits (code len : Nat) : List Bool :=
  (List.range len).map fun b => ((code >>> (len - 1 - b)) &&& 1) == 1

/-- For every used symbol in `lens`, decoding its own canonical codeword
(via `decodeBits`) must return that symbol. -/
def checkSelfConsistent (lens : Array UInt8) : IO Unit := do
  match buildDecoder lens, canonicalCodes lens with
  | .ok d, .ok codes =>
    for sym in [0:lens.size] do
      let len := (lens[sym]!).toNat
      if len > 0 then
        let bits := codeBits (codes[sym]!).toNat len
        assertEq (decodeBits d bits) (some (UInt16.ofNat sym)) s!"decode of sym {sym}'s own code"
  | .error e, _ => fail s!"buildDecoder failed: {e}"
  | _, .error e => fail s!"canonicalCodes failed: {e}"

def decodeSymTests : List TestCase := [
  test "RFC worked example self-decodes" do
    checkSelfConsistent #[3, 3, 3, 3, 3, 2, 4, 4],
  test "fixed literal/length table self-decodes" do
    let lens : Array UInt8 := (Array.range 288).map fun i =>
      if i ≤ 143 then 8 else if i ≤ 255 then 9 else if i ≤ 279 then 7 else 8
    checkSelfConsistent lens,
  test "package-merge outputs self-decode (randomized)" do
    let mut g := Tests.SplitMix64.ofSeed 20260711
    for _ in [0:8] do
      let (raw, g') := g.bytes 40
      g := g'
      let freqs : Array Nat := (Array.range 40).map fun i => (raw[i]!).toNat % 30
      let lens := lengthLimitedLengths freqs 15
      checkSelfConsistent lens
]

/-! ## lengthLimitedLengths (package-merge) -/

/-- Exact Kraft numerator `Σ 2 ^ (maxLen - len)` over used symbols, as a
`Nat` (avoids floating-point comparison). Should be `≤ 2 ^ maxLen`. -/
def kraftNumerator (lens : Array UInt8) (maxLen : Nat) : Nat := Id.run do
  let mut total := 0
  for l in lens do
    if l.toNat > 0 then
      total := total + 2 ^ (maxLen - l.toNat)
  return total

/-- Total weighted code length `Σ freq[i] * len[i]`. -/
def weightedBits (freqs : Array Nat) (lens : Array UInt8) : Nat := Id.run do
  let mut total := 0
  for i in [0:freqs.size] do
    total := total + freqs[i]! * (lens[i]!).toNat
  return total

/-- Optimal (unrestricted-length) Huffman cost via the classic
"sum of merge weights" identity: repeatedly combine the two smallest
weights; the total of all merge results equals the minimal weighted path
length. Proven-optimal reference used to check `lengthLimitedLengths`
against, independent of package-merge's own logic. -/
def huffmanOptimalBits (weights : List Nat) : Nat :=
  match weights with
  | [] => 0
  | [_] => 0
  | _ => Id.run do
    let mut ws := weights.toArray.qsort (· < ·)
    let mut total := 0
    while ws.size > 1 do
      let a := ws[0]!
      let b := ws[1]!
      let merged := a + b
      total := total + merged
      ws := (ws.extract 2 ws.size).push merged |>.qsort (· < ·)
    return total

def packageMergeTests : List TestCase := [
  test "zero-frequency symbols get length 0" do
    let lens := lengthLimitedLengths #[0, 5, 0, 3, 0] 15
    assertEq lens[0]! 0 "sym0"
    assertEq lens[2]! 0 "sym2"
    assertEq lens[4]! 0 "sym4"
    assertTrue (lens[1]! > 0) "sym1 used"
    assertTrue (lens[3]! > 0) "sym3 used",
  test "single used symbol gets length 1" do
    let lens := lengthLimitedLengths #[0, 0, 7, 0] 15
    assertEq lens #[0, 0, 1, 0] "lengths",
  test "no used symbols returns all zero" do
    let lens := lengthLimitedLengths #[0, 0, 0] 15
    assertEq lens #[0, 0, 0] "lengths",
  test "Kraft inequality holds (≤ 1) on a mixed frequency set" do
    let freqs : Array Nat := #[0, 5, 0, 1, 1, 1, 1, 1]
    let maxLen := 15
    let lens := lengthLimitedLengths freqs maxLen
    assertTrue (kraftNumerator lens maxLen ≤ 2 ^ maxLen) "Kraft ≤ 1",
  test "max length bound is respected on a skewed distribution" do
    let freqs : Array Nat := #[1, 1, 2, 3, 5, 8, 13, 21, 34, 55]
    let maxLen := 4
    let lens := lengthLimitedLengths freqs maxLen
    for l in lens do
      assertTrue (l.toNat ≤ maxLen) s!"length {l} ≤ {maxLen}"
    assertTrue (kraftNumerator lens maxLen ≤ 2 ^ maxLen) "Kraft ≤ 1",
  test "matches unbounded Huffman cost on small random frequency sets" do
    let mut g := Tests.SplitMix64.ofSeed 3
    for trial in [0:12] do
      let n := 2 + trial % 7  -- 2..8 symbols
      let (raw, g') := g.bytes n
      g := g'
      let freqs : Array Nat := (Array.range n).map fun i => (raw[i]!).toNat % 40 + 1
      -- maxLen generous enough that the length limit never binds for n ≤ 8.
      let lens := lengthLimitedLengths freqs 15
      let got := weightedBits freqs lens
      let want := huffmanOptimalBits freqs.toList
      assertEq got want s!"trial {trial} (n={n}, freqs={freqs.toList})"
      assertTrue (kraftNumerator lens 15 ≤ 2 ^ 15) s!"trial {trial}: Kraft ≤ 1"
]

/-! ## LZ77 tokenize / detokenize -/

/-- Every match token must reference bytes already produced (distance
within the current output-so-far) and stay within the frozen format's
length/distance ranges. -/
def assertValidTokens (tokens : Array UInt32) (label : String) : IO Unit := do
  let mut outSize := 0
  for t in tokens do
    if t &&& 0x80000000 != 0 then
      let len := ((t >>> 16) &&& 0x7FFF).toNat
      let dist := (t &&& 0xFFFF).toNat
      assertTrue (len ≥ 3 && len ≤ 258) s!"{label}: match length {len} in [3,258]"
      assertTrue (dist ≥ 1 && dist ≤ 32768) s!"{label}: match distance {dist} in [1,32768]"
      assertTrue (dist ≤ outSize) s!"{label}: match distance {dist} ≤ output-so-far {outSize}"
      outSize := outSize + len
    else
      outSize := outSize + 1

/-- Tokenize `data`, check every match is valid, detokenize, and assert the
round trip reproduces `data` exactly. -/
def roundTrip (label : String) (data : ByteArray) (level : Nat := 6) : IO Unit := do
  let tokens := LZ77.tokenize data level
  assertValidTokens tokens label
  let back := LZ77.detokenize tokens
  assertBytesEq back data label

def lz77Tests : List TestCase := [
  test "empty input" do
    roundTrip "empty" ByteArray.empty,
  test "single byte" do
    roundTrip "1 byte" (ByteArray.mk #[0x42]),
  test "10 KB of zeros produces long matches" do
    let data : ByteArray := Id.run do
      let mut b := ByteArray.emptyWithCapacity 10000
      for _ in [0:10000] do
        b := b.push 0
      return b
    let tokens := LZ77.tokenize data
    assertValidTokens tokens "zeros"
    assertBytesEq (LZ77.detokenize tokens) data "zeros round trip"
    -- 10000 zero bytes with a 258-byte max match length needs at least
    -- ⌈9997 / 258⌉ ≈ 39 tokens; a working matcher should stay well under
    -- one token per byte.
    assertTrue (tokens.size < 100) s!"long matches expected, got {tokens.size} tokens",
  test "\"abc\" repeated" do
    let data : ByteArray := Id.run do
      let mut b := ByteArray.emptyWithCapacity 300
      for _ in [0:100] do
        b := (b.push 97).push 98 |>.push 99
      return b
    roundTrip "abc repeated" data,
  test "random 10 KB is mostly literals" do
    let (data, _) := (Tests.SplitMix64.ofSeed 12345).bytes 10000
    let tokens := LZ77.tokenize data
    assertValidTokens tokens "random"
    assertBytesEq (LZ77.detokenize tokens) data "random round trip"
    let literals := tokens.foldl (fun acc t => if t &&& 0x80000000 == 0 then acc + 1 else acc) 0
    assertTrue (literals * 10 ≥ tokens.size * 6)
      s!"expected mostly literals, got {literals}/{tokens.size}",
  test "probe levels 1, 6, 9 all round-trip and stay valid" do
    let (data, _) := (Tests.SplitMix64.ofSeed 99).bytes 4000
    for level in [1, 6, 9] do
      roundTrip s!"level {level}" data level
]

/-- The `huffman` suite (WP3). -/
def suite : Tests.Suite :=
  { name := "huffman"
    cases := canonicalCodesTests ++ buildDecoderTests ++ decodeSymTests ++
             packageMergeTests ++ lz77Tests }

end Tests.HuffmanTests
