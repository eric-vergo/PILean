import Tests.Framework
import Tests.Prng

/-!
# lzw tests

LZW quirk vectors: KwKwK, deferred clear, width growth, earlyChange. Owned
by WP14.

The width-bump timing implemented by `PILean.Compress.Lzw` was reverse
engineered against Pillow 11.3.0's real GIF encoder/decoder (see that
module's docstring) rather than derived from folklore, so several tests
here hand-craft raw code streams (via `Compress.BitWriter` directly) that
independently mirror the *decoder's* own bookkeeping, to pin the exact
bump/KwKwK/deferred-clear semantics rather than only checking that
`compress` and `decompress` happen to agree with each other.
-/

namespace Tests.LzwTests

open PILean
open PILean.Compress

/-- Reduce every byte of `data` into `[0, 2^mcs)` so it's a legal LZW index
stream for `minCodeSize = mcs` (a no-op for `mcs ≥ 8`, since every byte is
already `< 256`). -/
private def clipToRange (mcs : Nat) (data : ByteArray) : ByteArray :=
  if mcs ≥ 8 then data
  else Id.run do
    let modulus : UInt8 := UInt8.ofNat (1 <<< mcs)
    let mut d := data
    for i in [0:d.size] do
      d := d.set! i (d.get! i % modulus)
    return d

/-- Compress `n` deterministic pseudo-random bytes (seeded by `seed`,
reduced to `minCodeSize = mcs`'s range) and assert `decompress` recovers
them exactly. -/
private def roundTripCase (mcs n seed : Nat) : IO Unit := do
  let (raw, _) := (SplitMix64.ofSeed seed).bytes n
  let data := clipToRange mcs raw
  let enc := Lzw.compress mcs data
  match Lzw.decompress mcs enc (n + 16) with
  | .error e => fail s!"mcs={mcs} n={n}: decompress failed: {e}"
  | .ok dec => assertBytesEq dec data s!"mcs={mcs} n={n} round trip"

/-! ## Round trip across every `minCodeSize` and several sizes -/

/-- `mcs=8, n=10000` alone is known (from prototyping, see the module
docstring on `Lzw`) to grow the dictionary past 4096 and trigger at least
one clear-and-reset, so this list already covers the reset path — no
separate "force a reset" scenario is needed beyond that. -/
def roundTripTests : List TestCase :=
  (List.range 7).flatMap fun k =>
    let mcs := k + 2
    [0, 1, 4095, 10000].map fun n =>
      test s!"round trip mcs={mcs} n={n}" (roundTripCase mcs n (9000 + mcs * 1009 + n))

/-! ## All-same-value runs (degenerate repetitive input) -/

def allSameValueTests : List TestCase := [
  test "all-same-value run round trips (mcs=2, n=3000)" do
    let data := ByteArray.replicateByte 3000 1
    match Lzw.decompress 2 (Lzw.compress 2 data) 3100 with
    | .error e => fail s!"decompress failed: {e}"
    | .ok dec => assertBytesEq dec data "all-same round trip",
  test "all-same-value run round trips (mcs=8, n=6000)" do
    let data := ByteArray.replicateByte 6000 200
    match Lzw.decompress 8 (Lzw.compress 8 data) 6100 with
    | .error e => fail s!"decompress failed: {e}"
    | .ok dec => assertBytesEq dec data "all-same round trip (mcs=8)"
]

/-! ## KwKwK (`code == nextCode`) -/

/-- Bytes for a repeating `"aababaababaabababaababaababaabab"` family
string, `'a' ↦ 0`, `'b' ↦ 1` — this exact overlapping-repeat shape is the
textbook LZW pattern that forces the decoder to resolve a code equal to
its own not-yet-created dictionary slot. -/
private def kwkwkData : ByteArray := Id.run do
  let unit := "aababaababaabababaababaababaabab"
  let s := String.join (List.replicate 40 unit)
  let mut d := ByteArray.emptyWithCapacity s.length
  for ch in s.toList do
    d := d.push (if ch == 'a' then 0 else 1)
  return d

def kwkwkTests : List TestCase := [
  test "KwKwK-inducing pattern round trips (mcs=2)" do
    match Lzw.decompress 2 (Lzw.compress 2 kwkwkData) (kwkwkData.size + 16) with
    | .error e => fail s!"decompress failed: {e}"
    | .ok dec => assertBytesEq dec kwkwkData "kwkwk round trip",
  test "KwKwK-inducing pattern round trips (mcs=3)" do
    match Lzw.decompress 3 (Lzw.compress 3 kwkwkData) (kwkwkData.size + 16) with
    | .error e => fail s!"decompress failed: {e}"
    | .ok dec => assertBytesEq dec kwkwkData "kwkwk round trip (mcs=3)"
]

/-! ## Deferred clear: dictionary fills to 4096 with no `Clear` in sight -/

/-- Hand-pack (via `BitWriter` directly, mirroring `decompress`'s own
`nextCode`/width bookkeeping) a `minCodeSize = 2` code stream that: emits
one literal, then 4090 alternating-literal codes — each of which, on the
decode side, still creates exactly one new dictionary entry (since `prev`
always exists), driving `nextCode` from 6 all the way to exactly 4096
*without ever emitting a `Clear` code* — then two more codes referencing
already-existing (now frozen-dictionary) entries, then EOI. Alternating
between two literals (rather than always referencing the freshly-created
entry, i.e. avoiding a KwKwK chain here) keeps each entry exactly 2 bytes
long, so decoding this stream is cheap despite filling the whole
4096-entry table. -/
private def deferredClearStream : ByteArray := Id.run do
  let minCodeSize := 2
  let clearCode := 1 <<< minCodeSize
  let mut width := minCodeSize + 1
  let mut w : BitWriter := {}
  w := w.writeBits 0 width
  let mut nextCode := clearCode + 2
  for i in [0:4090] do
    let v : UInt32 := if i % 2 == 0 then 1 else 0
    w := w.writeBits v width
    nextCode := nextCode + 1
    if nextCode ≥ (1 <<< width) && width < 12 then
      width := width + 1
  -- Dictionary is now exactly full (`nextCode = 4096`); width is frozen at
  -- 12 bits. These two references to pre-existing entries, plus EOI, must
  -- still decode cleanly.
  w := w.writeBits 6 width
  w := w.writeBits 4095 width
  w := w.writeBits (UInt32.ofNat (clearCode + 1)) width
  return w.toByteArray

def deferredClearTests : List TestCase := [
  test "dictionary fills to 4096 with no Clear code: freezes at 12 bits, keeps decoding" do
    match Lzw.decompress 2 deferredClearStream 10000 with
    | .error e => fail s!"expected deferred-clear decode to succeed, got: {e}"
    | .ok dec =>
      -- 1 initial literal + 4090 alternating literals + 2 tail references
      -- to existing (now frozen-dictionary) 2-byte entries.
      assertEq dec.size (1 + 4090 + 2 * 2) "decoded length"
      assertEq (dec.get! 0) (0 : UInt8) "first byte (initial literal)"
      for i in [0:4090] do
        let expected : UInt8 := if i % 2 == 0 then 1 else 0
        assertEq (dec.get! (1 + i)) expected s!"alternating literal at position {i}"
]

/-! ## Rejection: malformed streams never panic, always `.error` -/

def rejectionTests : List TestCase := [
  test "the first code (an implicit clear, at the very start of decode) must be a literal" do
    let minCodeSize := 2
    let badCode := (1 <<< minCodeSize) + 2  -- the first dynamic code, not a literal
    let stream : ByteArray :=
      (BitWriter.writeBits {} (UInt32.ofNat badCode) (minCodeSize + 1)).toByteArray
    match Lzw.decompress minCodeSize stream 100 with
    | .error (.corrupt _ _) => pure ()
    | .error e => fail s!"wrong error variant: {e}"
    | .ok _ => fail "expected a non-literal first code to be rejected",
  test "a code referencing far beyond the dictionary is rejected" do
    let minCodeSize := 2
    let stream : ByteArray := Id.run do
      let mut w : BitWriter := {}
      w := w.writeBits 0 (minCodeSize + 1)  -- valid literal first
      w := w.writeBits 4000 12  -- wildly out of range for a freshly-cleared table
      return w.toByteArray
    match Lzw.decompress minCodeSize stream 100 with
    | .error (.corrupt _ _) => pure ()
    | .error e => fail s!"wrong error variant: {e}"
    | .ok _ => fail "expected an out-of-range code to be rejected",
  test "minCodeSize below 2 is rejected" do
    match Lzw.decompress 1 ByteArray.empty 100 with
    | .error _ => pure ()
    | .ok _ => fail "expected minCodeSize=1 to be rejected",
  test "minCodeSize above 8 is rejected" do
    match Lzw.decompress 9 ByteArray.empty 100 with
    | .error _ => pure ()
    | .ok _ => fail "expected minCodeSize=9 to be rejected"
]

/-! ## `maxOutput` decompression-bomb guard -/

def maxOutputTests : List TestCase := [
  test "maxOutput rejects a decompression that would exceed it" do
    let data := ByteArray.replicateByte 500 7
    match Lzw.decompress 4 (Lzw.compress 4 data) 10 with
    | .error _ => pure ()
    | .ok _ => fail "expected maxOutput=10 to reject a ~500-byte decompression"
]

/-! ## Truncation fuzz: never panic/hang; exact match at full length -/

def fuzzTests : List TestCase := [
  test "every prefix of a compressed stream either errors or returns without panicking" do
    let (raw, _) := (SplitMix64.ofSeed 424242).bytes 500
    let data := clipToRange 4 raw
    let enc := Lzw.compress 4 data
    for n in [0:enc.size] do
      match Lzw.decompress 4 (enc.extract 0 n) (data.size + 16) with
      | .ok _ => pure ()
      | .error _ => pure ()
    match Lzw.decompress 4 enc (data.size + 16) with
    | .ok dec => assertBytesEq dec data "full length exact match"
    | .error e => fail s!"full length decode failed: {e}"
]

/-! ## `earlyChange` (TIFF one-code-early width bump) -/

/-- Hand-pack a tiny `minCodeSize = 2` stream whose width-bump timing is
computed under `earlyChange`'s own threshold (`(1 <<< width) - 1` instead
of `(1 <<< width)`), long enough to cross the first bump boundary
(`nextCode` 6 → 9). Used to show the two conventions genuinely diverge by
exactly one code, not just "sometimes decode differently". -/
private def tinyBumpStream (earlyChange : Bool) : ByteArray := Id.run do
  let minCodeSize := 2
  let clearCode := 1 <<< minCodeSize
  let mut width := minCodeSize + 1
  let mut w : BitWriter := {}
  w := w.writeBits 0 width
  let mut nextCode := clearCode + 2
  for i in [0:6] do
    let v : UInt32 := if i % 2 == 0 then 1 else 0
    w := w.writeBits v width
    nextCode := nextCode + 1
    let bumpAt := if earlyChange then (1 <<< width) - 1 else (1 <<< width)
    if nextCode ≥ bumpAt && width < 12 then
      width := width + 1
  w := w.writeBits (UInt32.ofNat (clearCode + 1)) width
  return w.toByteArray

def earlyChangeTests : List TestCase := [
  test "earlyChange round trips symmetrically (mcs=4, n=3000)" do
    let (raw, _) := (SplitMix64.ofSeed 8181).bytes 3000
    let data := clipToRange 4 raw
    let enc := Lzw.compressWith 4 data true
    match Lzw.decompress 4 enc (data.size + 16) true with
    | .error e => fail s!"earlyChange decode failed: {e}"
    | .ok dec => assertBytesEq dec data "earlyChange round trip",
  test "earlyChange=true-encoded bytes do not silently decode correctly with earlyChange=false" do
    let (raw, _) := (SplitMix64.ofSeed 8182).bytes 3000
    let data := clipToRange 4 raw
    let enc := Lzw.compressWith 4 data true
    match Lzw.decompress 4 enc (data.size + 16) false with
    | .error _ => pure ()
    | .ok dec =>
      assertTrue (dec != data)
        "earlyChange=false decoded earlyChange=true-encoded bytes to the SAME data (flag had no effect)",
  test "hand-built vector: the width bump lands one code earlier with earlyChange := true" do
    let earlyStream := tinyBumpStream true
    match Lzw.decompress 2 earlyStream 100 true, Lzw.decompress 2 earlyStream 100 false with
    | .ok correct, .ok mismatched =>
      assertTrue (correct != mismatched)
        "earlyChange must change the decoded bytes for this hand-built vector"
    | .ok _, .error _ => pure ()
    | .error e, _ => fail s!"expected the correctly-matched (earlyChange=true) decode to succeed: {e}"
]

/-- The `lzw` suite (WP14). -/
def suite : Tests.Suite :=
  { name := "lzw"
    cases := roundTripTests ++ allSameValueTests ++ kwkwkTests ++ deferredClearTests ++
      rejectionTests ++ maxOutputTests ++ fuzzTests ++ earlyChangeTests }

end Tests.LzwTests
