import PILean.Compress.BitStream

/-!
# Canonical Huffman coding

Shared by DEFLATE (encode + decode). Codes are canonical per RFC 1951
§3.2.2: shorter codes first, ties broken by symbol order.

Implementation notes for WP3: the v1 decoder is the puff.c-style
count/offset arithmetic decode implemented from the RFC text (simple,
obviously correct); a table-driven fast path can replace it behind the same
interface later. `buildDecoder` must reject over-subscribed code sets
(Kraft sum > 1). The encoder length-limiter uses package-merge, which
guarantees valid ≤ maxLen codes with no overflow fixup.
-/

namespace PILean.Compress.Huffman

/-- Maximum code length this module supports (RFC 1951's own limit: code
lengths are encoded in 4 bits and DEFLATE never uses more than 15). -/
private def maxBits : Nat := 15

/-- Count codes per length (index `0..maxBits`) and reject over-subscribed
length sets via the standard `left` bookkeeping (RFC 1951 §3.2.2 / puff.c
`construct`): starting from a code space of size 1, each length `L`
doubles the remaining space and consumes `count[L]` of it; going negative
means more codes were requested than the space allows. Incomplete sets
(`left > 0` at the end) are left for the caller to allow or reject. -/
private def countLengths (lengths : Array UInt8) : Except DecodeError (Array Nat) := do
  let mut counts : Array Nat := Array.replicate (maxBits + 1) 0
  for len in lengths do
    let l := len.toNat
    if l > maxBits then
      throw (.corrupt 0 s!"huffman code length {l} exceeds max {maxBits}")
    if l > 0 then
      counts := counts.set! l (counts[l]! + 1)
  let mut left : Int := 1
  for bits in [1:maxBits + 1] do
    left := left * 2 - (counts[bits]! : Int)
    if left < 0 then
      throw (.corrupt 0 "over-subscribed huffman code lengths")
  return counts

/-- Canonical code values for the given code lengths (RFC 1951 §3.2.2).
`lengths[sym] = 0` means the symbol is unused. Fails on over-subscribed
lengths. -/
def canonicalCodes (lengths : Array UInt8) : Except DecodeError (Array UInt16) := do
  let counts ← countLengths lengths
  -- `next_code[bits]` = smallest code value used at that length (RFC's
  -- `bl_count`/`next_code` algorithm).
  let mut code := 0
  let mut nextCode : Array Nat := Array.replicate (maxBits + 1) 0
  for bits in [1:maxBits + 1] do
    code := (code + counts[bits - 1]!) * 2
    nextCode := nextCode.set! bits code
  let mut codes : Array UInt16 := Array.replicate lengths.size 0
  for n in [0:lengths.size] do
    let len := (lengths[n]!).toNat
    if len > 0 then
      codes := codes.set! n (UInt16.ofNat nextCode[len]!)
      nextCode := nextCode.set! len (nextCode[len]! + 1)
  return codes

/-- A prepared Huffman decoder. Internals are owned by WP3 and may change;
only `buildDecoder`/`decodeSym` are frozen. `counts[len]` is the number of
codes of length `len` (`0..maxBits`); `symbols` lists the decoded symbols
ordered first by code length, then by symbol value (puff.c-style). -/
structure Decoder where
  counts : Array UInt16 := #[]
  symbols : Array UInt16 := #[]
  deriving Inhabited

/-- Build a decoder from code lengths. Rejects over-subscribed code sets;
incomplete sets are allowed (needed by DEFLATE's single-distance-code
edge case). -/
def buildDecoder (lengths : Array UInt8) : Except DecodeError Decoder := do
  let counts ← countLengths lengths
  -- `offs[len]` = index in `symbols` where length-`len` codes begin.
  let mut offs : Array Nat := Array.replicate (maxBits + 2) 0
  for len in [1:maxBits + 1] do
    offs := offs.set! (len + 1) (offs[len]! + counts[len]!)
  let total := offs[maxBits + 1]!
  let mut symbols : Array UInt16 := Array.replicate total 0
  for n in [0:lengths.size] do
    let len := (lengths[n]!).toNat
    if len > 0 then
      let o := offs[len]!
      symbols := symbols.set! o (UInt16.ofNat n)
      offs := offs.set! len (o + 1)
  return { counts := counts.map UInt16.ofNat, symbols }

/-- Decode one symbol from the bit stream: walk code lengths `1..maxBits`,
reading one bit at a time and tracking `(code, first, index)` exactly as
RFC 1951's reference decoder (puff.c `decode`) does, without ever
constructing a full lookup table. -/
def Decoder.decodeSym (d : Decoder) (r : BitReader) : Except DecodeError (UInt16 × BitReader) := do
  let mut code : Nat := 0
  let mut first : Nat := 0
  let mut index : Nat := 0
  let mut r := r
  for len in [1:maxBits + 1] do
    let (bit, r') ← r.readBits 1
    r := r'
    code := code * 2 + bit.toNat
    let count := if len < d.counts.size then (d.counts[len]!).toNat else 0
    if code < first + count then
      let symIdx := index + (code - first)
      if symIdx < d.symbols.size then
        return (d.symbols[symIdx]!, r)
      else
        throw (.corrupt 0 "huffman decode: symbol table inconsistent with code lengths")
    index := index + count
    first := (first + count) * 2
  throw (.corrupt 0 "huffman decode: bit sequence does not match any code (incomplete tree)")

/-- One working item in the package-merge computation: a combined weight
and the multiset (with repetition) of compacted leaf indices it accounts
for. Package-merge tracks, for each of the `maxLen` "levels", which leaves
get packaged together; a leaf's final code length is exactly the number of
times it appears among the cheapest `2 * (n - 1)` items of the last
level. -/
private structure PMNode where
  weight : Nat
  sources : Array Nat
  deriving Inhabited

private def PMNode.merge (a b : PMNode) : PMNode :=
  { weight := a.weight + b.weight, sources := a.sources ++ b.sources }

/-- Length-limited code lengths for the given symbol frequencies
(package-merge). Symbols with zero frequency get length 0. Total: always
returns a valid ≤ `maxLen` code set for the nonzero symbols, provided the
usual feasibility precondition `(number of nonzero symbols) ≤ 2 ^ maxLen`
holds (always true for DEFLATE's alphabets: ≤ 288 symbols, `maxLen` = 15). -/
def lengthLimitedLengths (freqs : Array Nat) (maxLen : Nat) : Array UInt8 := Id.run do
  let mut lengths : Array UInt8 := Array.replicate freqs.size 0
  -- Compact list of original indices with nonzero frequency.
  let mut origIdx : Array Nat := #[]
  for i in [0:freqs.size] do
    if freqs[i]! > 0 then
      origIdx := origIdx.push i
  let n := origIdx.size
  if n == 0 then
    return lengths
  if n == 1 then
    return lengths.set! origIdx[0]! 1
  if maxLen == 0 then
    -- No valid assignment exists for ≥ 2 symbols; return all-zero rather
    -- than crash (caller violated the feasibility precondition).
    return lengths
  -- Level 1: one leaf per nonzero symbol, sorted ascending by weight.
  let leaves : Array PMNode :=
    (origIdx.mapIdx fun k oi => ({ weight := freqs[oi]!, sources := #[k] } : PMNode))
      |>.qsort (fun a b => a.weight < b.weight)
  let mut coins := leaves
  for _ in [1:maxLen] do
    -- Package: pair up adjacent coins from the previous level.
    let mut packages : Array PMNode := #[]
    let mut i := 0
    while i + 1 < coins.size do
      packages := packages.push (PMNode.merge coins[i]! coins[i + 1]!)
      i := i + 2
    -- Merge: packages plus a fresh copy of the leaves, sorted by weight.
    coins := (packages ++ leaves).qsort (fun a b => a.weight < b.weight)
  -- The cheapest `2 * (n - 1)` items of the final level determine lengths.
  let selectCount := min (2 * (n - 1)) coins.size
  let mut counts : Array Nat := Array.replicate n 0
  for j in [0:selectCount] do
    for k in coins[j]!.sources do
      if k < n then
        counts := counts.set! k (counts[k]! + 1)
  for k in [0:n] do
    let len := min (max counts[k]! 1) maxLen
    lengths := lengths.set! origIdx[k]! (UInt8.ofNat len)
  return lengths

end PILean.Compress.Huffman
