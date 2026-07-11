import PILean.Compress.BitStream
import PILean.Compress.Huffman

/-!
# INFLATE — raw DEFLATE decoding (RFC 1951)

Decodes stored, fixed-Huffman, and dynamic-Huffman blocks. Also hosts the
RFC 1951 constant tables (length/distance base + extra-bit tables, the
code-length alphabet permutation, and the fixed Huffman code-length
tables) that `PILean.Compress.Deflate`'s encoder reuses — both files are
owned together, so sharing them here avoids duplicating RFC trivia.

Back-references copy from the output buffer itself, byte-by-byte (needed
for overlapping copies where `dist < len`). Every malformed or truncated
input returns `DecodeError` — this module never panics or hangs, no
matter how hostile the input (fuzzed in `Tests/InflateTests.lean`).
-/

namespace PILean.Compress

/-! ## RFC 1951 constant tables (shared with `Deflate`) -/

/-- Base length (before adding extra bits) for length codes 257–285, in
symbol order. Index `i` corresponds to symbol `257 + i`. -/
def lengthBase : Array Nat :=
  #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59,
    67, 83, 99, 115, 131, 163, 195, 227, 258]

/-- Number of extra bits following each length code 257–285, in symbol
order (parallel to `lengthBase`). -/
def lengthExtraBits : Array Nat :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3,
    4, 4, 4, 4, 5, 5, 5, 5, 0]

/-- Base distance (before adding extra bits) for distance codes 0–29, in
symbol order. -/
def distBase : Array Nat :=
  #[1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513,
    769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577]

/-- Number of extra bits following each distance code 0–29, in symbol
order (parallel to `distBase`). -/
def distExtraBits : Array Nat :=
  #[0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8,
    9, 9, 10, 10, 11, 11, 12, 12, 13, 13]

/-- Transmission order of code-length-alphabet symbols (0–18) in a dynamic
Huffman block's HCLEN section (RFC 1951 §3.2.7). -/
def codeLengthOrder : Array Nat :=
  #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- Code lengths of the fixed literal/length Huffman table (RFC 1951
§3.2.6): 0–143 ↦ 8, 144–255 ↦ 9, 256–279 ↦ 7, 280–287 ↦ 8. Includes symbols
286/287, which have valid fixed codewords but are never legal to emit —
`inflateBlock` rejects them explicitly when decoded. -/
def fixedLitLenLengths : Array UInt8 := Id.run do
  let mut a : Array UInt8 := Array.replicate 288 0
  for i in [0:288] do
    let len : UInt8 := if i ≤ 143 then 8 else if i ≤ 255 then 9 else if i ≤ 279 then 7 else 8
    a := a.set! i len
  return a

/-- Code lengths of the fixed distance Huffman table: 5 bits for symbols
0–29. Deliberately sized 30 (not 32): distance codes 30/31 are reserved
and never assigned a codeword here, so `Huffman.decodeSym` naturally
rejects them (an "incomplete tree" `corrupt` error) rather than needing a
separate check. -/
def fixedDistLengths : Array UInt8 := Array.replicate 30 5

/-- The fixed literal/length decoder (RFC 1951 §3.2.6), built once. The
lengths are a fixed, always-valid canonical assignment, so this cannot
fail in practice; `Decoder.mk` (empty) is an unreachable fallback. -/
def fixedLitLenDecoder : Huffman.Decoder :=
  match Huffman.buildDecoder fixedLitLenLengths with
  | .ok d => d
  | .error _ => {}

/-- The fixed distance decoder (RFC 1951 §3.2.6), built once. See
`fixedLitLenDecoder` on why the error branch is unreachable. -/
def fixedDistDecoder : Huffman.Decoder :=
  match Huffman.buildDecoder fixedDistLengths with
  | .ok d => d
  | .error _ => {}

/-- Canonical codes for the fixed literal/length table, built once. Reused
by `Deflate`'s encoder (which must write the same codewords, MSB-first per
codeword, that this table's `Huffman.decodeSym` expects). -/
def fixedLitLenCodes : Array UInt16 :=
  match Huffman.canonicalCodes fixedLitLenLengths with
  | .ok c => c
  | .error _ => #[]

/-- Canonical codes for the fixed distance table, built once. -/
def fixedDistCodes : Array UInt16 :=
  match Huffman.canonicalCodes fixedDistLengths with
  | .ok c => c
  | .error _ => #[]

/-! ## Bit-level helpers -/

/-- Read `n` raw bytes for a stored block, correctly draining any whole
bytes already buffered in `r` (by `readBits`'s refill) before falling back
to reading fresh bytes directly from `r.data`. Plain `BitReader.readBytes`
must not be used here: it reads from `r.pos`, which after `alignByte` may
already be *ahead* of the logical stream position by the bytes sitting
unconsumed in `r.bitBuf`. Only valid once `r.bitCnt % 8 == 0` (i.e. after
`alignByte`). -/
def BitReader.readStoredBytes (r : BitReader) (n : Nat) : Except DecodeError (ByteArray × BitReader) := do
  let mut r := r
  let mut out := ByteArray.emptyWithCapacity n
  while r.bitCnt ≥ 8 && out.size < n do
    out := out.push r.bitBuf.toUInt8
    r := { r with bitBuf := r.bitBuf >>> 8, bitCnt := r.bitCnt - 8 }
  let remaining := n - out.size
  if remaining > 0 then
    let (bytes, r') ← r.readBytes remaining
    out := out ++ bytes
    r := r'
  return (out, r)

/-! ## Block decoding -/

/-- Decode one Huffman-coded block (fixed or dynamic — the only difference
is which decoders are passed in) starting at the first symbol and
finishing after consuming the end-of-block symbol 256. Literal/length
symbols 286/287 and distance symbols ≥ 30 are rejected; back-reference
distances further than the current output size are rejected
("dist-too-far"). -/
def inflateBlock (litlenDec distDec : Huffman.Decoder) (out : ByteArray) (r : BitReader) :
    Except DecodeError (ByteArray × BitReader) := do
  let mut out := out
  let mut r := r
  let mut done := false
  while !done do
    let (symV, r1) ← litlenDec.decodeSym r
    r := r1
    let sym := symV.toNat
    if sym < 256 then
      out := out.push (UInt8.ofNat sym)
    else if sym == 256 then
      done := true
    else if sym ≤ 285 then
      let idx := sym - 257
      let ebits := lengthExtraBits[idx]!
      let (extraV, r2) ← r.readBits ebits
      r := r2
      let len := lengthBase[idx]! + extraV.toNat
      let (distSymV, r3) ← distDec.decodeSym r
      r := r3
      let dsym := distSymV.toNat
      if dsym ≥ 30 then
        throw (.corrupt r.pos s!"invalid distance code {dsym}")
      let debits := distExtraBits[dsym]!
      let (dextraV, r4) ← r.readBits debits
      r := r4
      let dist := distBase[dsym]! + dextraV.toNat
      if dist == 0 || dist > out.size then
        throw (.corrupt r.pos s!"back-reference distance {dist} exceeds output size {out.size}")
      let start := out.size - dist
      for i in [0:len] do
        out := out.push (out.get! (start + i))
    else
      throw (.corrupt r.pos s!"invalid literal/length symbol {sym}")
  return (out, r)

/-- Read the dynamic-block header (HLIT/HDIST/HCLEN, the code-length code,
then the RLE'd literal/length + distance code lengths) and build the two
resulting decoders. `repeat-16` before any code length has been emitted is
rejected, as is any repeat count that would overrun the table. -/
def readDynamicTables (r : BitReader) :
    Except DecodeError (Huffman.Decoder × Huffman.Decoder × BitReader) := do
  let (hlitV, r1) ← r.readBits 5
  let (hdistV, r2) ← r1.readBits 5
  let (hclenV, r3) ← r2.readBits 4
  let mut r := r3
  let nLitLen := hlitV.toNat + 257
  let nDist := hdistV.toNat + 1
  let nCLen := hclenV.toNat + 4
  -- puff.c-style bound: rejects any header that would need litlen symbols
  -- 286/287 or distance symbols 30/31 to even be representable.
  if nLitLen > 286 then
    throw (.corrupt r.pos s!"HLIT too large ({nLitLen} literal/length codes)")
  if nDist > 30 then
    throw (.corrupt r.pos s!"HDIST too large ({nDist} distance codes)")
  let mut clLengths : Array UInt8 := Array.replicate 19 0
  for i in [0:nCLen] do
    let (l3, r') ← r.readBits 3
    r := r'
    clLengths := clLengths.set! (codeLengthOrder[i]!) (UInt8.ofNat l3.toNat)
  let clDecoder ← Huffman.buildDecoder clLengths
  let total := nLitLen + nDist
  let mut lens : Array UInt8 := Array.replicate total 0
  let mut i := 0
  while i < total do
    let (symV, r') ← clDecoder.decodeSym r
    r := r'
    let s := symV.toNat
    if s ≤ 15 then
      lens := lens.set! i (UInt8.ofNat s)
      i := i + 1
    else if s == 16 then
      if i == 0 then
        throw (.corrupt r.pos "repeat code 16 before any code length")
      let (extraV, r') ← r.readBits 2
      r := r'
      let count := extraV.toNat + 3
      if i + count > total then
        throw (.corrupt r.pos "repeat code 16 overruns the code-length table")
      let prev := lens[i - 1]!
      for _ in [0:count] do
        lens := lens.set! i prev
        i := i + 1
    else if s == 17 then
      let (extraV, r') ← r.readBits 3
      r := r'
      let count := extraV.toNat + 3
      if i + count > total then
        throw (.corrupt r.pos "repeat code 17 overruns the code-length table")
      for _ in [0:count] do
        lens := lens.set! i 0
        i := i + 1
    else if s == 18 then
      let (extraV, r') ← r.readBits 7
      r := r'
      let count := extraV.toNat + 11
      if i + count > total then
        throw (.corrupt r.pos "repeat code 18 overruns the code-length table")
      for _ in [0:count] do
        lens := lens.set! i 0
        i := i + 1
    else
      throw (.corrupt r.pos s!"invalid code-length symbol {s}")
  let litlenLengths := lens.extract 0 nLitLen
  let distLengths := lens.extract nLitLen total
  let litlenDec ← Huffman.buildDecoder litlenLengths
  let distDec ← Huffman.buildDecoder distLengths
  return (litlenDec, distDec, r)

/-- Decode a raw DEFLATE (RFC 1951) stream. `sizeHint` preallocates the
output buffer when the caller knows the decompressed size (e.g. PNG). -/
def inflate (compressed : ByteArray) (sizeHint : Nat := 0) : Except DecodeError ByteArray := do
  let mut out := ByteArray.emptyWithCapacity (max sizeHint compressed.size)
  let mut r : BitReader := { data := compressed }
  let mut final := false
  while !final do
    let (finalV, r1) ← r.readBits 1
    final := finalV == 1
    let (btypeV, r2) ← r1.readBits 2
    r := r2
    if btypeV == 0 then
      r := r.alignByte
      let (lenV, r3) ← r.readBits 16
      let (nlenV, r4) ← r3.readBits 16
      r := r4
      if (lenV ^^^ nlenV) != (0xFFFF : UInt32) then
        throw (.corrupt r.pos "stored block LEN/NLEN complement check failed")
      let (raw, r5) ← r.readStoredBytes lenV.toNat
      r := r5
      out := out ++ raw
    else if btypeV == 1 then
      let (out', r') ← inflateBlock fixedLitLenDecoder fixedDistDecoder out r
      out := out'
      r := r'
    else if btypeV == 2 then
      let (litlenDec, distDec, r') ← readDynamicTables r
      r := r'
      let (out', r'') ← inflateBlock litlenDec distDec out r
      out := out'
      r := r''
    else
      throw (.corrupt r.pos "reserved block type 3")
  return out

end PILean.Compress
