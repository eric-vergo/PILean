import PILean.Binary.Writer
import PILean.Compress.BitStream
import PILean.Compress.Huffman
import PILean.Compress.LZ77
import PILean.Compress.Inflate

/-!
# DEFLATE — raw compression (RFC 1951)

`level 0` always emits stored blocks (zero compression, always valid —
also the final fallback shape for any single block, though the general
encoder below prefers fixed/dynamic Huffman whenever they're cheaper).
`level ≥ 1` runs `LZ77.tokenize`, splits the resulting tokens into blocks
of at most 65536 tokens, and for each block writes whichever of
stored / fixed-Huffman / dynamic-Huffman has the lowest *exact* bit cost:

- fixed: RFC 1951's hardcoded literal/length and distance code lengths
  (see `Inflate.fixedLitLenLengths`/`fixedDistLengths`), so it never fails.
- dynamic: token frequencies → `Huffman.lengthLimitedLengths` (≤ 15 bits)
  → `Huffman.canonicalCodes`, with the code-length sequence itself RLE'd
  (repeat codes 16/17/18) and Huffman-coded with a third, ≤ 7-bit-limited
  table. If any of these three `canonicalCodes` calls fails (should not
  happen given `lengthLimitedLengths`'s feasibility guarantee, but is not
  relied upon), the block falls back to fixed Huffman.
- stored: only considered when the block's source byte span fits the
  16-bit LEN field (≤ 65535 bytes); a full 65536-token block never does
  (every token consumes ≥ 1 source byte), but the final, possibly
  shorter, block of a large input often does.

Every block ends with the end-of-block symbol 256; `BFINAL` is set only on
the last block written.
-/

namespace PILean.Compress

/-! ## Encoder-side helpers on the RFC tables (`Inflate` hosts the tables
themselves, shared between both files). -/

/-- The length-code symbol (`0..28`, i.e. literal/length symbol `257 + idx`)
and its extra-bit count for a match length `3 ≤ len ≤ 258` (linear scan
over the 29-entry `lengthBase` table — called once per match token, cheap). -/
private def lengthCodeFor (len : Nat) : Nat × Nat := Id.run do
  let mut idx := 0
  for i in [0:lengthBase.size] do
    if lengthBase[i]! ≤ len then
      idx := i
  return (idx, lengthExtraBits[idx]!)

/-- The distance-code symbol (`0..29`) and its extra-bit count for a match
distance `1 ≤ dist ≤ 32768` (linear scan over the 30-entry `distBase`
table — called once per match token, cheap). -/
private def distCodeFor (dist : Nat) : Nat × Nat := Id.run do
  let mut sym := 0
  for i in [0:distBase.size] do
    if distBase[i]! ≤ dist then
      sym := i
  return (sym, distExtraBits[sym]!)

/-- Decoded byte length of one LZ77 token (1 for a literal, the match
length for a back-reference). -/
private def tokenDecodedLen (t : UInt32) : Nat :=
  if t &&& 0x80000000 != 0 then ((t >>> 16) &&& 0x7FFF).toNat else 1

/-- Total decoded byte length of a run of tokens. -/
private def chunkByteLength (chunk : Array UInt32) : Nat :=
  chunk.foldl (fun acc t => acc + tokenDecodedLen t) 0

/-- Exact bit cost of one token under a given literal/length + distance
code-length table (used for both the fixed table and a candidate dynamic
table, so the two can be compared on equal footing). -/
private def tokenBitCost (litLens distLens : Array UInt8) (t : UInt32) : Nat :=
  if t &&& 0x80000000 != 0 then
    let len := ((t >>> 16) &&& 0x7FFF).toNat
    let dist := (t &&& 0xFFFF).toNat
    let (lidx, lextra) := lengthCodeFor len
    let (didx, dextra) := distCodeFor dist
    (litLens[257 + lidx]!).toNat + lextra + (distLens[didx]!).toNat + dextra
  else
    (litLens[t.toNat]!).toNat

/-- Reverse the low `n` bits of `v`. DEFLATE packs a Huffman codeword's
bits MSB-first (RFC 1951 §3.1.1), while `BitWriter.writeBits` emits a
value's bits LSB-first; reversing before writing reconciles the two, and
is the exact inverse of the bit-at-a-time accumulation
`Huffman.Decoder.decodeSym` does while reading. -/
private def reverseBits (v : UInt32) (n : Nat) : UInt32 := Id.run do
  let mut x := v
  let mut r : UInt32 := 0
  for _ in [0:n] do
    r := (r <<< 1) ||| (x &&& 1)
    x := x >>> 1
  return r

/-- Write symbol `sym`'s canonical codeword (from parallel `codes`/`lens`
tables) to the bit stream. -/
private def writeCode (w : BitWriter) (codes : Array UInt16) (lens : Array UInt8) (sym : Nat) :
    BitWriter :=
  let len := (lens[sym]!).toNat
  w.writeBits (reverseBits (codes[sym]!).toUInt32 len) len

/-! ## Level 0 / stored-block building block -/

/-- Encode `data` as stored (uncompressed) DEFLATE blocks, splitting into
≤ 65535-byte blocks as the 16-bit LEN field requires. Always valid, used
both as the whole of `level 0` and as one candidate the per-block cost
comparison at `level ≥ 1` can select. -/
def storedBlocks (data : ByteArray) : ByteArray := Id.run do
  let n := data.size
  let mut out := ByteArray.emptyWithCapacity (n + n / 65535 * 5 + 6)
  if n == 0 then
    -- one final stored block with LEN = 0
    return ((out.push 0x01).pushU16le 0).pushU16le 0xFFFF
  let mut pos := 0
  while pos < n do
    let len := min 65535 (n - pos)
    let final := pos + len == n
    -- BFINAL in bit 0, BTYPE = 00; the rest of the byte pads to the byte
    -- boundary, so a stored block's header is exactly one byte here.
    out := out.push (if final then 0x01 else 0x00)
    out := out.pushU16le (UInt16.ofNat len)
    out := out.pushU16le (UInt16.ofNat len ^^^ 0xFFFF)
    out := data.copySlice pos out out.size len
    pos := pos + len
  return out

/-- Write one stored block (`bytes`, already known to be ≤ 65535 long) to
the bit stream, aligning to the next byte boundary first. -/
private def writeStoredBlock (w : BitWriter) (bytes : ByteArray) (final : Bool) : BitWriter :=
  let w := w.writeBits (if final then 1 else 0) 1
  let w := w.writeBits 0 2
  let w := w.alignByte
  let len := bytes.size
  let hdr := (w.out.pushU16le (UInt16.ofNat len)).pushU16le (UInt16.ofNat len ^^^ 0xFFFF)
  { w with out := hdr ++ bytes }

/-! ## Fixed Huffman blocks -/

/-- Write one fixed-Huffman block for `chunk`'s tokens. -/
private def writeFixedBlock (w : BitWriter) (chunk : Array UInt32) (final : Bool) : BitWriter :=
  Id.run do
    let mut w := w.writeBits (if final then 1 else 0) 1
    w := w.writeBits 1 2
    for t in chunk do
      if t &&& 0x80000000 != 0 then
        let len := ((t >>> 16) &&& 0x7FFF).toNat
        let dist := (t &&& 0xFFFF).toNat
        let (lidx, lextra) := lengthCodeFor len
        w := writeCode w fixedLitLenCodes fixedLitLenLengths (257 + lidx)
        if lextra > 0 then
          w := w.writeBits (UInt32.ofNat (len - lengthBase[lidx]!)) lextra
        let (didx, dextra) := distCodeFor dist
        w := writeCode w fixedDistCodes fixedDistLengths didx
        if dextra > 0 then
          w := w.writeBits (UInt32.ofNat (dist - distBase[didx]!)) dextra
      else
        w := writeCode w fixedLitLenCodes fixedLitLenLengths t.toNat
    w := writeCode w fixedLitLenCodes fixedLitLenLengths 256
    return w

/-! ## Dynamic Huffman blocks -/

/-- One entry of the RLE'd code-length sequence: a code-length-alphabet
symbol (`0..18`), its extra-bits value (when the symbol is a repeat code
16/17/18), and how many extra bits that value needs (`0` for literal code
lengths `0..15`). -/
private structure ClToken where
  sym : Nat
  extraVal : Nat
  extraBits : Nat
  deriving Inhabited

/-- RLE-encode a sequence of code lengths (the concatenation of a block's
literal/length and distance code lengths) using repeat codes 16 (copy
previous length, 3–6 times), 17 (repeat a zero length, 3–10 times), and 18
(repeat a zero length, 11–138 times) — RFC 1951 §3.2.7. Greedy, not
necessarily bit-optimal, but always a valid encoding. Also returns the
resulting frequency of each of the 19 code-length symbols, for building
the code-length Huffman table. -/
private def rleEncodeLengths (seq : Array UInt8) : Array ClToken × Array Nat := Id.run do
  let mut tokens : Array ClToken := #[]
  let mut freq : Array Nat := Array.replicate 19 0
  let n := seq.size
  let mut i := 0
  while i < n do
    let curlen := seq[i]!
    let mut runLen := 1
    while i + runLen < n && seq[i + runLen]! == curlen do
      runLen := runLen + 1
    if curlen == 0 then
      let mut rem := runLen
      while rem > 0 do
        if rem ≥ 11 then
          let take := min rem 138
          tokens := tokens.push { sym := 18, extraVal := take - 11, extraBits := 7 }
          freq := freq.set! 18 (freq[18]! + 1)
          rem := rem - take
        else if rem ≥ 3 then
          let take := min rem 10
          tokens := tokens.push { sym := 17, extraVal := take - 3, extraBits := 3 }
          freq := freq.set! 17 (freq[17]! + 1)
          rem := rem - take
        else
          for _ in [0:rem] do
            tokens := tokens.push { sym := 0, extraVal := 0, extraBits := 0 }
            freq := freq.set! 0 (freq[0]! + 1)
          rem := 0
    else
      let s := curlen.toNat
      tokens := tokens.push { sym := s, extraVal := 0, extraBits := 0 }
      freq := freq.set! s (freq[s]! + 1)
      let mut rem := runLen - 1
      while rem > 0 do
        if rem ≥ 3 then
          let take := min rem 6
          tokens := tokens.push { sym := 16, extraVal := take - 3, extraBits := 2 }
          freq := freq.set! 16 (freq[16]! + 1)
          rem := rem - take
        else
          for _ in [0:rem] do
            tokens := tokens.push { sym := s, extraVal := 0, extraBits := 0 }
            freq := freq.set! s (freq[s]! + 1)
          rem := 0
    i := i + runLen
  return (tokens, freq)

/-- Trim trailing zero lengths off `lens`, but never below `minCount`
entries. Used both to compute `HLIT`/`HDIST` (the transmitted table sizes)
and, applied to the code-length table in transmission order, `HCLEN`. -/
private def trimTrailingZeros (lens : Array UInt8) (minCount : Nat) : Nat := Id.run do
  let mut n := lens.size
  while n > minCount && lens[n - 1]! == 0 do
    n := n - 1
  return n

/-- Token frequencies for one block: literal/length symbol counts (size
286: literals 0–255, end-of-block 256, length codes 257–285) and distance
symbol counts (size 30). The end-of-block symbol is always counted once,
since every block emits it exactly once. -/
private def tokenFreqs (chunk : Array UInt32) : Array Nat × Array Nat := Id.run do
  let mut litFreq : Array Nat := Array.replicate 286 0
  let mut distFreq : Array Nat := Array.replicate 30 0
  for t in chunk do
    if t &&& 0x80000000 != 0 then
      let len := ((t >>> 16) &&& 0x7FFF).toNat
      let dist := (t &&& 0xFFFF).toNat
      let (lidx, _) := lengthCodeFor len
      let (didx, _) := distCodeFor dist
      litFreq := litFreq.set! (257 + lidx) (litFreq[257 + lidx]! + 1)
      distFreq := distFreq.set! didx (distFreq[didx]! + 1)
    else
      let b := t.toNat
      litFreq := litFreq.set! b (litFreq[b]! + 1)
  litFreq := litFreq.set! 256 (litFreq[256]! + 1)
  return (litFreq, distFreq)

/-- A fully-built candidate dynamic-Huffman encoding for one block: the
three canonical code tables (literal/length, distance, code-length), the
header sizes to transmit, the RLE'd code-length sequence, and the exact
total bit cost (header + body), for comparison against fixed/stored. -/
private structure DynamicPlan where
  litLens : Array UInt8
  distLens : Array UInt8
  litCodes : Array UInt16
  distCodes : Array UInt16
  nLitLen : Nat
  nDist : Nat
  clLens : Array UInt8
  clCodes : Array UInt16
  clLensInOrder : Array UInt8
  rleTokens : Array ClToken
  cost : Nat
  deriving Inhabited

/-- Build the cheapest-effort dynamic-Huffman plan for `chunk`, or `none`
if any of the three `Huffman.canonicalCodes` calls fails (not expected —
`Huffman.lengthLimitedLengths` guarantees a Kraft-feasible code for
DEFLATE's alphabets — but the caller falls back to a fixed block rather
than relying on that). Implements the `HDIST` edge rules for free: a
single used distance symbol already gets length 1 from
`lengthLimitedLengths`'s own single-symbol rule, and an all-zero distance
frequency array trims (via `trimTrailingZeros _ 1`) to exactly one
zero-length entry. -/
private def buildDynamicPlan (chunk : Array UInt32) : Option DynamicPlan := Id.run do
  let (litFreq, distFreq) := tokenFreqs chunk
  let litLens := Huffman.lengthLimitedLengths litFreq 15
  let distLens := Huffman.lengthLimitedLengths distFreq 15
  let nLitLen := trimTrailingZeros litLens 257
  let nDist := trimTrailingZeros distLens 1
  let seq := (litLens.extract 0 nLitLen) ++ (distLens.extract 0 nDist)
  let (rleTokens, clFreq) := rleEncodeLengths seq
  let clLens := Huffman.lengthLimitedLengths clFreq 7
  let clLensInOrderFull := codeLengthOrder.map fun sym => clLens[sym]!
  let nCLen := trimTrailingZeros clLensInOrderFull 4
  match Huffman.canonicalCodes litLens, Huffman.canonicalCodes distLens, Huffman.canonicalCodes clLens with
  | .ok litCodes, .ok distCodes, .ok clCodes =>
    let headerBits := 5 + 5 + 4 + 3 * nCLen +
      rleTokens.foldl (fun acc t => acc + (clLens[t.sym]!).toNat + t.extraBits) 0
    let bodyBits := chunk.foldl (fun acc t => acc + tokenBitCost litLens distLens t) 0 +
      (litLens[256]!).toNat
    return some {
      litLens := litLens, distLens := distLens, litCodes := litCodes, distCodes := distCodes,
      nLitLen := nLitLen, nDist := nDist, clLens := clLens, clCodes := clCodes,
      clLensInOrder := clLensInOrderFull.extract 0 nCLen, rleTokens := rleTokens,
      cost := headerBits + bodyBits }
  | _, _, _ => return none

/-- Write one dynamic-Huffman block from an already-built `DynamicPlan`. -/
private def writeDynamicBlock (w : BitWriter) (d : DynamicPlan) (chunk : Array UInt32)
    (final : Bool) : BitWriter := Id.run do
  let mut w := w.writeBits (if final then 1 else 0) 1
  w := w.writeBits 2 2
  w := w.writeBits (UInt32.ofNat (d.nLitLen - 257)) 5
  w := w.writeBits (UInt32.ofNat (d.nDist - 1)) 5
  w := w.writeBits (UInt32.ofNat (d.clLensInOrder.size - 4)) 4
  for l in d.clLensInOrder do
    w := w.writeBits (UInt32.ofNat l.toNat) 3
  for t in d.rleTokens do
    w := writeCode w d.clCodes d.clLens t.sym
    if t.extraBits > 0 then
      w := w.writeBits (UInt32.ofNat t.extraVal) t.extraBits
  for t in chunk do
    if t &&& 0x80000000 != 0 then
      let len := ((t >>> 16) &&& 0x7FFF).toNat
      let dist := (t &&& 0xFFFF).toNat
      let (lidx, lextra) := lengthCodeFor len
      w := writeCode w d.litCodes d.litLens (257 + lidx)
      if lextra > 0 then
        w := w.writeBits (UInt32.ofNat (len - lengthBase[lidx]!)) lextra
      let (didx, dextra) := distCodeFor dist
      w := writeCode w d.distCodes d.distLens didx
      if dextra > 0 then
        w := w.writeBits (UInt32.ofNat (dist - distBase[didx]!)) dextra
    else
      w := writeCode w d.litCodes d.litLens t.toNat
  w := writeCode w d.litCodes d.litLens 256
  return w

/-! ## Per-block dispatch -/

/-- Encode one block (`chunk`'s tokens, spanning `data[dataStart:dataEnd)`)
by exact bit cost: build the fixed cost directly, build a dynamic plan
(if representable), compute the stored cost (only when the source span
fits a single ≤ 65535-byte stored block, accounting for the byte-alignment
padding the block header plus alignment would actually cost from `w`'s
current bit position), and write whichever is cheapest. -/
private def emitBlock (w : BitWriter) (chunk : Array UInt32) (data : ByteArray)
    (dataStart dataEnd : Nat) (final : Bool) : BitWriter :=
  let fixedCost := chunk.foldl (fun acc t => acc + tokenBitCost fixedLitLenLengths fixedDistLengths t) 0
    + (fixedLitLenLengths[256]!).toNat
  let dyn? := buildDynamicPlan chunk
  let chunkByteLen := dataEnd - dataStart
  -- After the 3-bit BFINAL+BTYPE header, alignment pads to the next byte.
  let afterHeaderBits := (w.bitCnt.toNat + 3) % 8
  let storedPad := (8 - afterHeaderBits) % 8
  let storedCost? := if chunkByteLen ≤ 65535 then some (storedPad + 32 + chunkByteLen * 8) else none
  let nonStoredCost := match dyn? with
    | some d => min d.cost fixedCost
    | none => fixedCost
  match storedCost? with
  | some sc =>
    if sc ≤ nonStoredCost then
      writeStoredBlock w (data.extract dataStart dataEnd) final
    else match dyn? with
      | some d => if d.cost < fixedCost then writeDynamicBlock w d chunk final else writeFixedBlock w chunk final
      | none => writeFixedBlock w chunk final
  | none => match dyn? with
    | some d => if d.cost < fixedCost then writeDynamicBlock w d chunk final else writeFixedBlock w chunk final
    | none => writeFixedBlock w chunk final

/-- Maximum number of LZ77 tokens per DEFLATE block at `level ≥ 1`, so each
block's Huffman tables can adapt to locally-varying statistics and no
block's frequency arrays grow unboundedly. -/
private def maxTokensPerBlock : Nat := 65536

/-- Encode `data` as a raw DEFLATE (RFC 1951) stream. Total — never fails.
`level` 0 = stored blocks; `level` 1–9 = `LZ77.tokenize` at that level, then
per-block cheapest of stored/fixed-Huffman/dynamic-Huffman (see module
docstring). Higher levels only change `LZ77.tokenize`'s match effort, not
the block-encoding strategy. -/
def deflate (data : ByteArray) (level : Nat := 6) : ByteArray :=
  if level == 0 then
    storedBlocks data
  else Id.run do
    let tokens := LZ77.tokenize data level
    let n := tokens.size
    let mut w : BitWriter := {}
    if n == 0 then
      w := emitBlock w #[] data 0 0 true
    else
      let mut i := 0
      let mut dataPos := 0
      while i < n do
        let chunkEnd := min n (i + maxTokensPerBlock)
        let chunk := tokens.extract i chunkEnd
        let chunkLen := chunkByteLength chunk
        let isFinal := chunkEnd == n
        w := emitBlock w chunk data dataPos (dataPos + chunkLen) isFinal
        dataPos := dataPos + chunkLen
        i := chunkEnd
    return w.toByteArray

end PILean.Compress
