/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Png.Checksum
import PILean.Png.Tables

/-!
# DEFLATE and zlib: the decompressor

A decompressor for zlib streams (RFC 1950) and raw DEFLATE streams (RFC 1951) that treats its
input as untrusted: every length is checked, the output size is capped by the caller, every loop
is bounded by the input, and every failure is a value of `InflateError`, never a panic.

## Main definitions

* `InflateError`: why a stream was rejected.
* `inflateRaw`: decodes DEFLATE blocks starting at a byte position; returns the output and the
  position after the last block.
* `zlibDecompress`: checks the zlib header and the Adler-32 trailer around `inflateRaw`.

## Implementation notes

* Work is bounded: each block header consumes three bits, each symbol at least one bit, and each
  byte copied by a match counts against the output cap; the loops run over at most as many steps
  as the input has bits (plus the cap for match copies).
* Huffman codes are decoded canonically (by code length counts), with these rules, which are
  those of RFC 1951 and of zlib: a code that is over-subscribed is rejected; an incomplete code
  is rejected, except that a code with a single symbol of length 1 is accepted (so a block that
  uses one distance code, or none, is valid), and a code with no symbols is accepted (using it
  is an error at the point of use). The code-length code must be complete. A dynamic block
  must give the end-of-block symbol a code, may declare at most 286 literal/length and 30
  distance codes, and a run of code lengths may not cross the declared total or repeat a
  previous length that does not exist. Symbols 286 and 287 of the fixed code, and distance
  symbols 30 and 31, are errors when used.
* A stored block's `LEN` and `NLEN` must be complements, and its bytes must be present.
* A back reference may not reach before the start of the output; references may reach across
  block boundaries.
* `zlibDecompress` requires `CM = 8`, `CINFO ≤ 7`, a correct check value (`FCHECK`), no preset
  dictionary, and the Adler-32 of the output; bytes after the trailer are an error unless
  `allowTrailing` is set.

## References

* RFC 1950, ZLIB Compressed Data Format Specification version 3.3.
* RFC 1951, DEFLATE Compressed Data Format Specification version 1.3.
* Written from the published specifications; no existing implementation was consulted or copied.
-/

namespace PILean.Png

/-- Why a DEFLATE or zlib stream was rejected. -/
inductive InflateError where
  /-- The input ended inside a block, a header or the trailer. -/
  | truncated
  /-- The zlib header is wrong (method, window size or check value). -/
  | badZlibHeader
  /-- The zlib header asks for a preset dictionary, which is not supported. -/
  | presetDictionary
  /-- A block has the reserved type 3. -/
  | badBlockType
  /-- The `LEN` and `NLEN` of a stored block are not complements. -/
  | badStoredLength
  /-- The code lengths of a dynamic block are invalid (counts, repeats or missing end of block). -/
  | badCodeLengths
  /-- A Huffman code is over-subscribed. -/
  | oversubscribedCode
  /-- A Huffman code is incomplete (and not the single-symbol case). -/
  | incompleteCode
  /-- A bit sequence matches no code, or names a reserved symbol. -/
  | invalidSymbol
  /-- A back reference reaches before the start of the output or uses a reserved distance. -/
  | badDistance
  /-- The output would exceed the cap given by the caller. -/
  | outputTooLarge
  /-- The Adler-32 trailer does not match the output. -/
  | badChecksum
  /-- Bytes follow the end of the stream. -/
  | trailingData
deriving Repr, BEq, Inhabited, DecidableEq

/-- A short description of the error. -/
def InflateError.toString : InflateError → String
  | .truncated => "compressed data is truncated"
  | .badZlibHeader => "bad zlib header"
  | .presetDictionary => "zlib preset dictionaries are not supported"
  | .badBlockType => "reserved DEFLATE block type"
  | .badStoredLength => "stored block length check failed"
  | .badCodeLengths => "invalid code lengths in a dynamic block"
  | .oversubscribedCode => "over-subscribed Huffman code"
  | .incompleteCode => "incomplete Huffman code"
  | .invalidSymbol => "invalid Huffman symbol"
  | .badDistance => "invalid back reference distance"
  | .outputTooLarge => "decompressed data exceeds the size limit"
  | .badChecksum => "zlib checksum mismatch"
  | .trailingData => "data after the end of the compressed stream"

instance : ToString InflateError := ⟨InflateError.toString⟩

/-! ### Bit reader -/

/-- The bit reader state: the next input byte, and the `n` pending bits in `acc` (least
significant first). The input itself is passed to each function. -/
structure Bits where
  /-- Index of the next input byte to load. -/
  pos : Nat
  /-- The pending bits. -/
  acc : UInt64 := 0
  /-- The number of pending bits. -/
  n : Nat := 0

namespace Bits

/-- Loads input bytes while there is room for them in the 64-bit buffer. -/
def refill (data : ByteArray) (b : Bits) : Bits := Id.run do
  let mut b := b
  for _ in [0:8] do
    if b.n ≤ 56 && b.pos < data.size then
      b := { pos := b.pos + 1, acc := b.acc ||| ((byteAt data b.pos).toUInt64 <<< b.n.toUInt64),
             n := b.n + 8 }
  return b

/-- Reads `k ≤ 32` bits (least significant first). -/
def get (data : ByteArray) (b : Bits) (k : Nat) : Except InflateError (Nat × Bits) :=
  let b := if b.n < k then refill data b else b
  if b.n < k then .error .truncated
  else
    let v := (b.acc &&& ((1 <<< k.toUInt64) - 1)).toNat
    .ok (v, { b with acc := b.acc >>> k.toUInt64, n := b.n - k })

/-- Drops the pending bits up to the next input byte boundary and gives back the whole bytes
that were loaded but not used. -/
def alignToByte (b : Bits) : Bits := { pos := b.pos - b.n / 8, acc := 0, n := 0 }

end Bits

/-! ### Huffman decoding -/

/-- A canonical Huffman code for decoding: the number of codes of each length and the symbols
ordered by (length, symbol). -/
structure Huff where
  /-- `count[l]` is the number of codes of length `l` (index 0 unused). -/
  count : Array Nat
  /-- The symbols with a code, ordered by code length and then value. -/
  symbols : Array Nat

/-- Builds the decoding table for code lengths `lens` (each at most 15) under the rules in the
module documentation; `completeOnly` rejects the single-symbol exception. -/
def Huff.build (lens : Array Nat) (completeOnly : Bool := false) : Except InflateError Huff := do
  let mut count : Array Nat := Array.replicate 16 0
  for l in lens do
    if l > 15 then throw .badCodeLengths
    count := count.modify l (· + 1)
  let total := lens.size - count.getD 0 0
  let mut left : Int := 1
  for l in [1:16] do
    left := left * 2 - count.getD l 0
    if left < 0 then throw .oversubscribedCode
  if left > 0 && total > 0 then
    if completeOnly || !(total == 1 && count.getD 1 0 == 1) then throw .incompleteCode
  let mut offs : Array Nat := Array.replicate 17 0
  for l in [1:16] do
    offs := offs.setIfInBounds (l + 1) (offs.getD l 0 + count.getD l 0)
  let mut symbols : Array Nat := Array.replicate total 0
  for s in [0:lens.size] do
    let l := lens.getD s 0
    if l > 0 then
      symbols := symbols.setIfInBounds (offs.getD l 0) s
      offs := offs.modify l (· + 1)
  return { count, symbols }

/-- Decodes one symbol. -/
def Huff.decode (h : Huff) (data : ByteArray) (b : Bits) : Except InflateError (Nat × Bits) := do
  let b := if b.n < 15 then Bits.refill data b else b
  let mut code := 0
  let mut first := 0
  let mut index := 0
  for len in [1:16] do
    if len > b.n then throw .truncated
    code := code ||| ((b.acc >>> (len - 1).toUInt64) &&& 1).toNat
    let cnt := h.count.getD len 0
    if code < first + cnt then
      return (h.symbols.getD (index + (code - first)) 0,
        { b with acc := b.acc >>> len.toUInt64, n := b.n - len })
    index := index + cnt
    first := (first + cnt) <<< 1
    code := code <<< 1
  throw .invalidSymbol

/-! ### Blocks -/

/-- Decodes the symbols of one compressed block with the given codes; stops after the
end-of-block symbol. `size` is the length of the output so far. With `store`, the bytes are
appended to `out` (the whole output so far, which back references read); without it only `size`
advances, so the length of a stream can be measured without holding its output. -/
def inflateCodes (data : ByteArray) (lit dist : Huff) (maxOut : Nat) (store : Bool) (b : Bits)
    (size : Nat) (out : ByteArray) : Except InflateError (Bits × Nat × ByteArray) := do
  let mut b := b
  let mut size := size
  let mut out := out
  for _ in [0:data.size * 8 + 16] do
    let (sym, b1) ← lit.decode data b
    b := b1
    if sym < 256 then
      if size ≥ maxOut then throw .outputTooLarge
      size := size + 1
      if store then out := out.push sym.toUInt8
    else if sym == 256 then
      return (b, size, out)
    else if sym ≤ 285 then
      let k := sym - 257
      let (le, b2) ← Bits.get data b (lenExtra.getD k 0)
      let len := lenBase.getD k 0 + le
      let (ds, b3) ← dist.decode data b2
      if ds ≥ 30 then throw .badDistance
      let (de, b4) ← Bits.get data b3 (distExtra.getD ds 0)
      let d := distBase.getD ds 0 + de
      b := b4
      if d > size then throw .badDistance
      if size + len > maxOut then throw .outputTooLarge
      size := size + len
      if store then
        for _ in [0:len] do
          out := out.push (byteAt out (out.size - d))
    else throw .invalidSymbol
  throw .truncated

/-- The fixed Huffman codes of block type 1. -/
def fixedHuff : Except InflateError (Huff × Huff) := do
  return (← Huff.build fixedLitLens, ← Huff.build fixedDistLens)

/-- Reads the code lengths of a dynamic block and builds its two codes. -/
def readDynamic (data : ByteArray) (b : Bits) : Except InflateError (Huff × Huff × Bits) := do
  let (hlit, b) ← Bits.get data b 5
  let (hdist, b) ← Bits.get data b 5
  let (hclen, b) ← Bits.get data b 4
  let nlit := hlit + 257
  let ndist := hdist + 1
  if nlit > 286 || ndist > 30 then throw .badCodeLengths
  let mut b := b
  let mut cl : Array Nat := Array.replicate 19 0
  for i in [0:hclen + 4] do
    let (v, b1) ← Bits.get data b 3
    b := b1
    cl := cl.setIfInBounds (clOrder.getD i 0) v
  let clh ← Huff.build cl (completeOnly := true)
  let total := nlit + ndist
  let mut lens : Array Nat := #[]
  for _ in [0:total] do
    if lens.size ≥ total then break
    let (sym, b1) ← clh.decode data b
    b := b1
    if sym < 16 then lens := lens.push sym
    else
      let (rep, v, nb) := match sym with
        | 16 => (3, lens.back?.getD 0, 2)
        | 17 => (3, 0, 3)
        | _ => (11, 0, 7)
      if sym == 16 && lens.isEmpty then throw .badCodeLengths
      let (e, b2) ← Bits.get data b nb
      b := b2
      if lens.size + rep + e > total then throw .badCodeLengths
      for _ in [0:rep + e] do lens := lens.push v
  if lens.size != total then throw .badCodeLengths
  if lens.getD 256 0 == 0 then throw .badCodeLengths
  let lit ← Huff.build (lens.extract 0 nlit)
  let dist ← Huff.build (lens.extract nlit total)
  return (lit, dist, b)

/-- Decodes the DEFLATE blocks that start at byte `start` of `data`, producing at most `maxOut`
bytes. Returns the length of the output, the output (empty unless `store`; allocated once with
`capacity` bytes, so a `capacity` of the final length means no copy is made) and the index of
the first byte after the last block. -/
def inflateRaw (data : ByteArray) (start maxOut : Nat) (store : Bool := true)
    (capacity : Nat := 0) : Except InflateError (Nat × ByteArray × Nat) := do
  let mut b : Bits := { pos := start }
  let mut size := 0
  let mut out := ByteArray.emptyWithCapacity (if store then min capacity maxOut else 0)
  for _ in [0:data.size * 3 + 4] do
    let (fin, b1) ← Bits.get data b 1
    let (typ, b2) ← Bits.get data b1 2
    b := b2
    if typ == 0 then
      let b3 := Bits.alignToByte b
      if b3.pos + 4 > data.size then throw .truncated
      let len := (byteAt data b3.pos).toNat ||| ((byteAt data (b3.pos + 1)).toNat <<< 8)
      let nlen := (byteAt data (b3.pos + 2)).toNat ||| ((byteAt data (b3.pos + 3)).toNat <<< 8)
      if len ^^^ nlen != 0xFFFF then throw .badStoredLength
      let s := b3.pos + 4
      if s + len > data.size then throw .truncated
      if size + len > maxOut then throw .outputTooLarge
      size := size + len
      if store then out := data.copySlice s out out.size len
      b := { pos := s + len }
    else if typ == 1 then
      let (lit, dist) ← fixedHuff
      let (b3, n, o) ← inflateCodes data lit dist maxOut store b size out
      b := b3
      size := n
      out := o
    else if typ == 2 then
      let (lit, dist, b3) ← readDynamic data b
      let (b4, n, o) ← inflateCodes data lit dist maxOut store b3 size out
      b := b4
      size := n
      out := o
    else throw .badBlockType
    if fin == 1 then
      return (size, out, (Bits.alignToByte b).pos)
  throw .truncated

/-! ### zlib -/

/-- The number a big-endian trailer of four bytes stands for. -/
def trailerValue (b0 b1 b2 b3 : UInt8) : Nat :=
  b0.toNat * 16777216 + b1.toNat * 65536 + b2.toNat * 256 + b3.toNat

/-- Decompresses a zlib stream: checks the header, inflates, and checks the Adler-32 trailer.
The output is at most `maxOut` bytes. Bytes after the trailer are `.trailingData` unless
`allowTrailing`. With `expected := some n` (at most `maxOut`) the output is decoded into a buffer
of `n` bytes and may not exceed it; otherwise the stream is first decoded without keeping its output, to
learn its length, and then decoded into a buffer of exactly that length. Either way the only
large allocation is the output itself, made once, and a stream whose output would exceed
`maxOut` is rejected before it is made. -/
def zlibDecompress (data : ByteArray) (maxOut : Nat) (allowTrailing : Bool := false)
    (expected : Option Nat := none) : Except InflateError ByteArray := do
  if data.size < 2 then throw .truncated
  let cmf := (byteAt data 0).toNat
  let flg := (byteAt data 1).toNat
  if cmf &&& 15 != 8 || cmf >>> 4 > 7 || (cmf * 256 + flg) % 31 != 0 then throw .badZlibHeader
  if flg &&& 32 != 0 then throw .presetDictionary
  let size ← match expected with
    | some n => if n > maxOut then throw .outputTooLarge else pure n
    | none => pure (← inflateRaw data 2 maxOut (store := false)).1
  let (_, out, e) ← inflateRaw data 2 size (capacity := size)
  if e + 4 > data.size then throw .truncated
  if (adler32 out).toNat != trailerValue (byteAt data e) (byteAt data (e + 1))
      (byteAt data (e + 2)) (byteAt data (e + 3)) then throw .badChecksum
  if !allowTrailing && e + 4 != data.size then throw .trailingData
  return out

end PILean.Png
