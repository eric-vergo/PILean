/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Png.Checksum
import PILean.Png.Tables

/-!
# DEFLATE and zlib: the compressor

A zlib stream (RFC 1950) holding DEFLATE blocks (RFC 1951): stored, fixed Huffman and dynamic
Huffman blocks, with LZ77 matches found through hash chains.

## Main definitions

* `deflate`: the raw DEFLATE stream of a byte array at a compression level.
* `zlibCompress`: the zlib stream: two header bytes, the DEFLATE stream and the big-endian
  Adler-32 of the input.
* `huffLengths`: Huffman code lengths for a frequency table, limited to a maximum length.
* `canonicalCodes`: the canonical codes of RFC 1951 section 3.2.2 for given lengths.

## Implementation notes

* The output is a function of the input bytes and the level alone: there is no randomness and no
  dependence on the iteration order of a hash map.
* Levels: `0` writes stored blocks only. Levels `1` to `9` find matches in a hash chain over
  3-byte prefixes in the 32 KiB window; `lzParams` gives the chain length limit, the match length
  at which the search stops and whether matching is lazy (a match is deferred by one byte when
  the next position has a longer one). Level `6` is the default.
* Matches are found in the whole input (blocks do not restart the window). Every block holds at
  most `blockSymbols` literals and matches. For each block the exact bit cost of the stored,
  the fixed and the dynamic form is computed, and the smallest is written (a tie goes to the
  fixed form, then to the dynamic form).
* Huffman lengths are built with the two-queue method on symbols sorted by (frequency, symbol),
  which is deterministic. When a length exceeds the limit (15, or 7 for the code-length
  alphabet), every frequency is replaced by `(f + 1) / 2` and the code is rebuilt; this repeats
  until the lengths fit (at the latest when all used symbols have frequency 1, where the tree is
  balanced). An alphabet with fewer than two used symbols gets dummy symbols (the first unused
  ones) so that the code is complete.
* The two header bytes are `0x78` and a flag byte whose level field (0 fastest, 1 fast, 2
  default, 3 maximum) follows the level and whose check bits make the pair a multiple of 31.
* An empty input is a single final fixed block holding only the end-of-block symbol.

## References

* RFC 1950, ZLIB Compressed Data Format Specification version 3.3.
* RFC 1951, DEFLATE Compressed Data Format Specification version 1.3.
* Written from the published specifications; no existing implementation was consulted or copied.
-/

namespace PILean.Png

/-! ### Bit writer -/

/-- A DEFLATE bit sink: complete bytes in `out` and the `n < 8` pending low bits in `acc`
(least significant bit first, as DEFLATE packs them). -/
structure BitWriter where
  /-- The bytes completed so far. -/
  out : ByteArray := ByteArray.empty
  /-- The pending bits. -/
  acc : UInt64 := 0
  /-- The number of pending bits, below 8 between calls. -/
  n : Nat := 0

namespace BitWriter

/-- Moves every complete byte of the pending bits to the output (at most `fuel` of them). The
structure is taken apart so that the output array is updated in place. -/
def flushBytes : BitWriter → Nat → BitWriter
  | w, 0 => w
  | ⟨out, acc, n⟩, k + 1 =>
    if n ≥ 8 then flushBytes ⟨out.push acc.toUInt8, acc >>> 8, n - 8⟩ k else ⟨out, acc, n⟩

/-- Appends the low `bits` bits of `v` (`bits ≤ 32`), least significant first. -/
def put : BitWriter → Nat → Nat → BitWriter
  | ⟨out, acc, n⟩, v, bits =>
    let v' := v.toUInt64 &&& ((1 <<< bits.toUInt64) - 1)
    flushBytes ⟨out, acc ||| (v' <<< n.toUInt64), n + bits⟩ 5

/-- Pads with zero bits to the next byte boundary. -/
def align : BitWriter → BitWriter
  | ⟨out, acc, n⟩ => if n > 0 then ⟨out.push acc.toUInt8, 0, 0⟩ else ⟨out, acc, n⟩

/-- Appends whole bytes (the writer must be at a byte boundary). -/
def append : BitWriter → ByteArray → BitWriter
  | ⟨out, acc, n⟩, bytes => ⟨out ++ bytes, acc, n⟩

/-- The number of bits written so far. -/
def bitCount (w : BitWriter) : Nat := w.out.size * 8 + w.n

end BitWriter

/-! ### Huffman codes -/

/-- The code lengths the two-queue Huffman construction gives to the symbols with a positive
weight (`freq` has at least two of them). -/
def rawHuffman (freq : Array Nat) : Array Nat := Id.run do
  let n := freq.size
  let mut keys : Array Nat := #[]
  for s in [0:n] do
    if freq.getD s 0 > 0 then keys := keys.push (freq.getD s 0 * (n + 1) + s)
  keys := keys.qsort (· < ·)
  let m := keys.size
  let mut lens : Array Nat := Array.replicate n 0
  if m < 2 then return lens
  let leafW : Array Nat := keys.map (· / (n + 1))
  let mut intW : Array Nat := #[]
  let mut parent : Array Nat := Array.replicate (2 * m - 1) 0
  let mut li := 0
  let mut ii := 0
  for k in [0:m - 1] do
    let mut w := 0
    for _ in [0:2] do
      let useLeaf := li < m && (ii ≥ intW.size || leafW.getD li 0 ≤ intW.getD ii 0)
      if useLeaf then
        w := w + leafW.getD li 0
        parent := parent.setIfInBounds li (m + k)
        li := li + 1
      else
        w := w + intW.getD ii 0
        parent := parent.setIfInBounds (m + ii) (m + k)
        ii := ii + 1
    intW := intW.push w
  let mut depth : Array Nat := Array.replicate (2 * m - 1) 0
  for r in [0:2 * m - 2] do
    let id := 2 * m - 3 - r
    depth := depth.setIfInBounds id (depth.getD (parent.getD id 0) 0 + 1)
  for i in [0:m] do
    lens := lens.setIfInBounds (keys.getD i 0 % (n + 1)) (depth.getD i 0)
  return lens

/-- Huffman code lengths for the frequencies `freq` (an alphabet of at least two symbols), none
longer than `maxLen`. Fewer than two used symbols are completed with dummy symbols; the result
is always a complete prefix code. -/
def huffLengths (freq : Array Nat) (maxLen : Nat) : Array Nat := Id.run do
  let n := freq.size
  let mut f := freq
  let used := f.foldl (fun c x => if x > 0 then c + 1 else c) 0
  if used < 2 then
    let mut need := 2 - used
    for s in [0:n] do
      if need > 0 && f.getD s 0 == 0 then
        f := f.setIfInBounds s 1
        need := need - 1
  for _ in [0:70] do
    let lens := rawHuffman f
    if lens.all (· ≤ maxLen) then return lens
    f := f.map fun x => if x == 0 then 0 else (x + 1) / 2
  return rawHuffman (f.map fun x => if x == 0 then 0 else 1)

/-- Reverses the low `len` bits of `code`. -/
def reverseBits (code len : Nat) : Nat := Id.run do
  let mut r := 0
  let mut c := code
  for _ in [0:len] do
    r := (r <<< 1) ||| (c &&& 1)
    c := c >>> 1
  return r

/-- The canonical Huffman codes (RFC 1951 section 3.2.2) of the code lengths `lens`, each with
its bits reversed so that it can be written least significant bit first. Symbols of length 0
get code 0. -/
def canonicalCodes (lens : Array Nat) : Array Nat := Id.run do
  let mut blCount : Array Nat := Array.replicate 17 0
  for l in lens do
    if l > 0 then blCount := blCount.modify l (· + 1)
  let mut next : Array Nat := Array.replicate 17 0
  let mut code := 0
  for b in [1:16] do
    code := (code + blCount.getD (b - 1) 0) <<< 1
    next := next.setIfInBounds b code
  let mut out : Array Nat := Array.replicate lens.size 0
  for s in [0:lens.size] do
    let l := lens.getD s 0
    if l > 0 then
      let c := next.getD l 0
      out := out.setIfInBounds s (reverseBits c l)
      next := next.setIfInBounds l (c + 1)
  return out

/-- The reversed fixed literal/length codes. -/
def fixedLitCodes : Array Nat := canonicalCodes fixedLitLens

/-- The reversed fixed distance codes. -/
def fixedDistCodes : Array Nat := canonicalCodes fixedDistLens

/-! ### Run-length coding of code lengths -/

/-- One item of the code-length stream: the code-length symbol, and the value and number of its
extra bits. -/
structure ClItem where
  /-- The symbol `0 … 18` of the code-length alphabet. -/
  sym : Nat
  /-- The extra bits' value. -/
  extra : Nat
  /-- The number of extra bits. -/
  extraBits : Nat

/-- Run-length codes a sequence of code lengths with the symbols 16 (repeat the previous length
3 to 6 times), 17 (3 to 10 zeros) and 18 (11 to 138 zeros), greedily from the left. -/
def rleLengths (ls : Array Nat) : Array ClItem := Id.run do
  let mut items : Array ClItem := #[]
  let n := ls.size
  let mut i := 0
  for _ in [0:n + 1] do
    if i ≥ n then break
    let v := ls.getD i 0
    let mut run := 1
    for _ in [0:137] do
      if i + run < n && ls.getD (i + run) 0 == v then run := run + 1 else break
    if v == 0 && run ≥ 11 then
      items := items.push ⟨18, run - 11, 7⟩
      i := i + run
    else if v == 0 && run ≥ 3 then
      let r := min run 10
      items := items.push ⟨17, r - 3, 3⟩
      i := i + r
    else if v != 0 && run ≥ 4 then
      -- the first copy is written as a literal length, the rest by symbol 16
      items := items.push ⟨v, 0, 0⟩
      let r := min (run - 1) 6
      items := items.push ⟨16, r - 3, 2⟩
      i := i + 1 + r
    else
      items := items.push ⟨v, 0, 0⟩
      i := i + 1
  return items

/-! ### LZ77 -/

/-- The longest distance of a match. -/
def windowSize : Nat := 32768

/-- The longest match. -/
def maxMatch : Nat := 258

/-- The number of literals and matches in a block. -/
def blockSymbols : Nat := 1 <<< 15

/-- The parameters of the match search: the number of chain links followed, the match length
that ends the search early, and whether matching is lazy. -/
structure LzParams where
  /-- The number of hash-chain links followed per position. -/
  maxChain : Nat
  /-- A match this long is taken without looking further. -/
  niceLen : Nat
  /-- Whether a match is deferred when the next position has a longer one. -/
  lazy : Bool

/-- The search parameters of a level (`1 … 9`; larger values behave as 9). -/
def lzParams (level : Nat) : LzParams :=
  match level with
  | 0 | 1 => ⟨4, 16, false⟩
  | 2 => ⟨8, 32, false⟩
  | 3 => ⟨16, 64, false⟩
  | 4 => ⟨16, 32, true⟩
  | 5 => ⟨32, 64, true⟩
  | 6 => ⟨128, 128, true⟩
  | 7 => ⟨256, 200, true⟩
  | 8 => ⟨512, 258, true⟩
  | _ => ⟨1024, 258, true⟩

/-- The hash of the three bytes at `i` (15 bits). -/
@[inline] def hash3 (d : ByteArray) (i : Nat) : Nat :=
  let v := (byteAt d i).toNat <<< 16 ||| (byteAt d (i + 1)).toNat <<< 8 ||| (byteAt d (i + 2)).toNat
  ((v * 2654435761) &&& 0xFFFFFFFF) >>> 17

/-- Records position `i` in the hash tables (`head` maps a hash to the latest position plus one,
0 for none; `prev` links a position, modulo the window, to the previous one with the same hash);
nothing is recorded within two bytes of the end. -/
@[inline] def insertPos (head prev : Array Nat) (d : ByteArray) (i : Nat) :
    Array Nat × Array Nat :=
  if i + 3 ≤ d.size then
    let h := hash3 d i
    let old := head.getD h 0
    (head.setIfInBounds h (i + 1), prev.setIfInBounds (i &&& 32767) old)
  else (head, prev)

/-- The length of the common prefix of the data at `a` and at `b` (`a < b`), at most `limit`. -/
def matchLength (d : ByteArray) (a b limit : Nat) : Nat := Id.run do
  let mut k := 0
  for _ in [0:limit] do
    if byteAt d (a + k) == byteAt d (b + k) then k := k + 1 else break
  return k

/-- The longest match for position `i` in the chain, as (length, distance); length 0 if none of
length 3 or more. At most `maxChain` links are followed. -/
def findMatch (d : ByteArray) (head prev : Array Nat) (i : Nat) (p : LzParams) :
    Nat × Nat := Id.run do
  let limit := min maxMatch (d.size - i)
  if limit < 3 then return (0, 0)
  let mut best := 0
  let mut bestDist := 0
  let mut cand := head.getD (hash3 d i) 0
  for _ in [0:p.maxChain] do
    if cand == 0 then break
    let pos := cand - 1
    if pos ≥ i || i - pos > windowSize then break
    if best == 0 || byteAt d (pos + best) == byteAt d (i + best) then
      let l := matchLength d pos i limit
      if l > best then
        best := l
        bestDist := i - pos
        if l ≥ p.niceLen || l == limit then break
    let nxt := prev.getD (pos &&& 32767) 0
    if nxt == 0 || nxt - 1 ≥ pos then break
    cand := nxt
  if best < 3 then return (0, 0)
  return (best, bestDist)

/-- A block under construction: its symbols (literal `b` as `b`, match as
`2 ^ 31 + len * 2 ^ 16 + dist`) and their frequencies. -/
structure Block where
  /-- The symbols. -/
  toks : Array UInt32 := #[]
  /-- Frequencies of the literal/length symbols `0 … 285`. -/
  litFreq : Array Nat := Array.replicate 286 0
  /-- Frequencies of the distance symbols. -/
  distFreq : Array Nat := Array.replicate 30 0

/-- Adds a literal. -/
def Block.addLit : Block → UInt8 → Block
  | ⟨toks, lf, df⟩, v => ⟨toks.push v.toUInt32, lf.modify v.toNat (· + 1), df⟩

/-- Adds a match of length `len` and distance `dist`. -/
def Block.addMatch : Block → Nat → Nat → Block
  | ⟨toks, lf, df⟩, len, dist =>
    ⟨toks.push ((1 : UInt32) <<< 31 ||| len.toUInt32 <<< 16 ||| dist.toUInt32),
      lf.modify (257 + lenIndexTable.getD len 0) (· + 1),
      df.modify (distIndex dist) (· + 1)⟩

/-! ### Writing blocks -/

/-- The index of the last element satisfying `p` (0 if there is none). -/
def lastIdx (a : Array Nat) (p : Nat → Bool) : Nat :=
  (List.range a.size).foldl (fun r i => if p (a.getD i 0) then i else r) 0

/-- The exact number of bits of the body of a compressed block (all symbols and the end of
block) under the given code lengths. -/
def bodyCost (litLens distLens litFreq distFreq : Array Nat) : Nat := Id.run do
  let mut c := 0
  for s in [0:litFreq.size] do
    let f := litFreq.getD s 0
    if f > 0 then
      c := c + f * (litLens.getD s 0 + (if s > 256 then lenExtra.getD (s - 257) 0 else 0))
  for s in [0:distFreq.size] do
    c := c + distFreq.getD s 0 * (distLens.getD s 0 + distExtra.getD s 0)
  return c

/-- The number of bits of `len` bytes as stored blocks written when `phase` bits of the current
byte are used. -/
def storedCost (phase len : Nat) : Nat :=
  let chunks := max 1 ((len + 65534) / 65535)
  3 + (8 - (phase + 3) % 8) % 8 + 32 * chunks + 8 * len + 8 * (chunks - 1)

/-- Writes `data[start, stop)` as stored blocks (at least one block); the last one carries the
final flag when `final` holds. -/
def writeStored (w : BitWriter) (data : ByteArray) (start stop : Nat) (final : Bool) :
    BitWriter := Id.run do
  let mut w := w
  let mut pos := start
  for _ in [0:(stop - start) / 65535 + 2] do
    let len := min 65535 (stop - pos)
    let last := pos + len ≥ stop
    w := (w.put (if last && final then 1 else 0) 1).put 0 2 |>.align
    w := (w.put len 16).put (len ^^^ 0xFFFF) 16
    w := w.append (data.extract pos (pos + len))
    pos := pos + len
    if last then break
  return w

/-- Writes the symbols of a block with the (reversed) codes, then the end of block. -/
def writeTokens (w : BitWriter) (toks : Array UInt32) (litCodes litLens distCodes distLens :
    Array Nat) : BitWriter := Id.run do
  let mut w := w
  for t in toks do
    if t >>> 31 == 0 then
      let s := t.toNat
      w := w.put (litCodes.getD s 0) (litLens.getD s 0)
    else
      let len := ((t >>> 16) &&& 0x1FF).toNat
      let dist := (t &&& 0xFFFF).toNat
      let k := lenIndexTable.getD len 0
      w := w.put (litCodes.getD (257 + k) 0) (litLens.getD (257 + k) 0)
      w := w.put (len - lenBase.getD k 0) (lenExtra.getD k 0)
      let ds := distIndex dist
      w := w.put (distCodes.getD ds 0) (distLens.getD ds 0)
      w := w.put (dist - distBase.getD ds 0) (distExtra.getD ds 0)
  return w.put (litCodes.getD 256 0) (litLens.getD 256 0)

/-- Writes a block of `data[start, stop)` whose symbols are in `blk`, in the cheapest of the
stored, fixed and dynamic forms. -/
def writeBlock (w : BitWriter) (data : ByteArray) (start stop : Nat) (blk : Block)
    (final : Bool) : BitWriter :=
  let fin := if final then 1 else 0
  let litFreq := blk.litFreq.modify 256 (· + 1)
  let distFreq := blk.distFreq
  -- dynamic
  let litLens := huffLengths litFreq 15
  let distLens := huffLengths distFreq 15
  let nlit := max 257 (lastIdx litLens (· > 0) + 1)
  let ndist := max 1 (lastIdx distLens (· > 0) + 1)
  let items := rleLengths (litLens.extract 0 nlit ++ distLens.extract 0 ndist)
  let clFreq := items.foldl (fun (a : Array Nat) it => a.modify it.sym (· + 1))
    (Array.replicate 19 0)
  let clLens := huffLengths clFreq 7
  let nclen := max 4 (lastIdx clOrder (fun s => clLens.getD s 0 > 0) + 1)
  let clCost := items.foldl (fun c it => c + clLens.getD it.sym 0 + it.extraBits) 0
  let dynCost := 3 + 14 + 3 * nclen + clCost + bodyCost litLens distLens litFreq distFreq
  let fixCost := 3 + bodyCost fixedLitLens fixedDistLens litFreq distFreq
  let stoCost := storedCost (w.n) (stop - start)
  if stoCost < fixCost && stoCost < dynCost then writeStored w data start stop final
  else if fixCost ≤ dynCost then
    let w := (w.put fin 1).put 1 2
    writeTokens w blk.toks fixedLitCodes fixedLitLens fixedDistCodes fixedDistLens
  else
    let w := ((w.put fin 1).put 2 2)
    let w := ((w.put (nlit - 257) 5).put (ndist - 1) 5).put (nclen - 4) 4
    let w := (clOrder.extract 0 nclen).foldl (fun w s => w.put (clLens.getD s 0) 3) w
    let clCodes := canonicalCodes clLens
    let w := items.foldl (fun w it =>
      (w.put (clCodes.getD it.sym 0) (clLens.getD it.sym 0)).put it.extra it.extraBits) w
    writeTokens w blk.toks (canonicalCodes litLens) litLens (canonicalCodes distLens) distLens

/-! ### The compressor -/

/-- The raw DEFLATE stream of `data` at `level` (`0` stored blocks only, `1 … 9` LZ77 with
Huffman coding; levels above 9 act as 9). -/
def deflate (data : ByteArray) (level : Nat := 6) : ByteArray := Id.run do
  if level == 0 then
    return (writeStored {} data 0 data.size true).align.out
  let p := lzParams level
  let n := data.size
  let mut w : BitWriter := {}
  let mut head : Array Nat := Array.replicate 32768 0
  let mut prev : Array Nat := Array.replicate 32768 0
  let mut blk : Block := {}
  let mut blockStart := 0
  let mut i := 0
  for _ in [0:n + 1] do
    if i ≥ n then break
    let (len, dist) := findMatch data head prev i p
    (head, prev) := insertPos head prev data i
    let mut takeMatch : Bool := decide (len ≥ 3)
    if takeMatch && p.lazy && len < p.niceLen && i + 1 < n then
      let (len2, _) := findMatch data head prev (i + 1) p
      if len2 > len then takeMatch := false
    if blk.toks.size ≥ blockSymbols then
      w := writeBlock w data blockStart i blk false
      blk := {}
      blockStart := i
    if takeMatch then
      blk := blk.addMatch len dist
      for k in [1:len] do
        (head, prev) := insertPos head prev data (i + k)
      i := i + len
    else
      blk := blk.addLit (byteAt data i)
      i := i + 1
  w := writeBlock w data blockStart n blk true
  return w.align.out

/-- The two zlib header bytes for a level: `CMF = 0x78` (deflate, 32 KiB window) and `FLG` with
the level field and the check bits (no preset dictionary). -/
def zlibHeader (level : Nat) : UInt8 × UInt8 :=
  let flevel := if level ≤ 1 then 0 else if level ≤ 5 then 1 else if level == 6 then 2 else 3
  let base := 0x7800 + flevel * 64
  (0x78, (flevel * 64 + (31 - base % 31) % 31).toUInt8)

/-- The four bytes of the zlib trailer: the Adler-32 in big-endian order. -/
def trailerBytes (a : UInt32) : List UInt8 :=
  [(a >>> 24).toUInt8, (a >>> 16).toUInt8, (a >>> 8).toUInt8, a.toUInt8]

/-- The zlib stream (RFC 1950) of `data`: header, DEFLATE stream, big-endian Adler-32. -/
def zlibCompress (data : ByteArray) (level : Nat := 6) : ByteArray :=
  let (cmf, flg) := zlibHeader level
  (((ByteArray.empty.push cmf).push flg) ++ deflate data level) ++
    ⟨(trailerBytes (adler32 data)).toArray⟩

end PILean.Png
