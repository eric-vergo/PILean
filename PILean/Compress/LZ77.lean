/-!
# LZ77 matching

Greedy hash-chain matcher for DEFLATE. Independent of the bit/Huffman
layers so it is testable in isolation: `detokenize (tokenize d) = d`, and
every emitted match must actually match the source.

Token packing (frozen): a literal byte `b` is the `UInt32` value `b`;
a match of length `len` (3–258) at distance `dist` (1–32768) is
`0x80000000 ||| (len <<< 16) ||| dist`.

Implementation notes for WP3: 3-byte hash into `head : Array Int32`
(2^15 buckets) + `prev : Array Int32` ring; chain-probe cap scales with
`level` (1 → ~8 probes, 6 → ~128, 9 → ~1024).

This implementation keeps `head`/`prev` as plain `Nat` position tables
(sentinel = `data.size`, an otherwise-impossible position) rather than
`Int32`, since Lean's `Array.get!`/indexing works uniformly on `Nat` and it
avoids `Int32`-vs-`Nat` conversions in the hot loop; `prev` is sized to the
input rather than ring-buffered (simpler, and every chain walk still stops
as soon as the distance exceeds the 32768-byte window, so results and
worst-case probe counts are identical to a ring-buffer implementation —
only peak memory differs).
-/

namespace PILean.Compress.LZ77

/-- Minimum match length DEFLATE can encode as a back-reference. -/
private def minMatch : Nat := 3

/-- Maximum match length DEFLATE can encode as a back-reference. -/
private def maxMatch : Nat := 258

/-- Maximum back-reference distance DEFLATE allows. -/
private def maxDist : Nat := 32768

/-- Number of hash-chain buckets (`head`), and the mask for the 3-byte
rolling hash below. -/
private def hashSize : Nat := 32768

/-- Chain-probe cap per compression `level` (1 = fastest/worst, 9 =
slowest/best), interpolated between the module docstring's anchors
(1 → 8, 6 → 128, 9 → 1024). -/
private def probeLimit (level : Nat) : Nat :=
  let table : Array Nat := #[8, 16, 32, 64, 96, 128, 256, 512, 1024]
  let l := max 1 (min 9 level)
  table[l - 1]!

/-- 3-byte rolling hash of `data[p], data[p+1], data[p+2]`, folded into
`[0, hashSize)`. Caller must ensure `p + 2 < data.size`. -/
private def hash3 (data : ByteArray) (p : Nat) : Nat :=
  let b0 := (data.get! p).toUInt32
  let b1 := (data.get! (p + 1)).toUInt32
  let b2 := (data.get! (p + 2)).toUInt32
  (((b0 <<< 10) ^^^ (b1 <<< 5) ^^^ b2) &&& (UInt32.ofNat (hashSize - 1))).toNat

/-- Tokenize `data` into literals and back-references (see module docstring
for the packed `UInt32` token format). Higher `level` = more probes =
better matches, slower. -/
def tokenize (data : ByteArray) (level : Nat := 6) : Array UInt32 := Id.run do
  let n := data.size
  let mut tokens : Array UInt32 := Array.emptyWithCapacity n
  if n == 0 then
    return tokens
  let probe := probeLimit level
  -- `head[h]` = most recent position hashing to bucket `h`, or `noPos`.
  -- `prev[p]` = the position before `p` sharing `p`'s hash, or `noPos`.
  let noPos := n
  let mut head : Array Nat := Array.replicate hashSize noPos
  let mut prev : Array Nat := Array.replicate n noPos
  let mut pos := 0
  while pos < n do
    let mut bestLen := 0
    let mut bestDist := 0
    if pos + minMatch <= n then
      let h := hash3 data pos
      let mut cand := head[h]!
      let mut tries := 0
      let maxLen := min maxMatch (n - pos)
      while cand != noPos && tries < probe do
        let dist := pos - cand
        if dist == 0 || dist > maxDist then
          cand := noPos
        else
          let mut len := 0
          while len < maxLen && data.get! (cand + len) == data.get! (pos + len) do
            len := len + 1
          if len >= minMatch && len > bestLen then
            bestLen := len
            bestDist := dist
          cand := if cand < prev.size then prev[cand]! else noPos
          tries := tries + 1
    if bestLen >= minMatch then
      tokens := tokens.push
        ((0x80000000 : UInt32) ||| (UInt32.ofNat bestLen <<< 16) ||| UInt32.ofNat bestDist)
      -- Insert every position covered by the match so later matches can
      -- reach back into it.
      let stop := min n (pos + bestLen)
      let mut p := pos
      while p < stop do
        if p + minMatch <= n then
          let h2 := hash3 data p
          prev := prev.set! p head[h2]!
          head := head.set! h2 p
        p := p + 1
      pos := pos + bestLen
    else
      tokens := tokens.push (data.get! pos).toUInt32
      if pos + minMatch <= n then
        let h2 := hash3 data pos
        prev := prev.set! pos head[h2]!
        head := head.set! h2 pos
      pos := pos + 1
  return tokens

/-- Reconstruct the original bytes from tokens. For testing `tokenize`
(round-trip and match-validity checks); not used by the encoder proper.
Malformed tokens (zero or out-of-window distance) are skipped rather than
causing a panic — this is a test helper, not a decoder for untrusted
input, but it stays total regardless. -/
def detokenize (tokens : Array UInt32) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (tokens.size * 2)
  for t in tokens do
    if t &&& 0x80000000 != 0 then
      let len := ((t >>> 16) &&& 0x7FFF).toNat
      let dist := (t &&& 0xFFFF).toNat
      if dist > 0 && dist <= out.size then
        let srcStart := out.size - dist
        for i in [0:len] do
          let srcIdx := srcStart + i
          let b := if srcIdx < out.size then out.get! srcIdx else 0
          out := out.push b
    else
      out := out.push t.toUInt8
  return out

end PILean.Compress.LZ77
