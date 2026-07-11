import PILean.Binary.Writer
import PILean.Compress.BitStream
import PILean.Compress.Huffman
import PILean.Compress.LZ77

/-!
# DEFLATE — raw compression (RFC 1951)

Staged implementation, all behind the same signature:
(a) **stored blocks (current)**: ≤ 65535-byte blocks, BFINAL on last —
always valid, zero compression; (b) fixed Huffman over greedy LZ77 tokens;
(c) dynamic Huffman (per-block frequencies → package-merge → code-length
RLE 16/17/18, emit cheapest of stored/fixed/dynamic). WP10 lands (b)/(c).
Encoder edge rules for (c): if exactly one distance symbol is used it
still gets code length 1; if none are used, emit HDIST=1 with a single
zero length. On any edge the dynamic path can't handle, fall back to a
fixed block — always legal. `level 0` always means stored blocks.
-/

namespace PILean.Compress

set_option linter.unusedVariables false in
/-- Encode `data` as a raw DEFLATE (RFC 1951) stream. Total — never fails.
`level` 0 = stored, 1–9 = increasing effort.

Current stage: stored blocks at every level (valid DEFLATE, no
compression); WP10 upgrades levels 1–9 to fixed/dynamic Huffman behind
this signature. -/
def deflate (data : ByteArray) (level : Nat := 6) : ByteArray := Id.run do
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

end PILean.Compress
