import PILean.Core.Error

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# LSB-first bit streams

Bit-level reader/writer in DEFLATE bit order (RFC 1951: least-significant
bit of each byte first). Used by INFLATE/DEFLATE and GIF LZW.

**Not** for JPEG — JPEG entropy coding is MSB-first with 0xFF byte
stuffing and marker detection; it gets its own reader under
`PILean/Codec/Jpeg/`. Do not try to share.

Implementation notes for WP2: thread the structs explicitly or via
`let mut` in `Id.run do` — no `StateT` in the hot loop. `readBits` supports
`n ≤ 24`.
-/

namespace PILean.Compress

/-- LSB-first bit reader over a `ByteArray`. -/
structure BitReader where
  data : ByteArray
  /-- Byte position of the next byte to load into `bitBuf`. -/
  pos : Nat := 0
  /-- Buffered bits (consumed from the low end). -/
  bitBuf : UInt32 := 0
  /-- Number of valid bits in `bitBuf`. -/
  bitCnt : UInt32 := 0
  deriving Inhabited

namespace BitReader

/-- Read `n ≤ 24` bits, LSB-first. -/
def readBits (r : BitReader) (n : Nat) : Except DecodeError (UInt32 × BitReader) :=
  .error (.unsupported "bitstream" "BitReader.readBits not implemented yet (WP2)")

/-- Discard buffered bits up to the next byte boundary. -/
def alignByte (r : BitReader) : BitReader :=
  panic! "PILean.Compress.BitReader.alignByte: not implemented yet (WP2)"

/-- Read `n` whole bytes; only valid on a byte boundary (DEFLATE stored
blocks). -/
def readBytes (r : BitReader) (n : Nat) : Except DecodeError (ByteArray × BitReader) :=
  .error (.unsupported "bitstream" "BitReader.readBytes not implemented yet (WP2)")

end BitReader

/-- LSB-first bit writer. -/
structure BitWriter where
  out : ByteArray := ByteArray.empty
  /-- Pending bits not yet flushed to `out` (filled from the low end). -/
  bitBuf : UInt32 := 0
  /-- Number of valid bits in `bitBuf`. -/
  bitCnt : UInt32 := 0
  deriving Inhabited

namespace BitWriter

/-- Append the low `n ≤ 24` bits of `v`, LSB-first. -/
def writeBits (w : BitWriter) (v : UInt32) (n : Nat) : BitWriter :=
  panic! "PILean.Compress.BitWriter.writeBits: not implemented yet (WP2)"

/-- Pad with zero bits to the next byte boundary. -/
def alignByte (w : BitWriter) : BitWriter :=
  panic! "PILean.Compress.BitWriter.alignByte: not implemented yet (WP2)"

/-- Flush (zero-padding the final partial byte) and return the bytes. -/
def toByteArray (w : BitWriter) : ByteArray :=
  panic! "PILean.Compress.BitWriter.toByteArray: not implemented yet (WP2)"

end BitWriter

end PILean.Compress
