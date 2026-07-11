import PILean.Core.Error

/-!
# LSB-first bit streams

Bit-level reader/writer in DEFLATE bit order (RFC 1951: least-significant
bit of each byte first). Used by INFLATE/DEFLATE and GIF LZW.

**Not** for JPEG — JPEG entropy coding is MSB-first with 0xFF byte
stuffing and marker detection; it gets its own reader under
`PILean/Codec/Jpeg/`. Do not try to share.

The structs are threaded explicitly (no `StateT`): every operation takes
the current reader/writer and returns the updated one alongside its result.
`readBits`/`writeBits` support `n ≤ 24`, which keeps `bitBuf` (a `UInt32`)
from ever needing more than `24 + 7 = 31` bits at once.
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

/-- Read `n ≤ 24` bits, LSB-first: bits earlier in the stream land in the
low end of the result. Fails with `DecodeError.truncated` if fewer than `n`
bits remain in `r.data`. -/
def readBits (r : BitReader) (n : Nat) : Except DecodeError (UInt32 × BitReader) := Id.run do
  let nn : UInt32 := UInt32.ofNat n
  let mut buf := r.bitBuf
  let mut cnt := r.bitCnt
  let mut pos := r.pos
  -- Refill from `data`, LSB-first: each new byte's bits land above the
  -- bits already buffered (which are consumed from the low end).
  while cnt < nn do
    if pos < r.data.size then
      buf := buf ||| ((r.data.get! pos).toUInt32 <<< cnt)
      cnt := cnt + 8
      pos := pos + 1
    else
      return .error (.truncated pos s!"expected {n} bits, only {cnt} buffered")
  let mask : UInt32 := ((1 : UInt32) <<< nn) - 1
  let value := buf &&& mask
  return .ok (value, { r with pos := pos, bitBuf := buf >>> nn, bitCnt := cnt - nn })

/-- Discard buffered bits up to the next byte boundary (i.e. the remaining
bits of the byte currently being consumed). -/
def alignByte (r : BitReader) : BitReader :=
  let drop := r.bitCnt % 8
  { r with bitBuf := r.bitBuf >>> drop, bitCnt := r.bitCnt - drop }

/-- Read `n` whole bytes directly from the underlying data; only valid on a
byte boundary (call `alignByte` first, as DEFLATE stored blocks require).
Fails with `DecodeError.truncated` if fewer than `n` bytes remain. -/
def readBytes (r : BitReader) (n : Nat) : Except DecodeError (ByteArray × BitReader) :=
  if r.pos + n ≤ r.data.size then
    .ok (r.data.extract r.pos (r.pos + n), { r with pos := r.pos + n })
  else
    .error (.truncated r.pos s!"expected {n} bytes, only {r.data.size - r.pos} remain")

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

/-- Append the low `n ≤ 24` bits of `v`, LSB-first, flushing any bytes that
become complete. -/
def writeBits (w : BitWriter) (v : UInt32) (n : Nat) : BitWriter := Id.run do
  let nn : UInt32 := UInt32.ofNat n
  let mask : UInt32 := ((1 : UInt32) <<< nn) - 1
  let mut buf := w.bitBuf ||| ((v &&& mask) <<< w.bitCnt)
  let mut cnt := w.bitCnt + nn
  let mut out := w.out
  while cnt ≥ 8 do
    out := out.push buf.toUInt8
    buf := buf >>> 8
    cnt := cnt - 8
  return { out := out, bitBuf := buf, bitCnt := cnt }

/-- Pad with zero bits to the next byte boundary, flushing the (now
complete, zero-padded) partial byte. -/
def alignByte (w : BitWriter) : BitWriter :=
  if w.bitCnt == 0 then w
  else { out := w.out.push w.bitBuf.toUInt8, bitBuf := 0, bitCnt := 0 }

/-- Flush (zero-padding the final partial byte) and return the bytes. -/
def toByteArray (w : BitWriter) : ByteArray :=
  w.alignByte.out

end BitWriter

end PILean.Compress
