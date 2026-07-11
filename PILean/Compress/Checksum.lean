import PILean.Core.Error

/-!
# Checksums

CRC-32 (PNG, GIF) and Adler-32 (zlib). Both take a running value so
checksums chain across buffers: `crc32 b (crc32 a) = crc32 (a ++ b)`.

CRC-32 uses polynomial `0xEDB88320`, table-driven — the 256-entry table is
computed once in a plain top-level `def` (never a literal). The classic CRC
algorithm operates on an inverted running value; `crc32`'s `crc` parameter
and return value are the *externally visible* (non-inverted) checksum, with
the inversion applied/undone internally, so that the chaining identity
`crc32 b (crc32 a) = crc32 (a ++ b)` holds with the conventional default
`crc := 0` (rather than requiring callers to pass `0xFFFFFFFF`).

Adler-32 is mod 65521 with the standard NMAX = 5552 batching before
reduction (batching keeps the running sums from overflowing `UInt32` between
reductions, and lets us reduce with `%` far less often than once per byte).
-/

namespace PILean.Compress

/-- The 256-entry CRC-32 lookup table for polynomial `0xEDB88320`
(reflected form of the standard CRC-32 polynomial, as used by PNG, gzip,
and zlib). Computed once at load time, not embedded as a literal. -/
def crc32Table : Array UInt32 := Id.run do
  let mut table := Array.replicate 256 (0 : UInt32)
  for n in [0:256] do
    let mut c : UInt32 := UInt32.ofNat n
    for _ in [0:8] do
      if c &&& 1 == 1 then
        c := (0xEDB88320 : UInt32) ^^^ (c >>> 1)
      else
        c := c >>> 1
    table := table.set! n c
  return table

/-- CRC-32 (polynomial `0xEDB88320`, as used by PNG and zlib's gzip). Pass
the previous return value as `crc` to continue across buffers; the default
starts a fresh checksum. Satisfies `crc32 b (crc32 a) = crc32 (a ++ b)`. -/
def crc32 (data : ByteArray) (crc : UInt32 := 0) : UInt32 := Id.run do
  -- Classic CRC-32 runs on the bitwise-inverted value internally; invert on
  -- the way in and out so the public `crc` behaves as a plain accumulator.
  let mut c : UInt32 := crc ^^^ 0xFFFFFFFF
  for i in [0:data.size] do
    let b := data.get! i
    let idx := ((c ^^^ b.toUInt32) &&& 0xFF).toNat
    c := crc32Table[idx]! ^^^ (c >>> 8)
  return c ^^^ 0xFFFFFFFF

/-- Modulus for Adler-32 (the largest prime below 2^16). -/
private def adlerMod : UInt32 := 65521

/-- Largest number of bytes that can be summed into a `UInt32` accumulator
before reducing mod `adlerMod`, without overflow (standard zlib constant). -/
private def adlerNmax : Nat := 5552

/-- Adler-32 (RFC 1950). Pass the previous return value as `adler` to
continue across buffers; the default starts a fresh checksum. Satisfies
`adler32 b (adler32 a) = adler32 (a ++ b)`. -/
def adler32 (data : ByteArray) (adler : UInt32 := 1) : UInt32 := Id.run do
  let mut a : UInt32 := adler &&& 0xFFFF
  let mut b : UInt32 := (adler >>> 16) &&& 0xFFFF
  let n := data.size
  let mut i := 0
  while i < n do
    let chunk := min adlerNmax (n - i)
    for j in [i:i + chunk] do
      a := a + (data.get! j).toUInt32
      b := b + a
    a := a % adlerMod
    b := b % adlerMod
    i := i + chunk
  return (b <<< 16) ||| a

end PILean.Compress
