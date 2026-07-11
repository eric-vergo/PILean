import PILean.Binary.Writer
import PILean.Compress.Checksum
import PILean.Compress.Inflate
import PILean.Compress.Deflate

/-!
# zlib framing (RFC 1950)

CMF/FLG header + raw DEFLATE + Adler-32 trailer. `compress` writes the
conventional `0x78 0x9C` header. `decompress` verifies the header
checksum, requires `CM = 8` and no preset dictionary, and verifies the
Adler-32 trailer.
-/

namespace PILean.Compress.Zlib

/-- Decompress a zlib (RFC 1950) stream: validates the CMF/FLG header
checksum, requires `CM = 8` (DEFLATE) and no preset dictionary (`FDICT`),
inflates the body, then verifies the trailing big-endian Adler-32 against
the decompressed bytes. -/
def decompress (data : ByteArray) : Except DecodeError ByteArray := do
  if data.size < 2 then
    throw (.truncated 0 "zlib header (CMF/FLG)")
  let cmf := data.get! 0
  let flg := data.get! 1
  let cm := cmf.toNat &&& 0x0F
  if cm != 8 then
    throw (.corrupt 0 s!"unsupported zlib compression method {cm} (expected 8, DEFLATE)")
  if (cmf.toNat * 256 + flg.toNat) % 31 != 0 then
    throw (.corrupt 0 "zlib header checksum (CMF/FLG) failed")
  if flg.toNat &&& 0x20 != 0 then
    throw (.unsupported "zlib" "FDICT preset dictionary")
  if data.size < 6 then
    throw (.truncated 2 "zlib compressed body/trailer")
  let body := data.extract 2 (data.size - 4)
  let trailer := data.extract (data.size - 4) data.size
  let decoded ← inflate body
  let expected : UInt32 :=
    ((trailer.get! 0).toUInt32 <<< 24) ||| ((trailer.get! 1).toUInt32 <<< 16) |||
    ((trailer.get! 2).toUInt32 <<< 8) ||| (trailer.get! 3).toUInt32
  let actual := adler32 decoded
  if actual != expected then
    throw (.corrupt (data.size - 4) s!"Adler-32 mismatch: expected {expected}, got {actual}")
  return decoded

/-- Compress into a zlib (RFC 1950) stream (header `0x78 0x9C`, raw
DEFLATE body, big-endian Adler-32 trailer). -/
def compress (data : ByteArray) (level : Nat := 6) : ByteArray :=
  let out := ((ByteArray.emptyWithCapacity (data.size + 16)).push 0x78).push 0x9C
  (out ++ deflate data level).pushU32be (adler32 data)

end PILean.Compress.Zlib
