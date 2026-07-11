/-!
# Binary writing

`ByteArray` appenders for encoders. No monad — builders chain with `|>.`
on a linearly-used buffer, which keeps the reference count at 1 and appends
in place. Always preallocate with `ByteArray.emptyWithCapacity` when the
output size is known.
-/

namespace ByteArray

/-- Append a little-endian 16-bit integer. -/
@[inline] def pushU16le (b : ByteArray) (v : UInt16) : ByteArray :=
  (b.push v.toUInt8).push (v >>> 8).toUInt8

/-- Append a big-endian 16-bit integer. -/
@[inline] def pushU16be (b : ByteArray) (v : UInt16) : ByteArray :=
  (b.push (v >>> 8).toUInt8).push v.toUInt8

/-- Append a little-endian 32-bit integer. -/
@[inline] def pushU32le (b : ByteArray) (v : UInt32) : ByteArray :=
  ((((b.push v.toUInt8).push (v >>> 8).toUInt8).push (v >>> 16).toUInt8).push (v >>> 24).toUInt8)

/-- Append a big-endian 32-bit integer. -/
@[inline] def pushU32be (b : ByteArray) (v : UInt32) : ByteArray :=
  ((((b.push (v >>> 24).toUInt8).push (v >>> 16).toUInt8).push (v >>> 8).toUInt8).push v.toUInt8)

/-- Append a string's UTF-8 bytes (for ASCII headers and chunk types). -/
@[inline] def pushAscii (b : ByteArray) (s : String) : ByteArray :=
  b ++ s.toUTF8

/-- A fresh buffer of `n` copies of byte `v`. -/
def replicateByte (n : Nat) (v : UInt8) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    b := b.push v
  return b

end ByteArray
