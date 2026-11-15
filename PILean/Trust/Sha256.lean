/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# SHA-256

The secure hash algorithm SHA-256 over byte arrays, written from FIPS 180-4.

## Main definitions

* `Sha256.pad`: the padded message of section 5.1.1: the message, a `0x80` byte, zero bytes, and
  the message length in bits as a 64-bit big-endian number, in a multiple of 64 bytes.
* `Sha256.hash`: the 32-byte digest of a byte array.
* `Sha256.hashString`: the digest of the UTF-8 bytes of a string.
* `Sha256.hex`: bytes as lowercase hexadecimal text.

## Implementation notes

* The compression function works on `UInt32` words with the message schedule in one reused
  array of 64 words, so no list is built per byte; a 10 MB message takes a few seconds.
* The length field holds the length in bits modulo `2 ^ 64`, as the specification defines it for
  messages of fewer than `2 ^ 64` bits (no message here is larger).
* The facts about the padded length and the digest size are in `PILean/Trust/Sha256Proofs.lean`;
  the digests are tested against the published vectors in `PILeanTest/Trust.lean`.

## References

* FIPS 180-4, Secure Hash Standard (SHS), National Institute of Standards and Technology,
  August 2015, sections 4.1.2, 4.2.2, 5.1.1, 5.3.3, 6.2.
-/

namespace PILean.Sha256

/-- The number of zero bytes between the `0x80` byte and the length field for a message of `n`
bytes: the least number with `n + 1 + z + 8 ≡ 0 (mod 64)`. -/
def zeroCount (n : Nat) : Nat := (119 - n % 64) % 64

/-- The eight bytes of the message length `n` in bits, most significant byte first. -/
def lengthBytes (n : Nat) : ByteArray :=
  let bits := (n * 8) % 2 ^ 64
  ⟨#[(bits >>> 56).toUInt8, (bits >>> 48).toUInt8, (bits >>> 40).toUInt8,
    (bits >>> 32).toUInt8, (bits >>> 24).toUInt8, (bits >>> 16).toUInt8,
    (bits >>> 8).toUInt8, bits.toUInt8]⟩

/-- The padded message: `m`, the byte `0x80`, `zeroCount m.size` zero bytes and the eight bytes
of `lengthBytes m.size`. Its size is a multiple of 64. -/
def pad (m : ByteArray) : ByteArray :=
  m ++ ⟨#[0x80]⟩ ++ ⟨Array.replicate (zeroCount m.size) 0⟩ ++ lengthBytes m.size

/-- The constants `K₀ … K₆₃` of section 4.2.2: the first 32 bits of the fractional parts of the
cube roots of the first 64 primes. -/
def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- Rotation of a 32-bit word to the right by `n` bits, `0 < n < 32`. -/
@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- The eight working words of the hash computation. -/
structure State where
  /-- Word 0. -/
  a : UInt32
  /-- Word 1. -/
  b : UInt32
  /-- Word 2. -/
  c : UInt32
  /-- Word 3. -/
  d : UInt32
  /-- Word 4. -/
  e : UInt32
  /-- Word 5. -/
  f : UInt32
  /-- Word 6. -/
  g : UInt32
  /-- Word 7. -/
  h : UInt32

/-- The initial hash value of section 5.3.3: the first 32 bits of the fractional parts of the
square roots of the first eight primes. -/
def initialState : State :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
    0x5be0cd19⟩

/-- The big-endian word at byte `i` of `d` (bytes past the end read as 0). -/
@[inline] def wordAt (d : ByteArray) (i : Nat) : UInt32 :=
  (d.get! i).toUInt32 <<< 24 ||| (d.get! (i + 1)).toUInt32 <<< 16 |||
    (d.get! (i + 2)).toUInt32 <<< 8 ||| (d.get! (i + 3)).toUInt32

/-- The message schedule `W₀ … W₆₃` of the 64-byte block of `d` at byte `off`, written into `w`
(an array of 64 words). -/
def schedule (d : ByteArray) (off : Nat) (w : Array UInt32) : Array UInt32 := Id.run do
  let mut w := w
  for t in [0:16] do
    w := w.set! t (wordAt d (off + 4 * t))
  for t in [16:64] do
    let w2 := w[t - 2]!
    let w15 := w[t - 15]!
    let s1 := rotr w2 17 ^^^ rotr w2 19 ^^^ (w2 >>> 10)
    let s0 := rotr w15 7 ^^^ rotr w15 18 ^^^ (w15 >>> 3)
    w := w.set! t (s1 + w[t - 7]! + s0 + w[t - 16]!)
  return w

/-- One application of the compression function (section 6.2.2) to a state and a schedule. -/
def compress (st : State) (w : Array UInt32) : State := Id.run do
  let mut s := st
  for t in [0:64] do
    let bigS1 := rotr s.e 6 ^^^ rotr s.e 11 ^^^ rotr s.e 25
    let ch := (s.e &&& s.f) ^^^ (~~~s.e &&& s.g)
    let t1 := s.h + bigS1 + ch + roundConstants[t]! + w[t]!
    let bigS0 := rotr s.a 2 ^^^ rotr s.a 13 ^^^ rotr s.a 22
    let maj := (s.a &&& s.b) ^^^ (s.a &&& s.c) ^^^ (s.b &&& s.c)
    let t2 := bigS0 + maj
    s := ⟨t1 + t2, s.a, s.b, s.c, s.d + t1, s.e, s.f, s.g⟩
  return ⟨st.a + s.a, st.b + s.b, st.c + s.c, st.d + s.d, st.e + s.e, st.f + s.f, st.g + s.g,
    st.h + s.h⟩

/-- The four bytes of a word, most significant first. -/
def wordBytes (x : UInt32) : ByteArray :=
  ⟨#[(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]⟩

/-- The state after the compression function has been applied to every block of `pad m`. -/
def finalState (m : ByteArray) : State := Id.run do
  let p := pad m
  let mut st := initialState
  let mut w : Array UInt32 := Array.replicate 64 0
  for blk in [0:p.size / 64] do
    w := schedule p (blk * 64) w
    st := compress st w
  return st

/-- The 32 bytes of a state: its eight words, most significant byte first. -/
def digest (st : State) : ByteArray :=
  wordBytes st.a ++ wordBytes st.b ++ wordBytes st.c ++ wordBytes st.d ++
    wordBytes st.e ++ wordBytes st.f ++ wordBytes st.g ++ wordBytes st.h

/-- The SHA-256 digest of `m`: 32 bytes. -/
def hash (m : ByteArray) : ByteArray := digest (finalState m)

/-- The SHA-256 digest of the UTF-8 encoding of `s`. -/
def hashString (s : String) : ByteArray := hash s.toUTF8

/-- The bytes as lowercase hexadecimal text, two digits a byte. -/
def hex (b : ByteArray) : String :=
  b.foldl (init := "") fun out x =>
    (out.push (Nat.digitChar (x.toNat / 16))).push (Nat.digitChar (x.toNat % 16))

end PILean.Sha256
