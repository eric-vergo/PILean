/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# CRC-32 and Adler-32

The two checksums of the PNG format: the CRC-32 of every PNG chunk and the Adler-32 trailer of a
zlib stream.

## Main definitions

* `crc32Bits`: the CRC-32 as the specification describes it, eight shift-and-xor steps per byte.
* `crc32`: the same function driven by a 256-entry table (`crcTable`), the one the code uses.
* `adler32`: the Adler-32 checksum, with the modulus applied after every byte.
* `adlerSpec`: the two sums of RFC 1950 written as the specification states them; `adler32`
  agrees with it (`PILean.Png.adler32_eq_adlerSpec`).

## Implementation notes

* The CRC is the reflected form of the polynomial `0x04C11DB7`, that is the constant `0xEDB88320`,
  with the register initialised to all ones and complemented at the end.
* The table is built from the bitwise byte step, so `crc32 = crc32Bits` is a theorem
  (`PILean.Png.crc32_eq_crc32Bits`).
* Both checksums fold over a `ByteArray`; they take no unchecked index.

## References

* PNG Specification, Third Edition (W3C), annex "Cyclic Redundancy Code algorithm".
* RFC 1950, ZLIB Compressed Data Format Specification version 3.3, section 8.2 (Adler-32).
* These modules are written from the published specifications; no existing implementation was
  consulted or copied.
-/

namespace PILean.Png

/-! ### CRC-32 -/

/-- The reflected CRC-32 polynomial of PNG, zlib and gzip. -/
def crcPoly : UInt32 := 0xEDB88320

/-- One shift-and-xor step of the reflected CRC register. -/
def crcBitStep (c : UInt32) : UInt32 :=
  if c &&& 1 == 1 then (c >>> 1) ^^^ crcPoly else c >>> 1

/-- Eight `crcBitStep`s: what the register does for one byte already xored into its low bits. -/
def crcByteBits (c : UInt32) : UInt32 :=
  crcBitStep (crcBitStep (crcBitStep (crcBitStep
    (crcBitStep (crcBitStep (crcBitStep (crcBitStep c)))))))

/-- The CRC-32 of a byte array, computed bit by bit exactly as the specification describes; the
reference that `crc32` is proved equal to. -/
def crc32Bits (data : ByteArray) : UInt32 :=
  data.foldl (fun c b => crcByteBits (c ^^^ b.toUInt32)) 0xFFFFFFFF ^^^ 0xFFFFFFFF

/-- The 256-entry CRC table: entry `i` is `crcByteBits i`. -/
def crcTable : Vector UInt32 256 := Vector.ofFn fun i => crcByteBits i.val.toUInt32

/-- One byte step of the table-driven CRC register. -/
def crcStep (c : UInt32) (b : UInt8) : UInt32 :=
  let x := c ^^^ b.toUInt32
  crcTable[x.toUInt8.toNat]'(by have := x.toUInt8.toNat_lt; omega) ^^^ (c >>> 8)

/-- The register after feeding `data` (without the initial and final complement); `crc32`
starts it at all ones. Streaming code can continue from a returned value. -/
def crcUpdate (c : UInt32) (data : ByteArray) : UInt32 := data.foldl crcStep c

/-- The CRC-32 of a byte array (table driven): `crc32 "123456789".toUTF8 = 0xCBF43926`. -/
def crc32 (data : ByteArray) : UInt32 := crcUpdate 0xFFFFFFFF data ^^^ 0xFFFFFFFF

/-! ### Adler-32 -/

/-- The Adler-32 modulus, the largest prime below `2 ^ 16`. -/
def adlerMod : Nat := 65521

/-- The Adler-32 checksum of a byte array: the low half is `1 + Σ dᵢ` and the high half is
`Σⱼ (1 + Σᵢ≤ⱼ dᵢ)`, both modulo `adlerMod`; the modulus is applied after every byte, so the
registers stay below `2 ^ 32`. -/
def adler32 (data : ByteArray) : UInt32 :=
  let st := data.foldl (fun (s : UInt32 × UInt32) b =>
    let a := (s.1 + b.toUInt32) % 65521
    (a, (s.2 + a) % 65521)) (1, 0)
  (st.2 <<< 16) + st.1

/-- The sum of the bytes of a list, as a natural number. -/
def byteSum (l : List UInt8) : Nat := (l.map UInt8.toNat).sum

/-- The two halves of Adler-32 as RFC 1950 states them, for a list of bytes `d₁ … dₙ`:
`A = (1 + d₁ + … + dₙ) mod 65521` and `B = (Σ_{k=1}^{n} (1 + d₁ + … + d_k)) mod 65521`. -/
def adlerSpec (l : List UInt8) : Nat × Nat :=
  ((1 + byteSum l) % adlerMod,
    (((List.range l.length).map fun k => 1 + byteSum (l.take (k + 1))).sum) % adlerMod)

end PILean.Png
