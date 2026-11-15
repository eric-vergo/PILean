/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# DEFLATE constants

The tables of RFC 1951 shared by the compressor and the decompressor: the base values and extra
bit counts of the length and distance symbols, the order of the code-length alphabet, and the
code lengths of the fixed Huffman codes.

## Main definitions

* `lenBase`, `lenExtra`: match length of symbol `257 + k` is `lenBase[k] + (extra bits)`.
* `distBase`, `distExtra`: the same for the 30 distance symbols.
* `clOrder`: the order in which the code lengths of the code-length alphabet are transmitted.
* `fixedLitLens`, `fixedDistLens`: the code lengths of the fixed Huffman block type.
* `lenIndex`, `distIndex`: the symbol index (`0 ≤ k < 29`, `0 ≤ k < 30`) that encodes a given
  match length or distance.

## References

* RFC 1951, DEFLATE Compressed Data Format Specification version 1.3, sections 3.2.5, 3.2.6 and
  3.2.7. Written from the published specification.
-/

namespace PILean.Png

/-- Smallest match length of each of the 29 length symbols `257 … 285`. -/
def lenBase : Array Nat :=
  #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115,
    131, 163, 195, 227, 258]

/-- Number of extra bits of each length symbol. -/
def lenExtra : Array Nat :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0]

/-- Smallest distance of each of the 30 distance symbols. -/
def distBase : Array Nat :=
  #[1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
    2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577]

/-- Number of extra bits of each distance symbol. -/
def distExtra : Array Nat :=
  #[0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13,
    13]

/-- The order in which the code lengths of the code-length alphabet are transmitted. -/
def clOrder : Array Nat := #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- The code lengths of the fixed literal/length code (288 symbols). -/
def fixedLitLens : Array Nat :=
  Array.ofFn (n := 288) fun i =>
    if i.val < 144 then 8 else if i.val < 256 then 9 else if i.val < 280 then 7 else 8

/-- The code lengths of the fixed distance code (32 symbols, all of length 5; the symbols 30
and 31 never occur in valid data). -/
def fixedDistLens : Array Nat := Array.replicate 32 5

/-- The length symbol index `k` (symbol `257 + k`) that encodes the match length `len`
(`3 ≤ len ≤ 258`; 258 is encoded by the last symbol). -/
def lenIndex (len : Nat) : Nat :=
  (List.range 29).foldl (fun k j => if lenBase.getD j 0 ≤ len then j else k) 0

/-- A lookup table for `lenIndex` on `0 … 258`. -/
def lenIndexTable : Array Nat := Array.ofFn (n := 259) fun i => lenIndex i.val

/-- The distance symbol that encodes the distance `d` (`1 ≤ d ≤ 32768`). -/
def distIndex (d : Nat) : Nat :=
  let x := d - 1
  if x < 4 then x else
    let nb := x.log2
    2 * nb + ((x >>> (nb - 1)) &&& 1)

/-- The byte at index `i`, or 0 beyond the end (a total accessor, so that no index is unchecked). -/
@[inline] def byteAt (d : ByteArray) (i : Nat) : UInt8 := if h : i < d.size then d[i] else 0

end PILean.Png
