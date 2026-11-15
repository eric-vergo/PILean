/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Png.Tables
import Std.Data.HashMap

/-!
# GIF's LZW compression

The variable-width LZW coding of GIF image data, and the data sub-blocks that carry it.

## Main definitions

* `Lzw.encode`: pixel indices to the code stream of a given minimum code size.
* `Lzw.decode`: the code stream back to exactly the expected number of indices, or an error.
* `Lzw.packBlocks`, `Lzw.unpackBlocks`: a byte string as data sub-blocks (at most 255 bytes
  each, ended by a zero-length block) and back.

## Implementation notes

* For minimum code size `m` the clear code is `2 ^ m`, the end-of-information code one more, the
  first free code two more. Codes are `m + 1` bits wide at first and grow by one bit whenever the
  next free code reaches a power of two, up to 12 bits; they are packed least significant bit
  first.
* The encoder starts with a clear code and emits a clear code, and restarts the table, as soon
  as the table holds all 4096 codes. The end-of-information code follows the last code. The
  output is a function of the input alone.
* The decoder rejects a stream that does not start with a clear code, a code beyond the next
  free entry, a first code after a clear that is not a literal, output beyond the expected
  count, and a stream that ends with fewer pixels. A full table is kept as it is (some encoders
  clear late). Every loop is bounded by the input length.

## References

* Graphics Interchange Format, Version 89a (CompuServe, 1990), appendix F "Variable-Length-Code
  LZW Compression". Written from the specification.
-/

namespace PILean.Anim.Lzw

/-- A bit sink: bytes written so far and the pending low bits. -/
structure BitSink where
  /-- Complete bytes. -/
  out : ByteArray := ByteArray.empty
  /-- Pending bits, least significant first. -/
  acc : Nat := 0
  /-- Number of pending bits (below 8 between calls). -/
  n : Nat := 0

/-- The sink after appending the `size` low bits of `code`. -/
def BitSink.put (w : BitSink) (code size : Nat) : BitSink := Id.run do
  let mut acc := w.acc ||| (code <<< w.n)
  let mut n := w.n + size
  let mut out := w.out
  for _ in [0:3] do
    if n ≥ 8 then
      out := out.push (acc &&& 255).toUInt8
      acc := acc >>> 8
      n := n - 8
  return { out, acc, n }

/-- The sink's bytes, with the last partial byte padded with zero bits. -/
def BitSink.finish (w : BitSink) : ByteArray :=
  if w.n > 0 then w.out.push (w.acc &&& 255).toUInt8 else w.out

/-- The LZW code stream of the indices `px`, for minimum code size `minCode` (2 to 8). Index
values are taken modulo `2 ^ minCode`. -/
def encode (minCode : Nat) (px : ByteArray) : ByteArray := Id.run do
  let clear := 1 <<< minCode
  let mask := clear - 1
  let mut sink : BitSink := ({} : BitSink).put clear (minCode + 1)
  let mut size := minCode + 1
  let mut next := clear + 2
  let mut dict : Std.HashMap Nat Nat := {}
  let mut cur := 0
  let mut started := false
  for b in px do
    let v := b.toNat &&& mask
    if !started then
      cur := v
      started := true
    else
      let key := (cur <<< 8) ||| v
      match dict[key]? with
      | some c => cur := c
      | none =>
        sink := sink.put cur size
        dict := dict.insert key next
        if next == (1 <<< size) && size < 12 then size := size + 1
        next := next + 1
        if next == 4096 then
          sink := sink.put clear size
          dict := {}
          next := clear + 2
          size := minCode + 1
        cur := v
  if started then
    sink := sink.put cur size
    if next == (1 <<< size) && size < 12 then size := size + 1
  sink := sink.put (clear + 1) size
  return sink.finish

/-- The `size` bits at bit position `pos` of `data`, least significant first. -/
def getBits (data : ByteArray) (pos size : Nat) : Nat :=
  let i := pos / 8
  let v := (Png.byteAt data i).toNat ||| ((Png.byteAt data (i + 1)).toNat <<< 8) |||
    ((Png.byteAt data (i + 2)).toNat <<< 16)
  (v >>> (pos % 8)) &&& ((1 <<< size) - 1)

/-- The decoder's table: for each code the code it extends, its last byte and its first byte. -/
structure Table where
  /-- The code each entry extends. -/
  pre : Array Nat
  /-- The last byte of each entry. -/
  suf : Array UInt8
  /-- The first byte of each entry. -/
  fst : Array UInt8

/-- The bytes of a code's string appended to `out`. -/
def emit (t : Table) (clear : Nat) (code : Nat) (out : ByteArray) : ByteArray := Id.run do
  let mut tmp := ByteArray.empty
  let mut c := code
  for _ in [0:4097] do
    if c < clear then break
    tmp := tmp.push (t.suf.getD c 0)
    c := t.pre.getD c 0
  tmp := tmp.push c.toUInt8
  let mut o := out
  for j in [0:tmp.size] do
    o := o.push (Png.byteAt tmp (tmp.size - 1 - j))
  return o

/-- The indices of an LZW code stream; the stream must hold exactly `expected` of them. -/
def decode (minCode : Nat) (data : ByteArray) (expected : Nat) : Except String ByteArray := do
  if minCode < 2 || minCode > 8 then throw "invalid minimum code size"
  let clear := 1 <<< minCode
  let mut t : Table := { pre := Array.replicate 4096 0, suf := Array.replicate 4096 0,
                         fst := Array.replicate 4096 0 }
  for i in [0:clear] do t := { t with fst := t.fst.setIfInBounds i i.toUInt8 }
  let mut next := clear + 2
  let mut size := minCode + 1
  let mut prev : Option Nat := none
  let mut out := ByteArray.emptyWithCapacity expected
  let mut pos := 0
  let mut started := false
  let mut finished := false
  for _ in [0:data.size * 8 / (minCode + 1) + 1] do
    if pos + size > data.size * 8 then break
    let code := getBits data pos size
    pos := pos + size
    if code == clear then
      started := true
      next := clear + 2
      size := minCode + 1
      prev := none
    else if !started then throw "stream does not start with a clear code"
    else if code == clear + 1 then
      finished := true
      break
    else
      match prev with
      | none =>
        if code ≥ clear then throw "invalid first code after a clear code"
        out := out.push code.toUInt8
        prev := some code
      | some p =>
        if code > next || (code == next && next ≥ 4096) then
          throw "code beyond the next free table entry"
        let fb := if code < next then t.fst.getD code 0 else t.fst.getD p 0
        if code == next then out := (emit t clear p out).push fb
        else out := emit t clear code out
        if next < 4096 then
          t := { pre := t.pre.setIfInBounds next p, suf := t.suf.setIfInBounds next fb,
                 fst := t.fst.setIfInBounds next (t.fst.getD p 0) }
          next := next + 1
          if next == (1 <<< size) && size < 12 then size := size + 1
        prev := some code
      if out.size > expected then throw "more pixels than the image holds"
  if out.size != expected then
    throw (if finished then "fewer pixels than the image holds" else "stream ends early")
  return out

/-- A byte string as data sub-blocks: blocks of at most 255 bytes, each after its length byte, and
a zero-length block at the end. -/
def packBlocks (data : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (data.size + data.size / 255 + 2)
  let mut pos := 0
  for _ in [0:data.size / 255 + 1] do
    if pos ≥ data.size then break
    let e := min data.size (pos + 255)
    out := (out.push (e - pos).toUInt8) ++ data.extract pos e
    pos := e
  return out.push 0

/-- The bytes of the data sub-blocks that start at `pos`, and the position after the terminating
zero-length block; an error if the input ends first. -/
def unpackBlocks (bytes : ByteArray) (pos : Nat) : Except String (ByteArray × Nat) := do
  let mut out := ByteArray.empty
  let mut p := pos
  for _ in [0:bytes.size + 1] do
    if p ≥ bytes.size then throw "data sub-blocks end early"
    let n := (Png.byteAt bytes p).toNat
    if p + 1 + n > bytes.size then throw "data sub-block runs past the end"
    if n == 0 then return (out, p + 1)
    out := out ++ bytes.extract (p + 1) (p + 1 + n)
    p := p + 1 + n
  throw "data sub-blocks end early"

end PILean.Anim.Lzw
