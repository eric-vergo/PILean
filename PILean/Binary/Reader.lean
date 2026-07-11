import PILean.Core.Error

/-!
# Binary reading

`ParseM` — the parsing monad for binary container formats (BMP, PNG chunks,
GIF blocks, JPEG markers, TIFF, Netpbm headers). Byte-cursor over a
`ByteArray` with typed little/big-endian reads and ASCII helpers.

Bit-level reading (DEFLATE, JPEG entropy coding) does **not** live here —
see `PILean.Compress.BitReader` (LSB-first) and the JPEG-specific MSB-first
reader; their semantics differ and must not be shared. `ParseM` is for
container structure, not hot per-byte loops.
-/

namespace PILean.Binary

/-- Cursor state for `ParseM`. -/
structure ReaderState where
  data : ByteArray
  pos : Nat := 0

/-- Parsing monad for binary container formats: cursor state plus
`DecodeError` failure. `EStateM` is core and compiles efficiently. -/
abbrev ParseM := EStateM DecodeError ReaderState

namespace ParseM

/-- Run a parser over `data` from position 0. -/
def run (p : ParseM α) (data : ByteArray) : Except DecodeError α :=
  match EStateM.run p { data } with
  | .ok a _ => .ok a
  | .error e _ => .error e

/-- Current byte offset. -/
@[inline] def pos : ParseM Nat := return (← get).pos

/-- Bytes remaining. -/
@[inline] def remaining : ParseM Nat := do
  let s ← get
  return s.data.size - s.pos

/-- Are we at end of input? -/
@[inline] def isEof : ParseM Bool := return (← remaining) == 0

/-- Next byte without advancing, or `none` at end of input. -/
@[inline] def peek? : ParseM (Option UInt8) := do
  let s ← get
  return if s.pos < s.data.size then some (s.data.get! s.pos) else none

/-- Read one byte. -/
@[inline] def u8 : ParseM UInt8 := do
  let s ← get
  if s.pos < s.data.size then
    let b := s.data.get! s.pos
    set { s with pos := s.pos + 1 }
    return b
  else
    throw (.truncated s.pos "expected a byte")

/-- Read a little-endian 16-bit integer. -/
@[inline] def u16le : ParseM UInt16 := do
  let a ← u8; let b ← u8
  return a.toUInt16 ||| (b.toUInt16 <<< 8)

/-- Read a big-endian 16-bit integer. -/
@[inline] def u16be : ParseM UInt16 := do
  let a ← u8; let b ← u8
  return (a.toUInt16 <<< 8) ||| b.toUInt16

/-- Read a little-endian 32-bit integer. -/
@[inline] def u32le : ParseM UInt32 := do
  let a ← u8; let b ← u8; let c ← u8; let d ← u8
  return a.toUInt32 ||| (b.toUInt32 <<< 8) ||| (c.toUInt32 <<< 16) ||| (d.toUInt32 <<< 24)

/-- Read a big-endian 32-bit integer. -/
@[inline] def u32be : ParseM UInt32 := do
  let a ← u8; let b ← u8; let c ← u8; let d ← u8
  return (a.toUInt32 <<< 24) ||| (b.toUInt32 <<< 16) ||| (c.toUInt32 <<< 8) ||| d.toUInt32

/-- Read `n` bytes (copied out of the input). -/
def take (n : Nat) : ParseM ByteArray := do
  let s ← get
  if s.pos + n ≤ s.data.size then
    let bs := s.data.extract s.pos (s.pos + n)
    set { s with pos := s.pos + n }
    return bs
  else
    throw (.truncated s.pos s!"expected {n} bytes, only {s.data.size - s.pos} remain")

/-- Advance past `n` bytes. -/
def skip (n : Nat) : ParseM Unit := do
  let s ← get
  if s.pos + n ≤ s.data.size then
    set { s with pos := s.pos + n }
  else
    throw (.truncated s.pos s!"cannot skip {n} bytes, only {s.data.size - s.pos} remain")

/-- Consume `magic`, or fail with `DecodeError.badMagic format`. -/
def expectBytes (magic : ByteArray) (format : String) : ParseM Unit := do
  let s ← get
  if s.pos + magic.size ≤ s.data.size then
    for i in [0:magic.size] do
      if s.data.get! (s.pos + i) != magic.get! i then
        throw (.badMagic format)
    set { s with pos := s.pos + magic.size }
  else
    throw (.badMagic format)

/-- Is `b` ASCII whitespace (space, TAB, LF, VT, FF, CR)? -/
@[inline] def isAsciiWhitespace (b : UInt8) : Bool :=
  b == 32 || (9 ≤ b && b ≤ 13)

/-- Skip any run of ASCII whitespace. -/
def skipAsciiWhitespace : ParseM Unit := do
  repeat
    match ← peek? with
    | some b =>
      if isAsciiWhitespace b then
        let _ ← u8
      else
        break
    | none => break

/-- Skip whitespace, then read a run of non-whitespace bytes as a `String`.
Fails on empty. -/
def asciiToken : ParseM String := do
  skipAsciiWhitespace
  let mut acc := ""
  repeat
    match ← peek? with
    | some b =>
      if isAsciiWhitespace b then break
      let _ ← u8
      acc := acc.push (Char.ofNat b.toNat)
    | none => break
  if acc.isEmpty then
    throw (.corrupt (← pos) "expected a token")
  return acc

/-- Skip whitespace, then read a decimal natural number. Fails if no digit
follows. -/
def asciiNat : ParseM Nat := do
  skipAsciiWhitespace
  let mut n := 0
  let mut seen := false
  repeat
    match ← peek? with
    | some b =>
      if 48 ≤ b && b ≤ 57 then
        let _ ← u8
        n := n * 10 + (b.toNat - 48)
        seen := true
      else
        break
    | none => break
  unless seen do
    throw (.corrupt (← pos) "expected a decimal integer")
  return n

end ParseM

end PILean.Binary
