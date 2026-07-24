import PILean.Core.Error
import PILean.Compress.BitStream
import Std.Data.HashMap

/-!
# LZW (GIF and TIFF variants)

Variable-code-width LZW with clear/EOI codes, parameterized by
`earlyChange` so a future TIFF reader can reuse the decoder: TIFF bumps the
code width one code *earlier* than GIF. GIF callers always pass `false`
(`compress` is hardwired to it, since GIF never needs the early variant).

## The width-bump convention (read this before touching either direction)

Both directions were reverse-engineered and cross-checked against Pillow
11.3.0's real C encoder/decoder (byte-for-byte on `minCodeSize = 8` LZW
streams extracted from actual `.gif` files, including forced dictionary
resets), not just derived from folklore, because folklore about "early
change" is inconsistently defined across sources. Ground truth: the width
bump is *delayed by one emitted code* relative to the naive "bump the
instant the dictionary grows" scheme.

Concretely, on a dictionary miss the encoder (1) emits the current code at
the *current* width, (2) applies any bump that was *scheduled by the
previous miss* (not this one), (3) inserts the new dictionary entry and,
if that insertion pushes `nextCode` past the threshold, *schedules* a bump
for the miss after next (not this emission). Symmetrically, the decoder
computes each new entry (and its resulting width bump) only once it has
decoded the *following* code (needed for that code's first byte, via
`firstByteOf`), so the bump naturally lands on the read right after that —
which lines up exactly with the encoder's schedule. This is why the
decoder's bump check runs *after* fully processing a code (affecting only
the next `readBits` call) while the encoder's runs *before* emitting the
next miss.

## Decoder must-handle cases (WP14)

KwKwK (`code == nextCode`, resolved as `prev`'s sequence with its own
first byte appended), deferred clear (dictionary full at 4096 and the
encoder never sends a clear — freeze at 12 bits and keep decoding, not an
error), first code after a clear must be a literal, missing EOI (stop at
data end, no error). `maxOutput` bounds the output (a decompression-bomb
guard; callers pass e.g. `width * height`).

## Dictionary-full policy (encoder)

"Grows to 4096 then emits a clear and resets" — the simplest correct
policy. Once `nextCode` would reach 4096, the encoder clears and restarts
at `minCodeSize + 1` bits instead of ever assigning code 4096 (which
wouldn't fit in the 12-bit ceiling anyway).
-/

namespace PILean.Compress.Lzw

/-- Number of bytes the dictionary entry for `code` expands to (1 for a
literal `< clearCode`, else 1 + the length of its pfx entry).
Termination is guaranteed by construction (`pfx` always points to a
strictly smaller code, so the chain is acyclic) — the loop bound is a
defensive cap against that invariant ever being violated by a bug. -/
private def chainLength (pfx : Array Nat) (clearCode code : Nat) : Nat := Id.run do
  let mut c := code
  let mut n := 1
  for _ in [0:4098] do
    if c < clearCode then
      return n
    c := pfx[c - clearCode - 2]!
    n := n + 1
  panic! "PILean.Compress.Lzw.chainLength: dictionary chain exceeded capacity"

/-- The first byte of the sequence `code` expands to (itself, if `code` is
a literal). Used both for KwKwK resolution and to fill in a newly-created
dictionary entry's suffix byte. -/
private def firstByteOf (pfx : Array Nat) (clearCode code : Nat) : UInt8 := Id.run do
  let mut c := code
  for _ in [0:4098] do
    if c < clearCode then
      return UInt8.ofNat c
    c := pfx[c - clearCode - 2]!
  panic! "PILean.Compress.Lzw.firstByteOf: dictionary chain exceeded capacity"

/-- Append `code`'s expansion to `out`. Walks the pfx chain once to
learn `len` bytes' worth of positions, writing back-to-front so the whole
sequence lands in forward order without any intermediate `Array`/`List`
allocation. -/
private def expandInto (out : ByteArray) (pfx : Array Nat) (suffix : Array UInt8)
    (clearCode code len : Nat) : ByteArray := Id.run do
  let base := out.size
  let mut o := out
  for _ in [0:len] do
    o := o.push 0
  let mut c := code
  let mut pos := base + len
  for _ in [0:4098] do
    pos := pos - 1
    if c < clearCode then
      o := o.set! pos (UInt8.ofNat c)
      return o
    else
      o := o.set! pos (suffix[c - clearCode - 2]!)
      c := pfx[c - clearCode - 2]!
  panic! "PILean.Compress.Lzw.expandInto: dictionary chain exceeded capacity"

/-- Decompress an LZW stream. `minCodeSize` is the GIF "LZW minimum code
size" (initial width is `minCodeSize + 1`, must be in `[2, 8]`); `maxOutput`
bounds the output (error past it — a decompression-bomb guard). `earlyChange
:= true` selects the TIFF width-bump quirk (one code earlier than GIF); GIF
decoding always uses `false`. See the module docstring for the exact
bump-timing convention (empirically matched against Pillow). Never panics:
every malformed shape (bad `minCodeSize`, a non-literal first code after a
clear, an out-of-range code, an output size past `maxOutput`) is a
`DecodeError.corrupt`; a missing end-of-information code is tolerated
(decoding just stops at the end of `data`). -/
def decompress (minCodeSize : Nat) (data : ByteArray) (maxOutput : Nat)
    (earlyChange : Bool := false) : Except DecodeError ByteArray := do
  if minCodeSize < 2 || minCodeSize > 8 then
    throw (.corrupt 0 s!"lzw: minCodeSize {minCodeSize} out of range [2, 8]")
  let clearCode := 1 <<< minCodeSize
  let eoiCode := clearCode + 1
  let mut width := minCodeSize + 1
  let mut r : BitReader := { data := data }
  let mut out : ByteArray := ByteArray.emptyWithCapacity (min (max maxOutput 1) (max data.size 16))
  let mut pfx : Array Nat := #[]
  let mut suffix : Array UInt8 := #[]
  let mut nextCode := clearCode + 2
  let mut prev? : Option Nat := none
  let mut justCleared := true
  let mut done := false
  while !done do
    match r.readBits width with
    | .error _ =>
      -- Missing EOI (or any truncation mid-code) is tolerated: stop with
      -- whatever has been decoded so far.
      done := true
    | .ok (codeV, r') =>
      r := r'
      let code := codeV.toNat
      if code == clearCode then
        pfx := #[]
        suffix := #[]
        nextCode := clearCode + 2
        width := minCodeSize + 1
        prev? := none
        justCleared := true
      else if code == eoiCode then
        done := true
      else if justCleared && code ≥ clearCode then
        throw (.corrupt r.pos s!"lzw: first code after a clear must be a literal, got {code}")
      else if code > nextCode then
        throw (.corrupt r.pos s!"lzw: invalid code {code} (next unassigned code is {nextCode})")
      else
        match prev? with
        | some p =>
          if nextCode < 4096 then
            let fb := if code == nextCode then firstByteOf pfx clearCode p
                      else firstByteOf pfx clearCode code
            pfx := pfx.push p
            suffix := suffix.push fb
            nextCode := nextCode + 1
            let bumpAt := if earlyChange then (1 <<< width) - 1 else (1 <<< width)
            if nextCode ≥ bumpAt && width < 12 then
              width := width + 1
          else if code == nextCode then
            throw (.corrupt r.pos "lzw: code refers to a dictionary slot beyond capacity")
        | none =>
          if code == nextCode then
            throw (.corrupt r.pos "lzw: KwKwK code with no previous code")
        let len := chainLength pfx clearCode code
        if out.size + len > maxOutput then
          throw (.corrupt r.pos s!"lzw: decompressed output would exceed {maxOutput} bytes")
        out := expandInto out pfx suffix clearCode code len
        prev? := some code
        justCleared := false
  return out

/-- Compress with LZW, parameterized by `earlyChange` (GIF's `compress`
below always passes `false`; the parameter exists so `Tests.LzwTests` can
build `earlyChange := true` vectors to exercise `decompress`'s TIFF path).
See the module docstring for the exact bump-timing convention. -/
def compressWith (minCodeSize : Nat) (data : ByteArray) (earlyChange : Bool) : ByteArray :=
  Id.run do
  let clearCode := 1 <<< minCodeSize
  let eoiCode := clearCode + 1
  let mut width := minCodeSize + 1
  let mut w : BitWriter := {}
  w := w.writeBits (UInt32.ofNat clearCode) width
  let mut dict : Std.HashMap (Nat × UInt8) Nat := Std.HashMap.emptyWithCapacity 4096
  let mut nextCode := clearCode + 2
  let mut pendingBump := false
  let mut hasCur := false
  let mut cur : Nat := 0
  for i in [0:data.size] do
    let c := data.get! i
    if !hasCur then
      cur := c.toNat
      hasCur := true
    else
      match dict.get? (cur, c) with
      | some code => cur := code
      | none =>
        w := w.writeBits (UInt32.ofNat cur) width
        if pendingBump then
          width := width + 1
          pendingBump := false
        if nextCode < 4096 then
          dict := dict.insert (cur, c) nextCode
          nextCode := nextCode + 1
          let bumpAt := if earlyChange then (1 <<< width) - 1 else (1 <<< width)
          if nextCode ≥ bumpAt && width < 12 then
            pendingBump := true
        else
          w := w.writeBits (UInt32.ofNat clearCode) width
          dict := Std.HashMap.emptyWithCapacity 4096
          nextCode := clearCode + 2
          width := minCodeSize + 1
          pendingBump := false
        cur := c.toNat
  if hasCur then
    w := w.writeBits (UInt32.ofNat cur) width
    if pendingBump then
      width := width + 1
      pendingBump := false
  w := w.writeBits (UInt32.ofNat eoiCode) width
  return w.toByteArray

/-- Compress with LZW (GIF variant; emits clear/EOI codes, `earlyChange :=
false`). `minCodeSize` should be in `[2, 8]` (GIF's LZW minimum code size)
and every byte of `data` must be `< 2^minCodeSize` — both are the caller's
responsibility (checked by `Gif.encodeFrames`, which always derives
`minCodeSize` from the actual palette size and remaps pixels into range),
since this is an internal encoding step over data PILean itself produced,
not a boundary that parses untrusted input. -/
def compress (minCodeSize : Nat) (data : ByteArray) : ByteArray :=
  compressWith minCodeSize data false

end PILean.Compress.Lzw
