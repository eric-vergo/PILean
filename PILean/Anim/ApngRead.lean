/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Anim.Compose

/-!
# The APNG reader

`Anim.readApng` reads an animated PNG (or a plain PNG, as a sequence of one frame) and composes
every frame onto the canvas.

## Main definitions

* `Anim.readApng`: the composed frames, their delays and the loop count.

## Implementation notes

* The input is untrusted. Every chunk length, CRC, sequence number and frame rectangle is checked;
  the canvas must be at most `Limits.maxPixels` pixels, the number of frames at most
  `Limits.maxFrames` and the composed frames together at most `Limits.maxBytes` bytes. Every
  loop is bounded by the input size. Failure is an `AnimError`, never a panic.
* Each frame's compressed data is wrapped into a stand-alone PNG (with the file's `PLTE` and
  `tRNS`) and decoded by `Png.decode`, so every colour type and bit depth, interlacing and the
  inflate bounds of the PNG reader apply to frames too.
* If `IDAT` is not preceded by an `fcTL`, it is the default image and not a frame.
* The first frame must cover the canvas; a `dispose_op` of `PREVIOUS` on it acts as
  `BACKGROUND`. A denominator of 0 means 100. The number of frames must equal the one in `acTL`.
* Frames are composed by `Anim.Composer.add`, which implements `dispose_op` and `blend_op`.

## References

* Animated Portable Network Graphics (APNG) Specification, MDN / Mozilla; PNG Specification,
  Third Edition (W3C). Written from the specifications.
-/

namespace PILean.Anim

/-- The PNG reader's caps that correspond to these limits. -/
def Limits.toPng (lim : Limits) : Png.Limits :=
  { maxPixels := lim.maxPixels, maxBytes := lim.maxBytes }

/-- The reader's state. -/
structure ReadState where
  /-- The validated header. -/
  hdr : Option Png.Header := none
  /-- The bytes of the `IHDR` data. -/
  ihdr : ByteArray := ByteArray.empty
  /-- The `PLTE` and `tRNS` chunks as in the file. -/
  extra : ByteArray := ByteArray.empty
  /-- The frame count and play count of `acTL`. -/
  actl : Option (Nat × Nat) := none
  /-- The next expected sequence number. -/
  seq : Nat := 0
  /-- The control data of the frame being collected. -/
  pending : Option FrameCtl := none
  /-- The concatenated `IDAT` or `fdAT` payloads of that frame. -/
  pdata : ByteArray := ByteArray.empty
  /-- Whether `IDAT` is before (0), in (1) or after (2) its run of chunks. -/
  idat : Nat := 0
  /-- The composed frames. -/
  comp : Composer := { w := 0, h := 0, canvas := ByteArray.empty }

/-- The RGBA samples of a frame: its compressed data in a stand-alone PNG, decoded. -/
def decodeFrame (st : ReadState) (ctl : FrameCtl) (data : ByteArray) (lim : Limits) :
    Except AnimError ByteArray := do
  let hd := Png.be32 ctl.rect.w.toUInt32 ++ Png.be32 ctl.rect.h.toUInt32 ++
    st.ihdr.extract 8 13
  let png := Png.pngSignature ++ Png.chunk "IHDR" hd ++ st.extra ++ Png.chunk "IDAT" data ++
    Png.chunk "IEND" ByteArray.empty
  match Png.decode png lim.toPng with
  | .error (.tooLarge m) => throw (.tooLarge m)
  | .error e => throw (.malformed s!"frame data: {e}")
  | .ok d =>
    let im : Image := Image.ofRaw d.image
    match im.toRgbaData with
    | some p =>
      if im.width != ctl.rect.w || im.height != ctl.rect.h then
        throw (.malformed "frame size differs from its header")
      return p
    | none => throw (.malformed "frame samples")

/-- Composes the pending frame, if any. -/
def flush (st : ReadState) (lim : Limits) : Except AnimError ReadState := do
  let some ctl := st.pending | return st
  let pix ← decodeFrame st ctl st.pdata lim
  return { st with pending := none, pdata := ByteArray.empty, comp := st.comp.add ctl pix }

/-- Reads the chunk at `pos`. -/
def readChunk (st : ReadState) (lim : Limits) (bytes : ByteArray) (pos : Nat) :
    Except AnimError (ReadState × Nat × Bool) := do
  let len := Png.getBe32 bytes pos
  if len > 0x7FFFFFFF then throw (.malformed "chunk length exceeds 2^31 - 1")
  if pos + 12 + len > bytes.size then throw .truncated
  let tyBytes := bytes.extract (pos + 4) (pos + 8)
  let data := bytes.extract (pos + 8) (pos + 8 + len)
  if !(tyBytes.data.all fun b => (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122)) then
    throw (.malformed "chunk type is not four letters")
  let ty := Png.latin1String tyBytes
  let crc := Png.crcUpdate (Png.crcUpdate 0xFFFFFFFF tyBytes) data ^^^ 0xFFFFFFFF
  if crc.toNat != Png.getBe32 bytes (pos + 8 + len) then throw (.malformed s!"CRC of {ty}")
  let next := pos + 12 + len
  let mut st := st
  if st.hdr.isNone && ty != "IHDR" then throw (.malformed "IHDR is not the first chunk")
  if ty != "IDAT" && st.idat == 1 then st := { st with idat := 2 }
  let some h := st.hdr | do
    let hdr ← match Png.parseHeader data lim.toPng with
      | .ok h => pure h
      | .error (.tooLarge m) => throw (.tooLarge m)
      | .error e => throw (.malformed s!"{e}")
    let blank := ByteArray.mk (Array.replicate (hdr.width * hdr.height * 4) 0)
    return ({ st with
      hdr := some hdr
      ihdr := data
      comp := { w := hdr.width, h := hdr.height, canvas := blank } }, next, false)
  match ty with
  | "IHDR" => throw (.malformed "repeated IHDR")
  | "PLTE" | "tRNS" =>
    if st.idat != 0 then throw (.malformed s!"{ty} after IDAT")
    st := { st with extra := st.extra ++ bytes.extract pos next }
  | "acTL" =>
    if st.actl.isSome || st.idat != 0 || len != 8 then throw (.malformed "invalid acTL")
    let n := Png.getBe32 data 0
    if n == 0 || n > lim.maxFrames then throw (.tooLarge "number of frames")
    st := { st with actl := some (n, Png.getBe32 data 4) }
  | "fcTL" =>
    let some (n, _) := st.actl | throw (.malformed "fcTL before acTL")
    st ← flush st lim
    if len != 26 || Png.getBe32 data 0 != st.seq then throw (.malformed "invalid fcTL")
    let r : Rect := {
      x := Png.getBe32 data 12
      y := Png.getBe32 data 16
      w := Png.getBe32 data 4
      h := Png.getBe32 data 8 }
    if r.w == 0 || r.h == 0 || r.x + r.w > h.width || r.y + r.h > h.height then
      throw (.malformed "frame rectangle outside the canvas")
    if st.comp.frames.isEmpty && (r.x != 0 || r.y != 0 || r.w != h.width || r.h != h.height) then
      throw (.malformed "first frame does not cover the canvas")
    let dispose := (Png.byteAt data 24).toNat
    let blend := (Png.byteAt data 25).toNat
    if dispose > 2 || blend > 1 then throw (.malformed "invalid dispose_op or blend_op")
    if st.comp.frames.size + 1 > n then throw (.malformed "more frames than acTL states")
    if (st.comp.frames.size + 1) * (h.width * h.height * 4) > lim.maxBytes then
      throw (.tooLarge "composed frames")
    let num := (Png.byteAt data 20).toNat * 256 + (Png.byteAt data 21).toNat
    let den := (Png.byteAt data 22).toNat * 256 + (Png.byteAt data 23).toNat
    let ctl : FrameCtl := { rect := r, num, den, dispose, blend }
    st := { st with seq := st.seq + 1, pending := some ctl }
  | "IDAT" =>
    if st.idat == 2 then throw (.malformed "IDAT chunks are not consecutive")
    st := { st with idat := 1 }
    if st.actl.isNone && st.pending.isNone then
      let full : Rect := { x := 0, y := 0, w := h.width, h := h.height }
      let ctl : FrameCtl := { rect := full, num := 0, den := 1, dispose := 0, blend := 0 }
      st := { st with pending := some ctl }
    if st.pending.isSome then st := { st with pdata := st.pdata ++ data }
  | "fdAT" =>
    if st.pending.isNone then throw (.malformed "fdAT without fcTL")
    if len < 4 || Png.getBe32 data 0 != st.seq then throw (.malformed "invalid fdAT")
    st := { st with seq := st.seq + 1, pdata := st.pdata ++ data.extract 4 data.size }
  | "IEND" =>
    if len != 0 then throw (.malformed "IEND is not empty")
    return (← flush st lim, next, true)
  | _ =>
    if (Png.byteAt tyBytes 0) &&& 32 == 0 then throw (.malformed s!"unknown critical chunk {ty}")
  return (st, next, false)

/-- Reads an APNG (or PNG) file and composes its frames. The delays are in lowest terms; `loops`
is the play count of `acTL` (0 forever), 1 for a plain PNG. Fails with an `AnimError` if the
file is malformed, truncated or larger than `lim` allows. -/
def readApng (bytes : ByteArray) (lim : Limits := {}) : Except AnimError FrameSeq := do
  if bytes.size < 8 || bytes.extract 0 8 != Png.pngSignature then
    throw (.malformed "not a PNG file")
  let mut st : ReadState := {}
  let mut pos := 8
  let mut done := false
  for _ in [0:bytes.size / 12 + 1] do
    if pos + 12 > bytes.size then throw .truncated
    let (st', pos', fin) ← readChunk st lim bytes pos
    st := st'
    pos := pos'
    if fin then
      done := true
      break
  if !done then throw .truncated
  let c := st.comp
  if let some (n, _) := st.actl then
    if n != c.frames.size then throw (.malformed "number of frames differs from acTL")
  if c.frames.isEmpty then throw (.malformed "no frames")
  return { width := c.w, height := c.h, frames := c.frames, delays := c.delays
           loops := (st.actl.map (·.2)).getD 1 }

end PILean.Anim
