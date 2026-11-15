/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanTest.AnimData

/-!
# Animated-image tests on files

The readers on hand-built APNG and GIF files, rejections, mutated and truncated copies of the
writers' output (each must end in a value or an error), and the sample files for other software.
-/

namespace PILeanTest.AnimFiles

open PILean PILean.Anim PILeanTest.AnimData

/-- The `i`th frame read, or a one-pixel image. -/
def frameAt (r : Except AnimError FrameSeq) (i : Nat) : Image :=
  match r with
  | .ok s => s.frames.getD i (Image.new .rgba 1 1 ⟨1, 2, 3, 4⟩)
  | .error _ => Image.new .rgba 1 1 ⟨1, 2, 3, 4⟩

/-- Whether the pixel at `(x, y)` of frame `i` is `c`. -/
def pixelIs (r : Except AnimError FrameSeq) (i x y : Nat) (c : Rgba) : Bool :=
  (frameAt r i).getpixel x y == c

/-- The transparent colour. -/
def clear : Rgba := ⟨0, 0, 0, 0⟩

/-- The red opaque colour. -/
def red : Rgba := ⟨255, 0, 0, 255⟩

/-- The hand-built APNG with an `OVER` frame. -/
def apngOver : ByteArray :=
  buildApng 4 3 #[{ x := 0, y := 0, w := 4, h := 3, pix := solid 4 3 red },
    { x := 1, y := 1, w := 2, h := 1, pix := solid 2 1 ⟨0, 0, 255, 128⟩, blend := 1,
      num := 3, den := 4 },
    { x := 0, y := 0, w := 1, h := 1, pix := solid 1 1 clear, blend := 1, den := 0 }]

/-- The hand-built APNG with the three disposal operations (`d1`, `d2`). -/
def apngDispose (d0 d1 : UInt8) : ByteArray :=
  buildApng 4 3 #[{ x := 0, y := 0, w := 4, h := 3, pix := solid 4 3 red, dispose := d0 },
    { x := 0, y := 0, w := 2, h := 2, pix := solid 2 2 ⟨0, 255, 0, 255⟩, dispose := d1 },
    { x := 3, y := 2, w := 1, h := 1, pix := solid 1 1 ⟨0, 0, 255, 255⟩ }]

/-- Checks of the APNG reader on hand-built files. -/
def apngReaderChecks : Array (String × Bool) :=
  let o := readApng apngOver
  let bg := readApng (apngDispose 0 1)
  let prev := readApng (apngDispose 0 2)
  let first := readApng (apngDispose 2 0)
  let png := (Image.new .rgba 3 2 ⟨5, 6, 7, 255⟩).writePng.toOption.getD ByteArray.empty
  #[("apng reader: three frames, canvas size", match o with
      | .ok s => s.frames.size == 3 && s.width == 4 && s.height == 3 | .error _ => false),
    ("apng reader: SOURCE first frame", pixelIs o 0 2 2 red),
    ("apng reader: OVER of half-transparent blue on red rounds to (127, 0, 128, 255)",
      pixelIs o 1 1 1 ⟨127, 0, 128, 255⟩ && pixelIs o 1 2 1 ⟨127, 0, 128, 255⟩ &&
        pixelIs o 1 0 0 red && pixelIs o 1 3 1 red),
    ("apng reader: OVER of a transparent pixel leaves the canvas",
      pixelIs o 2 0 0 red && pixelIs o 2 1 1 ⟨127, 0, 128, 255⟩),
    ("apng reader: delays, with denominator 0 meaning 100",
      match o with
      | .ok s => s.delays == #[(1, 10), (3, 4), (1, 100)]
      | .error _ => false),
    ("apng reader: dispose BACKGROUND clears the frame's rectangle",
      pixelIs bg 1 0 0 ⟨0, 255, 0, 255⟩ && pixelIs bg 2 0 0 clear && pixelIs bg 2 1 1 clear &&
        pixelIs bg 2 2 0 red && pixelIs bg 2 3 2 ⟨0, 0, 255, 255⟩),
    ("apng reader: dispose PREVIOUS restores the canvas",
      pixelIs prev 1 0 0 ⟨0, 255, 0, 255⟩ && pixelIs prev 2 0 0 red && pixelIs prev 2 1 1 red &&
        pixelIs prev 2 3 2 ⟨0, 0, 255, 255⟩),
    ("apng reader: dispose NONE keeps the frame",
      pixelIs (readApng (apngDispose 0 0)) 2 0 0 ⟨0, 255, 0, 255⟩),
    ("apng reader: PREVIOUS on the first frame acts as BACKGROUND",
      pixelIs first 0 1 1 red && pixelIs first 1 3 2 clear && pixelIs first 1 0 0 ⟨0, 255, 0, 255⟩),
    ("apng reader: a plain PNG is one frame with loops 1",
      match readApng png with
      | .ok s => s.frames.size == 1 && s.loops == 1 && s.width == 3 &&
          (s.frames.getD 0 (Image.new .rgba 1 1)).getpixel 2 1 == ⟨5, 6, 7, 255⟩
      | .error _ => false)]

/-- Checks of the GIF reader on hand-built files. -/
def gifReaderChecks : Array (String × Bool) :=
  let grey := fun (i : Nat) => (⟨(16 * i).toUInt8, (16 * i).toUInt8, (16 * i).toUInt8, 255⟩ : Rgba)
  let rows := interlaceRows 10
  let stored := Id.run do
    let mut b := ByteArray.empty
    for j in [0:10] do
      for _ in [0:4] do b := b.push (rows.getD j 0).toUInt8
    return b
  let ilImg : GifImage := { x := 0, y := 0, w := 4, h := 10, ix := stored, interlaced := true }
  let il := readGif (buildGif 4 10 #[ilImg])
  let full := fun (i : Nat) (w h : Nat) => ByteArray.mk (Array.replicate (w * h) i.toUInt8)
  let three := fun (d : Nat) => readGif (buildGif 6 6 #[
    { x := 0, y := 0, w := 6, h := 6, ix := full 3 6 6 },
    { x := 1, y := 1, w := 2, h := 2, ix := full 9 2 2, disposal := d },
    { x := 0, y := 0, w := 1, h := 1, ix := full 12 1 1 }])
  let tr := readGif (buildGif 4 2 #[{ x := 0, y := 0, w := 4, h := 2, ix := full 3 4 2 },
    { x := 0, y := 0, w := 2, h := 1, ix := ⟨#[5, 7]⟩, transparent := some 7 }])
  #[("gif reader: interlaced rows land where they belong",
      rows == #[0, 8, 4, 2, 6, 1, 3, 5, 7, 9] &&
      (List.range 10).all fun y => pixelIs il 0 0 y (grey y) && pixelIs il 0 3 y (grey y)),
    ("gif reader: comment extension skipped, delay 10 cs, plays once",
      match il with
      | .ok s => s.delays == #[(1, 10)] && s.loops == 1 | .error _ => false),
    ("gif reader: disposal 3 restores the canvas",
      pixelIs (three 3) 1 1 1 (grey 9) && pixelIs (three 3) 2 1 1 (grey 3) &&
        pixelIs (three 3) 2 0 0 (grey 12) && pixelIs (three 3) 2 5 5 (grey 3)),
    ("gif reader: disposal 2 clears to transparent",
      pixelIs (three 2) 2 1 1 clear && pixelIs (three 2) 2 2 2 clear &&
        pixelIs (three 2) 2 3 3 (grey 3) && pixelIs (three 2) 2 0 0 (grey 12)),
    ("gif reader: disposal 1 keeps the frame", pixelIs (three 1) 2 1 1 (grey 9)),
    ("gif reader: the transparent index leaves the canvas",
      pixelIs tr 1 0 0 (grey 5) && pixelIs tr 1 1 0 (grey 3) && pixelIs tr 1 3 1 (grey 3))]

/-- A GIF header with a screen size and nothing else but the trailer. -/
def tinyGif (w h : Nat) : ByteArray := "GIF89a".toUTF8 ++ le16 w ++ le16 h ++ ⟨#[0, 0, 0, 0x3B]⟩

/-- All reader checks. -/
def readerChecks : Array (String × Bool) := apngReaderChecks ++ gifReaderChecks

/-- The caps used by the mutation tests. -/
def tight : Limits := { maxPixels := 1 <<< 20, maxFrames := 100, maxBytes := 1 <<< 24 }

/-- Rejections, each with the expected kind of failure. -/
def rejectionChecks : Array (String × Bool) :=
  let apng := (movingSquare.toApng).toOption.getD ByteArray.empty
  let gif := (movingSquare.toGif).toOption.getD ByteArray.empty
  let isTooLarge := fun (r : Except AnimError FrameSeq) =>
    match r with | .error (.tooLarge _) => true | _ => false
  #[("reject: apng with a wrong signature", !isOk (readApng (apng.extract 1 apng.size))),
    ("reject: apng truncated at every length from 0 to 120 bytes",
      (List.range 121).all fun n => !isOk (readApng (apng.extract 0 n))),
    ("reject: apng without IEND", !isOk (readApng (apng.extract 0 (apng.size - 12)))),
    ("reject: apng larger than the pixel cap", isTooLarge (readApng apng { maxPixels := 100 })),
    ("reject: apng with more frames than the cap", isTooLarge (readApng apng { maxFrames := 3 })),
    ("reject: apng larger than the byte cap", isTooLarge (readApng apng { maxBytes := 5000 })),
    ("reject: gif with a wrong signature", !isOk (readGif (gif.extract 1 gif.size))),
    ("reject: gif truncated at every length from 0 to 150 bytes",
      (List.range 151).all fun n => !isOk (readGif (gif.extract 0 n))),
    ("reject: gif without trailer", !isOk (readGif (gif.extract 0 (gif.size - 1)))),
    ("reject: gif with a 65535 x 65535 screen", isTooLarge (readGif (tinyGif 65535 65535))),
    ("reject: gif with a zero-sized screen", !isOk (readGif (tinyGif 0 4))),
    ("reject: gif without frames", !isOk (readGif (tinyGif 4 4))),
    ("reject: gif with more frames than the cap", isTooLarge (readGif gif { maxFrames := 3 })),
    ("reject: gif larger than the byte cap", isTooLarge (readGif gif { maxBytes := 5000 })),
    ("reject: gif frame outside the screen",
      !isOk (readGif (buildGif 4 4 #[{ x := 2, y := 0, w := 3, h := 1, ix := ⟨#[1, 2, 3]⟩ }]))),
    ("reject: gif with more pixels than the frame holds",
      !isOk (readGif (buildGif 4 4
        #[{ x := 0, y := 0, w := 2, h := 2, ix := ⟨#[1, 2, 3, 4, 5]⟩ }]))),
    ("reject: gif with fewer pixels than the frame holds",
      !isOk (readGif (buildGif 4 4 #[{ x := 0, y := 0, w := 2, h := 2, ix := ⟨#[1, 2, 3]⟩ }]))),
    ("reject: writers refuse an empty sequence, a size mismatch and a zero denominator",
      let s := movingSquare
      !isOk ({ s with frames := #[], delays := #[] }.toApng) &&
      !isOk ({ s with delays := s.delays.pop }.toGif) &&
      !isOk ({ s with delays := s.delays.set! 0 (1, 0) }.toApng) &&
      !isOk ({ s with width := 49 }.toGif) &&
      !isOk ({ s with width := 0 }.toApng) && !isOk ({ s with loops := 2 ^ 32 }.toApng))]

/-- `n` mutated copies of `b` (flip a byte, truncate, overwrite four bytes, insert a byte), read
by `f`; returns how many were values and how many errors. -/
def mutate (b : ByteArray) (n : Nat) (seed : UInt32) (f : ByteArray → Bool) : Nat × Nat := Id.run do
  let mut s := seed
  let mut ok := 0
  let mut bad := 0
  for _ in [0:n] do
    s := lcg s
    let op := (s >>> 24).toNat % 4
    s := lcg s
    let pos := (s >>> 8).toNat % b.size
    s := lcg s
    let v := (s >>> 16).toUInt8
    let m := match op with
      | 0 => b.set! pos (Png.byteAt b pos ^^^ (v ||| 1))
      | 1 => b.extract 0 pos
      | 2 => (((b.set! pos v).set! ((pos + 1) % b.size) (v + 1)).set! ((pos + 7) % b.size)
          (v + 2)).set! ((pos + 9) % b.size) (v + 3)
      | _ => b.extract 0 pos ++ ⟨#[v]⟩ ++ b.extract pos b.size
    if f m then ok := ok + 1 else bad := bad + 1
  return (ok, bad)

/-- The mutation checks: the number of results of each kind adds up to the number of copies. -/
def mutationChecks : Array (String × Bool) := Id.run do
  let mut r : Array (String × Bool) := #[]
  for (nm, s) in #[("moving square", movingSquare), ("transparent", transparentFrames),
      ("identical", identicalFrames)] do
    let apng := (s.toApng).toOption.getD ByteArray.empty
    let gif := (s.toGif).toOption.getD ByteArray.empty
    let (a1, a2) := mutate apng 300 5 fun m => isOk (readApng m tight)
    let (g1, g2) := mutate gif 300 9 fun m => isOk (readGif m tight)
    r := r.push (s!"mutated apng ({nm}): 300 copies end in a value or an error", a1 + a2 == 300)
    r := r.push (s!"mutated gif ({nm}): 300 copies end in a value or an error", g1 + g2 == 300)
    r := r.push (s!"mutated apng ({nm}): most are rejected", a2 > 150)
    r := r.push (s!"mutated gif ({nm}): some are rejected", g2 > 20)
  return r

/-- Writes the samples to `dir`, as `name.gif` and `name.png` (APNG). -/
def writeSamples (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  let ramp := seqOf ((Array.range 8).map fun k => gradient 64 64 |>.putpixel k k ⟨0, 0, 0, 255⟩)
    (1, 10)
  let all := sequences ++ #[("dot-60", dotSequence), ("gradient", ramp)]
  for (nm, s) in all do
    let name := nm.map fun c => if c == ' ' then '-' else c
    match s.toApng with
    | .ok b => IO.FS.writeBinFile (dir / s!"{name}.png") b
    | .error e => IO.eprintln s!"{name}: {e}"
    match s.toGif with
    | .ok b => IO.FS.writeBinFile (dir / s!"{name}.gif") b
    | .error e => IO.eprintln s!"{name}: {e}"
  match ramp.toGif (dither := true) with
  | .ok b => IO.FS.writeBinFile (dir / "gradient-dithered.gif") b
  | .error e => IO.eprintln s!"gradient-dithered: {e}"
  match (seqOf #[dotSequence.frames.getD 0 (Image.new .rgba 1 1)] (1, 1)).toApng 0 with
  | .ok b => IO.FS.writeBinFile (dir / "dot-single-stored.png") b
  | .error e => IO.eprintln s!"dot-single-stored: {e}"

end PILeanTest.AnimFiles
