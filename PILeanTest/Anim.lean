/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanTest.AnimFiles

/-!
# Animated-image tests

LZW round trips and rejections, the palette quantiser and dithering, round trips of APNG and GIF
through writer and reader on synthetic sequences, the files of the readers on hand-built input,
the saving of differencing, malformed and mutated input, determinism, and the sample files
`writeSamples` writes for other software to check.
-/

namespace PILeanTest.Anim

open PILean PILean.Anim PILeanTest.AnimData PILeanTest.AnimFiles

/-- The frames of a sequence as RGBA samples. -/
def rgbaOf (s : FrameSeq) : Array ByteArray :=
  match s.rgbaFrames with | .ok r => r | .error _ => #[]

/-- Whether two delay fractions are equal as numbers. -/
def sameDelay (a b : Nat × Nat) : Bool := a.1 * b.2 == b.1 * a.2

/-- Whether a read sequence has the frames of the input (equal neighbours merged), the delays
`ds` (as numbers) and the loop count. -/
def sameSeq (r : FrameSeq) (s : FrameSeq) (ds : Array (Nat × Nat)) (loops : Nat) : Bool :=
  let (fs, _) := mergeEqual (rgbaOf s) s.delays
  r.width == s.width && r.height == s.height && r.frames.size == fs.size &&
    (r.frames.zip fs).all (fun (a, b) => a.data == b && a.mode == .rgba) &&
    r.delays.size == ds.size && (r.delays.zip ds).all (fun (a, b) => sameDelay a b) &&
    r.loops == loops

/-- The delays of a sequence after equal neighbours are merged. -/
def mergedDelays (s : FrameSeq) : Array (Nat × Nat) := (mergeEqual (rgbaOf s) s.delays).2

/-- The delays of a sequence in centiseconds, as fractions of a second. -/
def gifExpected (s : FrameSeq) : Array (Nat × Nat) :=
  (gifDelays (mergedDelays s)).map fun c => (c, 100)

/-- The LZW checks. -/
def lzwChecks : Array (String × Bool) := Id.run do
  let mut r : Array (String × Bool) := #[]
  for m in [2:9] do
    let gens : Array (String × (Nat → ByteArray)) :=
      #[("noise", fun n => noiseIndices 7 n m), ("runs", fun n => runIndices 3 n m),
        ("one colour", fun n => ByteArray.mk (Array.replicate n 1))]
    for (nm, g) in gens do
      let mut ok := true
      for n in [0, 1, 2, 3, 5, 100, 4095, 4096, 4097, 20000] do
        let x := g n
        ok := ok && (match Lzw.decode m (Lzw.encode m x) n with
          | .ok y => y == x | .error _ => false)
      r := r.push (s!"lzw: round trips, min code size {m}, {nm}", ok)
    let big := noiseIndices 11 120000 m
    r := r.push (s!"lzw: 120000 symbols force table resets, min code size {m}",
      match Lzw.decode m (Lzw.encode m big) 120000 with | .ok y => y == big | .error _ => false)
    let bigRuns := runIndices 12 150000 m
    r := r.push (s!"lzw: 150000 symbols with runs, min code size {m}",
      match Lzw.decode m (Lzw.encode m bigRuns) 150000 with
      | .ok y => y == bigRuns | .error _ => false)
  let enc := Lzw.encode 2 ⟨#[0, 1, 2, 3, 0, 1, 2, 3, 0, 1]⟩
  r := r.push ("lzw: encoder is deterministic",
    enc == Lzw.encode 2 ⟨#[0, 1, 2, 3, 0, 1, 2, 3, 0, 1]⟩)
  r := r.push ("lzw: starts with a clear code, 3 bits, and ends with the end code",
    Png.byteAt enc 0 &&& 7 == 4)
  r := r.push ("lzw: stream shorter than the pixels count is rejected",
    !isOk (Lzw.decode 2 enc 11))
  r := r.push ("lzw: more pixels than expected are rejected", !isOk (Lzw.decode 2 enc 9))
  r := r.push ("lzw: wrong minimum code size is rejected",
    !isOk (Lzw.decode 1 enc 10) && !isOk (Lzw.decode 9 enc 10))
  let craft := fun (codes : List (Nat × Nat)) =>
    (codes.foldl (fun (s : Lzw.BitSink) (c, n) => s.put c n) {}).finish
  r := r.push ("lzw: stream without a clear code is rejected",
    !isOk (Lzw.decode 2 (craft [(1, 3), (2, 3), (5, 3)]) 2))
  r := r.push ("lzw: code beyond the next free entry is rejected",
    !isOk (Lzw.decode 2 (craft [(4, 3), (1, 3), (7, 3), (5, 3)]) 3))
  r := r.push ("lzw: first code after clear must be a literal",
    !isOk (Lzw.decode 2 (craft [(4, 3), (6, 3), (5, 3)]) 1))
  r := r.push ("lzw: end code ends the stream",
    match Lzw.decode 2 (craft [(4, 3), (1, 3), (5, 3)]) 1 with
    | .ok y => y == ⟨#[1]⟩ | .error _ => false)
  r := r.push ("lzw: missing end code is fine once the pixels are complete",
    match Lzw.decode 2 (craft [(4, 3), (2, 3)]) 1 with | .ok y => y == ⟨#[2]⟩ | .error _ => false)
  r := r.push ("lzw: truncated stream is rejected", !isOk (Lzw.decode 2 (craft [(4, 3)]) 5))
  let mut blocksOk := true
  for n in [0, 1, 254, 255, 256, 509, 510, 1000] do
    let d := noiseIndices 5 n 8
    blocksOk := blocksOk && (match Lzw.unpackBlocks (Lzw.packBlocks d) 0 with
      | .ok (o, p) => o == d && p == (Lzw.packBlocks d).size | .error _ => false)
  r := r.push ("lzw: data sub-blocks round trip", blocksOk)
  r := r.push ("lzw: sub-blocks have at most 255 bytes and end with 0",
    let p := Lzw.packBlocks (noiseIndices 5 600 8)
    Png.byteAt p 0 == 255 && Png.byteAt p 256 == 255 && Png.byteAt p 512 == 90 &&
      p.size == 600 + 3 + 1)
  r := r.push ("lzw: unterminated sub-blocks are rejected",
    !isOk (Lzw.unpackBlocks ⟨#[3, 1, 2]⟩ 0) && !isOk (Lzw.unpackBlocks ⟨#[1, 1]⟩ 0))
  return r

/-- The mean squared RGB error of an indexed frame against the original. -/
def meanError (p : Quant.Palette) (f ix : ByteArray) : Nat := Id.run do
  let mut e := 0
  for i in [0:f.size / 4] do
    let c := p.colors.getD (Png.byteAt ix i).toNat 0
    e := e + Quant.dist2 c (Png.byteAt f (4 * i)).toNat (Png.byteAt f (4 * i + 1)).toNat
      (Png.byteAt f (4 * i + 2)).toNat
  return e / (f.size / 4)

/-- The quantiser and dithering checks. -/
def quantChecks : Array (String × Bool) :=
  let few := (square 8 8 2 2 3 white ⟨200, 0, 0, 255⟩).data
  let pf := Quant.quantize #[few]
  let g := (gradient 32 32).data
  let pg := Quant.quantize #[g]
  let (ixg, _) := Quant.indexFrame pg {} g 32 32 false
  let (ixd, _) := Quant.indexFrame pg {} g 32 32 true
  let (ixd2, _) := Quant.indexFrame pg {} g 32 32 true
  let big := (gradient 64 64).data
  let pbig := Quant.quantize #[big]
  let (ixb, _) := Quant.indexFrame pbig {} big 64 64 false
  let (ixbd, _) := Quant.indexFrame pbig {} big 64 64 true
  let (ixf, _) := Quant.indexFrame pf {} few 8 8 true
  let (ixf0, _) := Quant.indexFrame pf {} few 8 8 false
  let withAlpha := (Image.new .rgba 4 4 ⟨0, 0, 0, 0⟩).data ++ few
  let pa := Quant.quantize #[withAlpha]
  let g2 := (gradient 40 40).data
  let pg2 := Quant.quantize #[g2, g]
  #[("quantiser: 2 colours give an exact palette of 2 entries",
      pf.exact && pf.colors.size == 2 && !pf.hasTransparent),
    ("quantiser: exact palette maps every pixel to its own colour",
      (List.range 64).all fun i => pf.colors.getD (Png.byteAt ixf0 i).toNat 0 ==
        Quant.pack (Png.byteAt few (4 * i)).toNat (Png.byteAt few (4 * i + 1)).toNat
          (Png.byteAt few (4 * i + 2)).toNat),
    ("quantiser: dithering an exact palette changes nothing", ixf == ixf0),
    ("quantiser: a transparent pixel adds an entry", pa.hasTransparent && pa.size == 3),
    ("quantiser: transparent pixels get the index after the colours",
      (Quant.indexFrame pa {} withAlpha 8 4 false).1.data.toList.take 16 ==
        List.replicate 16 2),
    ("quantiser: a gradient of 1024 colours is cut to at most 256 entries",
      !pg.exact && pg.colors.size ≤ 256 && pg.colors.size > 200),
    ("quantiser: gradient error is bounded (mean squared error below 100)",
      meanError pg g ixg < 100),
    ("quantiser: with transparency the cap is 255 colours",
      (Quant.quantize #[g, (Image.new .rgba 1 1 ⟨0, 0, 0, 0⟩).data]).colors.size ≤ 255),
    ("quantiser: palette of two frames together covers both",
      !pg2.exact && pg2.colors.size ≤ 256),
    ("quantiser: deterministic", (Quant.quantize #[g]).colors == pg.colors &&
      (Quant.quantize #[g2, g]).colors == pg2.colors),
    ("dither: deterministic", ixd == ixd2),
    ("dither: differs from plain mapping on a 4096-colour gradient", ixbd != ixb),
    ("dither: indices stay inside the palette", ixd.data.all (·.toNat < pg.colors.size)),
    ("dither: average colour is closer than plain mapping's",
      let avg := fun (ix : ByteArray) (k : Nat) => (List.range 1024).foldl (fun a i =>
        a + Quant.chan (pg.colors.getD (Png.byteAt ix i).toNat 0) k) 0
      let orig := fun (k : Nat) => (List.range 1024).foldl (fun a i =>
        a + (Png.byteAt g (4 * i + k)).toNat) 0
      let d := fun (ix : ByteArray) => (List.range 3).foldl (fun a k =>
        a + Int.natAbs ((avg ix k : Int) - orig k)) 0
      d ixd ≤ d ixg),
    ("dither: mean error stays bounded on a 4096-colour gradient",
      meanError pbig big ixbd < 400),
    ("fitFrac: fractions that fit are reduced", fitFrac 10 100 == (1, 10)),
    ("fitFrac: large fractions are approximated within 16 bits",
      let (a, b) := fitFrac 123456 7
      a ≤ 65535 && b ≤ 65535 && sameDelay (a, b) (35273, 2)),
    ("fitFrac: tiny and huge values clamp", fitFrac 1 100000 == (1, 65535) &&
      fitFrac 10000000 3 == (65535, 1)),
    ("fitFrac: a close fraction is found", fitFrac 1234567 7654321 == (5, 31)),
    ("delays: one third of a second keeps the total exact",
      gifDelays #[(1, 3), (1, 3), (1, 3)] == #[33, 34, 33]),
    ("delays: at least 2 centiseconds, at most 65535",
      gifDelays #[(0, 1), (1, 1000), (100000, 1)] == #[2, 2, 65535]),
    ("delays: exact tenths", gifDelays #[(1, 10), (1, 10)] == #[10, 10])]

/-- Round trips of every synthetic sequence through both codecs. -/
def roundTripChecks : Array (String × Bool) := Id.run do
  let mut r : Array (String × Bool) := #[]
  for (nm, s) in sequences do
    let ds := mergedDelays s
    r := r.push (s!"apng: {nm} round trips exactly",
      match s.toApng with
      | .ok b => match readApng b with
        | .ok x => sameSeq x s ds s.loops
        | .error _ => false
      | .error _ => false)
    r := r.push (s!"gif: {nm} round trips exactly",
      match s.toGif with
      | .ok b => match readGif b with
        | .ok x => sameSeq x s (gifExpected s) (if s.loops == 0 then 0 else s.loops)
        | .error _ => false
      | .error _ => false)
    r := r.push (s!"apng and gif: {nm} encode deterministically",
      s.toApng.toOption == s.toApng.toOption && s.toGif.toOption == s.toGif.toOption)
  return r

/-- The names of the chunks of a PNG file, and whether every `fcTL` and `fdAT` has the next
sequence number. -/
def chunkTypes (b : ByteArray) : Array String × Bool := Id.run do
  let mut pos := 8
  let mut tys := #[]
  let mut seq := 0
  let mut ok := true
  for _ in [0:b.size / 12 + 1] do
    if pos + 12 > b.size then break
    let len := Png.getBe32 b pos
    let ty := Png.latin1String (b.extract (pos + 4) (pos + 8))
    if ty == "fcTL" || ty == "fdAT" then
      ok := ok && Png.getBe32 b (pos + 8) == seq
      seq := seq + 1
    tys := tys.push ty
    pos := pos + 12 + len
  return (tys, ok)

/-- The size of the dot sequence as full frames in an APNG: every frame's compressed image data
and a control chunk each, plus the header chunks. -/
def apngFullSize : Nat :=
  (rgbaOf dotSequence).foldl (fun a f => a + (Png.zlibCompress (Png.filterImage
    { width := 160, height := 120, mode := .rgba, data := f } none) 6).size + 12 + 38 + 16) 100

/-- The size of the dot sequence as full frames in a GIF: every frame's LZW stream and the
descriptors, plus the header and the colour table. -/
def gifFullSize : Nat :=
  let rgba := rgbaOf dotSequence
  let pal := Quant.quantize rgba
  let m := max 2 (tableBits (pal.colors.size + 1))
  rgba.foldl (fun a f =>
    let n := (Lzw.encode m (Quant.indexFrame pal {} f 160 120 false).1).size
    a + n + n / 255 + 30) (800 + 13)

/-- Checks of the APNG structure and of the saving by differencing. -/
def structureChecks : Array (String × Bool) :=
  let apng := (movingSquare.toApng).toOption.getD ByteArray.empty
  let (tys, seqOk) := chunkTypes apng
  let dot := (dotSequence.toApng).toOption.getD ByteArray.empty
  let gdot := (dotSequence.toGif).toOption.getD ByteArray.empty
  #[("apng: chunk order IHDR sRGB gAMA acTL fcTL IDAT fcTL fdAT … IEND",
      tys.toList.take 7 == ["IHDR", "sRGB", "gAMA", "acTL", "fcTL", "IDAT", "fcTL"] &&
      tys.getD 7 "" == "fdAT" && tys.getD (tys.size - 1) "" == "IEND"),
    ("apng: sequence numbers of fcTL and fdAT count up from 0", seqOk),
    ("apng: the PNG reader sees the first frame as the default image",
      match Png.decode apng with
      | .ok d => d.image.data == (rgbaOf movingSquare).getD 0 ByteArray.empty
      | .error _ => false),
    ("apng: 60 dot frames are at least 5 times smaller than the same frames in full",
      dot.size * 5 < apngFullSize),
    ("gif: 60 dot frames are at least 8 times smaller than the same frames in full",
      gdot.size * 8 < gifFullSize),
    ("apng: identical neighbours are merged (3 frames from 5)",
      (chunkTypes ((identicalFrames.toApng).toOption.getD ByteArray.empty)).1.count "fcTL" == 3),
    ("gif: starts with GIF89a and ends with the trailer",
      let g := (movingSquare.toGif).toOption.getD ByteArray.empty
      g.extract 0 6 == "GIF89a".toUTF8 && Png.byteAt g (g.size - 1) == 0x3B)]

/-- All pure checks. -/
def checks : Array (String × Bool) :=
  lzwChecks ++ quantChecks ++ roundTripChecks ++ structureChecks ++ readerChecks ++
    rejectionChecks ++ mutationChecks

/-- The checks that print: the sizes of the sample files with and without differencing. -/
def ioChecks : IO (Array (String × Bool)) := do
  let dot := (dotSequence.toApng).toOption.getD ByteArray.empty
  let gdot := (dotSequence.toGif).toOption.getD ByteArray.empty
  IO.println s!"anim sizes: 60-frame dot, APNG {dot.size} bytes (every frame in full: \
    {apngFullSize}), GIF {gdot.size} bytes (every frame in full: {gifFullSize})"
  return #[("anim: sample sizes were reported", dot.size > 0 && gdot.size > 0)]

end PILeanTest.Anim
