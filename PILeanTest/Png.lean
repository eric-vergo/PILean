/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean

/-!
# PNG tests

Known answers, round trips of the writer and the reader and of the compressor and the
decompressor, mutation tests on valid streams (every result must be a value, never a crash or a
hang), the size cap, the reader on the committed fixtures `PILeanTest/png/` (written by
`tools/png-check.py`), and a timing of a plot-sized image. `writeScratch` writes the writer's
output to a directory for `tools/png-check.py` to check with other software.
-/

namespace PILeanTest.Png

open PILean.Png

/-- One step of a linear congruential generator, the source of all test data. -/
def lcg (s : UInt32) : UInt32 := s * 1664525 + 1013904223

/-- `n` pseudo-random bytes from `seed`. -/
def noiseBytes (seed : UInt32) (n : Nat) : ByteArray := Id.run do
  let mut s := seed
  let mut b := ByteArray.empty
  for _ in [0:n] do
    s := lcg s
    b := b.push (s >>> 24).toUInt8
  return b

/-- Pseudo-random words joined into text of at least `n` bytes. -/
def textBytes (n : Nat) : ByteArray := Id.run do
  let words := #["the ", "quick ", "brown ", "fox ", "jumps ", "over ", "lazy ", "dog. "]
  let mut s : UInt32 := 7
  let mut b := ByteArray.empty
  for _ in [0:n] do
    if b.size ≥ n then break
    s := lcg s
    b := b ++ (words.getD ((s >>> 20).toNat % 8) "").toUTF8
  return b

/-- A noise image. -/
def noiseImage (w h : Nat) (mode : Mode) (seed : UInt32) : RawImage :=
  { width := w, height := h, mode, data := noiseBytes seed (w * h * mode.channels) }

/-- A smooth image (gradients), where the filters matter. -/
def gradientImage (w h : Nat) (mode : Mode) : RawImage :=
  let c := mode.channels
  { width := w, height := h, mode, data := Id.run do
      let mut b := ByteArray.empty
      for y in [0:h] do
        for x in [0:w] do
          for k in [0:c] do
            b := b.push ((x * (3 + k) + y * (2 + k)) % 256).toUInt8
      return b }

/-- An RGBA image that resembles a plot: white, a grid, axes and a jagged line. -/
def plotImage (w h : Nat) : RawImage :=
  { width := w, height := h, mode := .rgba, data := Id.run do
      let mut b := ByteArray.empty
      for y in [0:h] do
        for x in [0:w] do
          let fy := h / 2 + (x * 37) % 200 - 100
          let line := y + 1 ≥ fy && y ≤ fy + 1
          let axis := x == 50 || y + 50 == h
          let grid := x % 100 == 0 || y % 100 == 0
          if line then b := ((b.push 20).push 90).push 200 |>.push 255
          else if axis then b := ((b.push 0).push 0).push 0 |>.push 255
          else if grid then b := ((b.push 210).push 210).push 210 |>.push 255
          else b := ((b.push 255).push 255).push 255 |>.push 255
      return b }

/-- Whether two raw images are equal. -/
def sameImage (a b : RawImage) : Bool :=
  a.width == b.width && a.height == b.height && a.mode == b.mode && a.data == b.data

/-- A result is "settled" when it is a value; forcing it is what the mutation tests check. -/
def settled {α ε : Type} (r : Except ε α) : Bool := match r with | .ok _ => true | .error _ => true

/-- Whether decoding succeeded. -/
def isOk {α ε : Type} (r : Except ε α) : Bool := match r with | .ok _ => true | .error _ => false

/-- Whether a PNG decode failed with exactly the error `e`. -/
def failsWith (r : Except PngError Decoded) (e : PngError) : Bool :=
  match r with | .error e' => e' == e | .ok _ => false

/-- Whether a zlib decode failed with exactly the error `e`. -/
def zfails (r : Except InflateError ByteArray) (e : InflateError) : Bool :=
  match r with | .error e' => e' == e | .ok _ => false

/-- Whether a zlib decode succeeded with exactly `d`. -/
def zeq (r : Except InflateError ByteArray) (d : ByteArray) : Bool :=
  match r with | .ok o => o == d | .error _ => false

/-- The round trip of the compressor and the decompressor on `d` at `level`. -/
def zRoundTrip (d : ByteArray) (level : Nat) : Bool :=
  match zlibDecompress (zlibCompress d level) (d.size + 10) with
  | .ok o => o == d
  | .error _ => false

/-- The inputs of the compressor tests. -/
def zInputs : Array (String × ByteArray) :=
  let x := noiseBytes 5 300
  let big := noiseBytes 9 32768
  #[("empty", ByteArray.empty), ("one byte", ⟨#[42]⟩), ("two bytes", ⟨#[1, 1]⟩),
    ("zeros 100 KiB", ByteArray.mk (Array.replicate 102400 0)),
    ("text", textBytes 40000), ("noise", noiseBytes 1 20000),
    ("max match 258", ByteArray.mk (Array.replicate 1000 7)),
    ("distance 32768", x ++ noiseBytes 6 (32768 - 300) ++ x ++ noiseBytes 7 50),
    ("long repeat of a 32 KiB block", big ++ big ++ big),
    ("mixed", textBytes 20000 ++ noiseBytes 3 3000 ++ textBytes 20000),
    ("stored boundary", noiseBytes 4 65535 ++ noiseBytes 4 65536 ++ ⟨#[1, 2, 3]⟩)]

/-- The checks of the checksums. -/
def checksums : Array (String × Bool) :=
  let nine := "123456789".toUTF8
  #[("crc32: 123456789", crc32 nine == 0xCBF43926),
    ("crc32: empty", crc32 ByteArray.empty == 0),
    ("crc32Bits: 123456789", crc32Bits nine == 0xCBF43926),
    ("crc32: table equals bitwise on text and noise",
      crc32 (textBytes 5000) == crc32Bits (textBytes 5000) &&
      crc32 (noiseBytes 3 5000) == crc32Bits (noiseBytes 3 5000)),
    ("adler32: Wikipedia", adler32 "Wikipedia".toUTF8 == 0x11E60398),
    ("adler32: empty", adler32 ByteArray.empty == 1),
    ("adler32: long runs of 255 stay reduced",
      adler32 (ByteArray.mk (Array.replicate 100000 255)) ==
        (let r := (List.range 100000).foldl (fun (s : Nat × Nat) _ =>
          let a := (s.1 + 255) % 65521; (a, (s.2 + a) % 65521)) (1, 0)
         (r.2.toUInt32 <<< 16) + r.1.toUInt32))]

/-- The checks of the compressor and the decompressor. -/
def zlibChecks : Array (String × Bool) := Id.run do
  let mut r : Array (String × Bool) := #[]
  for (nm, d) in zInputs do
    for lv in [0, 1, 6, 9] do
      r := r.push (s!"zlib round trip: {nm}, level {lv}", zRoundTrip d lv)
    r := r.push (s!"zlib deterministic: {nm}", zlibCompress d 6 == zlibCompress d 6)
  let hello : ByteArray := ⟨#[0x78, 0x9c, 0xcb, 0x48, 0xcd, 0xc9, 0xc9, 0x07, 0x00, 0x06, 0x2c,
    0x02, 0x15]⟩
  let cap := 1000
  let z := zlibCompress (ByteArray.mk (Array.replicate 100000 0)) 6
  let good := zlibCompress (textBytes 2000) 6
  r := r ++ #[
    ("inflate: a stream from another encoder", zeq (zlibDecompress hello 100) "hello".toUTF8),
    ("inflate: empty stream", zeq (zlibDecompress ⟨#[0x78, 0x9c, 3, 0, 0, 0, 0, 1]⟩ 10)
      ByteArray.empty),
    ("inflate: output cap", zfails (zlibDecompress z cap) .outputTooLarge),
    ("inflate: cap equal to the size passes",
      isOk (zlibDecompress z 100000) && zfails (zlibDecompress z 99999) .outputTooLarge),
    ("inflate: bad header", zfails (zlibDecompress ⟨#[0x78, 0x9d, 3, 0, 0, 0, 0, 1]⟩ 10)
      .badZlibHeader),
    ("inflate: preset dictionary", zfails (zlibDecompress ⟨#[0x78, 0xbb, 3, 0, 0, 0, 0, 1]⟩ 10)
      .presetDictionary),
    ("inflate: bad checksum", zfails (zlibDecompress ⟨#[0x78, 0x9c, 3, 0, 0, 0, 0, 2]⟩ 10)
      .badChecksum),
    ("inflate: trailing data", zfails (zlibDecompress (good.push 0) 100000) .trailingData),
    ("inflate: trailing data allowed on request",
      isOk (zlibDecompress (good.push 0) 100000 (allowTrailing := true))),
    ("inflate: truncated", zfails (zlibDecompress (good.extract 0 20) 100000) .truncated),
    ("inflate: reserved block type", zfails (zlibDecompress ⟨#[0x78, 0x9c, 7, 0, 0, 0, 0, 1]⟩ 10)
      .badBlockType),
    ("inflate: stored length check", zfails (zlibDecompress
      ⟨#[0x78, 0x9c, 1, 1, 0, 0, 0, 65, 0, 0, 0, 0]⟩ 10) .badStoredLength),
    ("inflate: distance before the start", zfails (zlibDecompress
      -- fixed block: match of length 3 at distance 1 with an empty window
      ⟨#[0x78, 0x9c, 0x03, 0x02, 0, 0, 0, 0, 0]⟩ 10) .badDistance),
    ("huffman: over-subscribed", (Huff.build #[1, 1, 1]) matches .error .oversubscribedCode),
    ("huffman: incomplete", (Huff.build #[2, 2]) matches .error .incompleteCode),
    ("huffman: a single code of length 1", isOk (Huff.build #[0, 1, 0])),
    ("huffman: a single code of length 2 is incomplete",
      (Huff.build #[0, 2, 0]) matches .error .incompleteCode),
    ("huffman: no codes", isOk (Huff.build #[0, 0, 0])),
    ("huffman: canonical codes of the RFC example",
      canonicalCodes #[3, 3, 3, 3, 3, 2, 4, 4] ==
        #[reverseBits 2 3, reverseBits 3 3, reverseBits 4 3, reverseBits 5 3, reverseBits 6 3,
          reverseBits 0 2, reverseBits 14 4, reverseBits 15 4]),
    ("huffman: length limit holds for skewed frequencies",
      (huffLengths (Array.ofFn (n := 40) fun i => 2 ^ i.val) 15).all (· ≤ 15) &&
      (huffLengths (Array.ofFn (n := 19) fun i => 3 ^ i.val) 7).all (· ≤ 7))]
  return r

/-- Bytes with every chunk's CRC recomputed (chunks that run past the end are left alone). -/
def fixCrcs (b : ByteArray) : ByteArray := Id.run do
  let mut out := b
  let mut pos := 8
  for _ in [0:b.size / 12 + 1] do
    let len := getBe32 b pos
    if pos + 12 + len > b.size then break
    let body := b.extract (pos + 4) (pos + 8 + len)
    let c := be32 (crc32 body)
    out := out.extract 0 (pos + 8 + len) ++ c ++ out.extract (pos + 12 + len) out.size
    pos := pos + 12 + len
  return out

/-- Variations of a byte string: every bit flipped, every byte set to a few values, every byte
deleted, a byte inserted at every position, and every proper prefix. -/
def mutations (b : ByteArray) : Array ByteArray := Id.run do
  let mut r : Array ByteArray := #[]
  for i in [0:b.size] do
    for k in [0:8] do
      r := r.push (b.set! i (b.get! i ^^^ (1 <<< k).toUInt8))
    for v in [0, 1, 0x7F, 0x80, 0xFF] do
      r := r.push (b.set! i v.toUInt8)
    r := r.push (b.extract 0 i ++ b.extract (i + 1) b.size)
    r := r.push (b.extract 0 i ++ ⟨#[0xFF]⟩ ++ b.extract i b.size)
    r := r.push (b.extract 0 i)
  return r

/-- The sample PNG of the mutation tests: small, with every kind of chunk. -/
def samplePng (mode : Mode) (level : Nat) : ByteArray :=
  let md : Metadata := { text := #[{ keyword := "Title", text := "A test" },
    { keyword := "Comment", text := "ünï", international := true, language := "de" }] }
  match encode (noiseImage 5 4 mode 11) md level with
  | .ok b => b
  | .error _ => ByteArray.empty

/-- The checks of the PNG writer and reader. -/
def pngChecks : Array (String × Bool) := Id.run do
  let mut r : Array (String × Bool) := #[]
  let sizes := #[(1, 1), (3, 5), (255, 17), (7, 9), (64, 2), (2, 64)]
  for mode in [Mode.l, .rgb, .rgba] do
    for (w, h) in sizes do
      for (nm, img) in #[("noise", noiseImage w h mode 3), ("gradient", gradientImage w h mode)] do
        let ok := match encode img with
          | .ok b => match decode b with
            | .ok d => sameImage d.image img && d.srgbIntent == some 0 && d.gamma == some 45455
            | .error _ => false
          | .error _ => false
        r := r.push (s!"png round trip: {repr mode} {nm} {w}x{h}", ok)
  let img := gradientImage 50 40 .rgb
  for t in [0, 1, 2, 3, 4] do
    let ok := match encode img {} 6 (some t) with
      | .ok b => match decode b with | .ok d => sameImage d.image img | .error _ => false
      | .error _ => false
    r := r.push (s!"png round trip: fixed filter {t}", ok)
  for lv in [0, 1, 9] do
    let ok := match encode img {} lv with
      | .ok b => match decode b with | .ok d => sameImage d.image img | .error _ => false
      | .error _ => false
    r := r.push (s!"png round trip: level {lv}", ok)
  -- pixel density: 144 dpi is 5669 pixels a metre, written as a pHYs chunk after gAMA, and the
  -- image still reads back
  let dense := encode img { pixelsPerMetre := Metadata.dpi 144 }
  let physOk := match dense with
    | .ok b =>
      let want : ByteArray := ⟨#[0, 0, 0, 9, 112, 72, 89, 115, 0, 0, 22, 37, 0, 0, 22, 37, 1]⟩
      let found := (List.range (b.size - want.size)).any fun i =>
        b.extract i (i + want.size) == want
      found && (match decode b with | .ok d => sameImage d.image img | .error _ => false)
    | .error _ => false
  r := r.push ("png: a pixel density of 144 dpi is written as pHYs 5669 and read past",
    physOk && Metadata.dpi 72 == some (2835, 2835))
  -- metadata
  let entries : Array TextEntry := #[{ keyword := "Title", text := "Plot of sin(x)" },
    { keyword := "Source", text := "café\nline 2", international := true, language := "fr",
      translatedKeyword := "Origine" }]
  let md : Metadata := { srgbIntent := some 2, gamma := none, text := entries }
  let mdOk := match encode img md with
    | .ok b => match decode b with
      | .ok d => d.srgbIntent == some 2 && d.gamma == none && d.text == md.text
      | .error _ => false
    | .error _ => false
  r := r.push ("png metadata round trip", mdOk)
  -- the text budget is charged for every field of an entry and for the entry itself
  let tiny : Limits := { maxTextBytes := 3 * (1 + textEntryCost) + 10 }
  let manyEntries := (List.range 5).toArray.map fun _ => ({ keyword := "k", text := "" } :
    TextEntry)
  let budgetOk := match encode img { text := manyEntries } with
    | .ok b => match decode b tiny with
      | .ok d => d.text.size == 3 && d.textDropped == 2
      | .error _ => false
    | .error _ => false
  let longFields : Array TextEntry :=
    #[{ keyword := "k", text := "", international := true, language := "de",
        translatedKeyword := String.ofList (List.replicate 198 'a') }]
  let fieldsOk := match encode img { text := longFields } with
    | .ok b => match decode b { maxTextBytes := 200 + textEntryCost } with
      | .ok d => d.text.isEmpty && d.textDropped == 1
      | .error _ => false
    | .error _ => false
  r := r.push ("png reader: entries without text use up the text budget, and the dropped ones \
    are counted", budgetOk)
  r := r.push ("png reader: the keyword, language and translated keyword count in the text \
    budget", fieldsOk)
  let isErr (x : Except PngError ByteArray) : Bool :=
    match x with | .error (.invalidInput _) => true | _ => false
  let withText (k t : String) : Except PngError ByteArray :=
    encode img { text := #[{ keyword := k, text := t }] }
  r := r ++ #[
    ("png writer: keyword with a leading space", isErr (withText " a" "x")),
    ("png writer: keyword with a double space", isErr (withText "a  b" "x")),
    ("png writer: empty keyword", isErr (withText "" "x")),
    ("png writer: keyword of 80 characters",
      isErr (withText (String.ofList (List.replicate 80 'a')) "x")),
    ("png writer: keyword of 79 characters",
      !isErr (withText (String.ofList (List.replicate 79 'a')) "x")),
    ("png writer: tEXt text above Latin-1", isErr (withText "a" "→")),
    ("png writer: wrong data size", isErr (encode { img with data := img.data.extract 0 5 })),
    ("png writer: zero width", isErr (encode { img with width := 0 })),
    ("png writer: sRGB intent 4", isErr (encode img { srgbIntent := some 4 })),
    ("png writer: filter type 5", isErr (encode img {} 6 (some 5))),
    ("png writer: deterministic", (encode img).toOption == (encode img).toOption)]
  -- adaptive filter choice
  let row : ByteArray := ⟨#[10, 20, 30, 40, 50, 60]⟩
  r := r ++ #[
    ("filter: identical rows choose up", bestFilter row row 3 == 2),
    ("filter: a ramp row without a previous row chooses sub",
      bestFilter row ByteArray.empty 1 == 1),
    ("filter: paeth predictor", paeth 10 20 10 == 20 && paeth 5 5 5 == 5 && paeth 0 255 255 == 0)]
  -- structure of the output
  let png := match encode img with | .ok b => b | .error _ => ByteArray.empty
  let dflt := match decode png with
    | .ok d => d.srgbIntent == some 0 && d.gamma == some 45455
    | .error _ => false
  r := r ++ #[
    ("png: signature", png.extract 0 8 == pngSignature),
    ("png: IHDR first, IEND last",
      png.extract 12 16 == "IHDR".toUTF8 &&
        png.extract (png.size - 8) (png.size - 4) == "IEND".toUTF8),
    ("png: sRGB and gAMA by default", dflt)]
  return r

/-- A PNG header chunk followed by a tiny image-data chunk and `IEND`, with a claimed size. -/
def claimed (w h : Nat) (colorType depth : UInt8) : ByteArray :=
  pngSignature ++
    chunk "IHDR" (be32 w.toUInt32 ++ be32 h.toUInt32 ++ ⟨#[depth, colorType, 0, 0, 0]⟩) ++
    chunk "IDAT" (zlibCompress ⟨#[0, 0, 0, 0]⟩ 6) ++ chunk "IEND" ByteArray.empty

/-- The checks of the reader's rejection of bad files, and the mutation tests. -/
def robustChecks : Array (String × Bool) := Id.run do
  let mut r : Array (String × Bool) := #[]
  let png := samplePng .rgba 6
  r := r ++ #[
    ("png reader: bad signature", failsWith (decode (png.set! 0 0)) .badSignature),
    ("png reader: empty input", failsWith (decode ByteArray.empty) .badSignature),
    ("png reader: CRC error", failsWith (decode (png.set! 20 (png.get! 20 ^^^ 1)))
      (.badCrc "IHDR")),
    ("png reader: size cap on pixels", failsWith (decode (claimed 100000 100000 6 8))
      (.tooLarge "100000 x 100000 pixels")),
    ("png reader: size cap on pixels (colour type 0)",
      failsWith (decode (claimed 100000 100000 0 1)) (.tooLarge "100000 x 100000 pixels")),
    ("png reader: size cap on bytes", match decode (claimed 30000 30000 6 8)
        { maxPixels := 1 <<< 40 } with | .error (.tooLarge _) => true | _ => false),
    ("png reader: huge width", match decode (claimed 0x7FFFFFFF 0x7FFFFFFF 2 8) with
        | .error (.tooLarge _) => true | _ => false),
    ("png reader: width above 2^31-1", match decode (claimed 0x80000000 1 2 8) with
        | .error (.badHeader _) => true | _ => false),
    ("png reader: zero height", match decode (claimed 1 0 2 8) with
        | .error (.badHeader _) => true | _ => false),
    ("png reader: bad depth for colour type", match decode (claimed 1 1 2 4) with
        | .error (.badHeader _) => true | _ => false),
    ("png reader: too little data", match decode (claimed 4 4 0 8) with
        | .error (.badImageData _) => true | _ => false),
    ("png reader: chunk length 2^31",
      failsWith (decode (png.extract 0 8 ++ be32 0x80000000 ++ png.extract 12 png.size))
        .badChunkLength),
    ("png reader: truncated", failsWith (decode (png.extract 0 (png.size - 5))) .truncated),
    ("png reader: unknown ancillary chunk is skipped",
      match decode (png.extract 0 33 ++ chunk "teSt" ⟨#[1, 2]⟩ ++ png.extract 33 png.size) with
        | .ok _ => true | .error _ => false),
    ("png reader: unknown critical chunk is an error",
      failsWith (decode (png.extract 0 33 ++ chunk "TEST" ⟨#[1, 2]⟩ ++ png.extract 33 png.size))
        (.unknownCriticalChunk "TEST"))]
  -- mutations of PNG files, with and without repaired CRCs
  for (nm, mode, lv) in #[("rgba", Mode.rgba, 6), ("grey stored", .l, 0)] do
    let p := samplePng mode lv
    let ms := mutations p
    r := r.push (s!"png mutations ({nm}, {ms.size}): every result is a value, none crashes",
      ms.all fun m => settled (decode m))
    r := r.push (s!"png mutations with repaired CRCs ({nm})",
      ms.all fun m => settled (decode (fixCrcs m)))
  -- zlib streams
  let streams := #[("text", textBytes 300), ("noise", noiseBytes 2 200),
    ("zeros", ByteArray.mk (Array.replicate 500 0))]
  for (nm, d) in streams do
    for lv in [0, 1, 6] do
      let z := zlibCompress d lv
      let ms := mutations z
      r := r.push (s!"zlib mutations ({nm}, level {lv}, {ms.size})",
        ms.all fun m => settled (zlibDecompress m 4096))
  -- stored block lengths set to extremes
  let st := zlibCompress (textBytes 100) 0
  r := r.push ("zlib stored: every LEN/NLEN pair",
    (List.range 65536).all fun n =>
      n % 257 != 0 || settled (zlibDecompress
        ((st.set! 3 (n % 256).toUInt8).set! 4 (n / 256).toUInt8) 4096))
  -- garbage after a valid zlib header
  let garbage := (List.range 3000).all fun k =>
    let g := noiseBytes (k.toUInt32 * 7 + 1) (k % 200)
    settled (zlibDecompress (⟨#[0x78, 0x9c]⟩ ++ g) 5000)
  r := r.push ("zlib garbage after a header", garbage)
  -- valid streams of every length class keep working under a tight exact cap
  r := r.push ("zlib exact caps",
    zInputs.all fun (_, d) => isOk (zlibDecompress (zlibCompress d 6) d.size))
  return r

/-- The CRC-32 of the RGBA form of an image. -/
def rgbaCrc (img : RawImage) : UInt32 :=
  match img.mode with
  | .rgba => crc32 img.data
  | .rgb => crc32 (Id.run do
      let mut b := ByteArray.empty
      for i in [0:img.width * img.height] do
        b := (((b.push (byteAt img.data (3 * i))).push (byteAt img.data (3 * i + 1))).push
          (byteAt img.data (3 * i + 2))).push 255
      return b)
  | .l => crc32 (Id.run do
      let mut b := ByteArray.empty
      for i in [0:img.width * img.height] do
        let g := byteAt img.data i
        b := (((b.push g).push g).push g).push 255
      return b)

/-- The reader on the committed fixtures: each line of `PILeanTest/png/manifest.txt` is
`file width height crc32-of-RGBA-samples-in-hex`. -/
def fixtureChecks : IO (Array (String × Bool)) := do
  let dir : System.FilePath := "PILeanTest" / "png"
  let mut r : Array (String × Bool) := #[]
  if !(← (dir / "manifest.txt").pathExists) then
    return #[("png fixtures: manifest is present", false)]
  let lines := (← IO.FS.readFile (dir / "manifest.txt")).splitOn "\n"
  let mut n := 0
  for line in lines do
    match line.splitOn " " with
    | [f, w, h, c] =>
      n := n + 1
      let bytes ← IO.FS.readBinFile (dir / f)
      let ok := match decode bytes with
        | .ok d => d.image.width == w.toNat! && d.image.height == h.toNat! &&
            s!"{String.ofList ((Nat.toDigits 16 (rgbaCrc d.image).toNat))}" ==
              (c.dropWhile (· == '0'))
        | .error _ => false
      r := r.push (s!"png fixture {f}", ok)
    | _ => pure ()
  r := r.push ("png fixtures: at least 20 listed", n ≥ 20)
  return r

/-- Encodes and decodes a plot-sized image, printing the times; the checks are that the round
trip is exact and that the compressed file is small. -/
def perfChecks : IO (Array (String × Bool)) := do
  let img := plotImage 2000 1200
  let t0 ← IO.monoNanosNow
  let some png := (encode img).toOption | return #[("png perf: encode", false)]
  let t1 ← IO.monoNanosNow
  let ok := match decode png with
    | .ok d => sameImage d.image img
    | .error _ => false
  let t2 ← IO.monoNanosNow
  IO.println s!"perf: 2000x1200 RGBA plot: encode {(t1 - t0) / 1000000} ms, decode \
    {(t2 - t1) / 1000000} ms, {img.data.size} bytes -> {png.size} bytes"
  return #[("png perf: round trip of a 2000x1200 plot", ok),
    ("png perf: plot compresses well", png.size * 20 < img.data.size)]

/-- Writes the writer's files to `dir` for `tools/png-check.py`: for each case `name.png` and
`name.raw` (the samples) with `name.info` (`width height mode`), and for each byte string
`name.zlib` with `name.in`. -/
def writeScratch (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  let cases : Array (String × RawImage) := #[("noise-l-31x17", noiseImage 31 17 .l 1),
    ("noise-rgb-255x17", noiseImage 255 17 .rgb 2), ("noise-rgba-9x33", noiseImage 9 33 .rgba 3),
    ("gradient-rgb-100x80", gradientImage 100 80 .rgb),
    ("gradient-rgba-1x1", gradientImage 1 1 .rgba),
    ("plot-rgba-400x300", plotImage 400 300), ("gradient-l-300x3", gradientImage 300 3 .l)]
  for (nm, img) in cases do
    for (suffix, lv, f) in #[("", 6, none), ("-lv0", 0, some 0), ("-sub", 1, some 1),
        ("-up", 9, some 2), ("-avg", 6, some 3), ("-paeth", 6, some 4)] do
      match encode img { text := #[{ keyword := "Comment", text := "scratch" }] } lv f with
      | .ok b =>
        IO.FS.writeBinFile (dir / s!"{nm}{suffix}.png") b
        IO.FS.writeBinFile (dir / s!"{nm}{suffix}.raw") img.data
        let modeName := match img.mode with | .l => "l" | .rgb => "rgb" | .rgba => "rgba"
        IO.FS.writeFile (dir / s!"{nm}{suffix}.info") s!"{img.width} {img.height} {modeName}\n"
      | .error e => IO.eprintln s!"{nm}: {e}"
  for (nm, d) in zInputs do
    let nm := nm.map fun c => if c.isAlphanum then c else '-'
    IO.FS.writeBinFile (dir / s!"{nm}.in") d
    for lv in [0, 1, 6, 9] do
      IO.FS.writeBinFile (dir / s!"{nm}.{lv}.zlib") (zlibCompress d lv)

/-- All pure checks. -/
def checks : Array (String × Bool) := checksums ++ zlibChecks ++ pngChecks ++ robustChecks

/-- The checks that read files or the clock. -/
def ioChecks : IO (Array (String × Bool)) := do
  return (← fixtureChecks) ++ (← perfChecks)

end PILeanTest.Png
