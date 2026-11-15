/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILeanTest.AnimData
import PILeanTest.Examples
import PILeanTest.TrustData

/-!
# Trust tests

SHA-256 against the published vectors of FIPS 180-4 and NIST (the empty message, `abc`, the
448-bit and the 896-bit messages, one million `a`) and against `shasum -a 256` for every length
from 0 to 130 of a fixed byte pattern (the digests are constants in `PILeanTest.TrustData`,
computed with the system's `shasum`); the source information written into and read back from
SVG, PNG, APNG and GIF files made by the gallery's code paths, with the image data unchanged;
hostile inputs; the reader behind `pilean-info`.
-/

namespace PILeanTest.Trust

open PILean PILean.Trust PILeanTest.AnimData

/-- The `n` bytes `(7 i + 3) mod 256` of the pattern the digest constants are for. -/
def pattern (n : Nat) : ByteArray := ⟨(Array.range n).map fun i => ((i * 7 + 3) % 256).toUInt8⟩

/-- `2 ^ k` zero bytes, built by doubling. -/
def zeros (k : Nat) : ByteArray := Id.run do
  let mut b : ByteArray := ⟨#[0]⟩
  for _ in [0:k] do b := b ++ b
  return b

/-- The hexadecimal digest of a string. -/
def hs (s : String) : String := Sha256.hex (Sha256.hashString s)

/-- The checks of SHA-256 that need no files. -/
def shaChecks : Array (String × Bool) :=
  let million := ByteArray.mk (Array.replicate 1000000 97)
  #[("sha256: empty message", hs "" ==
      "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
    ("sha256: abc", hs "abc" ==
      "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
    ("sha256: the 448-bit message",
      hs "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" ==
        "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
    ("sha256: the 896-bit message of FIPS 180-4",
      hs ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqr\
        lmnopqrsmnopqrstnopqrstu") ==
        "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"),
    ("sha256: a message of 104 bytes (digest from shasum)",
      hs ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopq\
        klmnopqrlmnopqrsmnopqrst") ==
        "068b3a3ce777bea2450554786b903132e681cb3e87e73b42ffb0e4cc15a1203d"),
    ("sha256: one million a", Sha256.hex (Sha256.hash million) ==
      "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"),
    ("sha256: the hash of a string is the hash of its UTF-8 bytes",
      Sha256.hashString "häß ∀" == Sha256.hash "häß ∀".toUTF8),
    ("sha256: digests are 32 bytes", (Sha256.hash million).size == 32),
    ("sha256: hex is lowercase with two digits a byte",
      Sha256.hex ⟨#[0, 10, 255, 171]⟩ == "000affab"),
    ("sha256: 131 digests of the pattern, lengths 0 to 130",
      TrustData.patternDigests.size == 131 &&
        (Array.range 131).all fun n =>
          Sha256.hex (Sha256.hash (pattern n)) == TrustData.patternDigests.getD n ""),
    ("sha256: padding is a multiple of 64 bytes, starts with the message and 0x80",
      (Array.range 200).all fun n =>
        let p := Sha256.pad (pattern n)
        p.size % 64 == 0 && p.size > n && p.size ≤ n + 72 &&
          (p.extract 0 n == pattern n) && p.get! n == 0x80)]

/-- A source with every field. -/
def sample : Source :=
  { module := "PILeanTest.Examples", decl := "PILeanTest.Examples.functions",
    file := "PILeanTest/Examples.lean", line := 59, column := 4,
    repo := some "https://github.com/eric-vergo/PILean", commit := some "0123abcd",
    version := PILean.version, fingerprint := some (hs "specification") }

/-- A source with the fields that need escaping or care. -/
def awkward : Source :=
  { module := "M", decl := "a\"b<c>&d'e\tf", file := "dir/f&g.lean", line := 1, column := 0,
    repo := some "javascript:alert(1)", commit := none, version := "1" }

/-- A small figure, written as SVG and PNG by the gallery's code paths. -/
def figure : Plot.Figure := { PILeanTest.Examples.functions with width := 240, height := 160 }

/-- Whether a result is a value. -/
def isOk {α ε : Type} (r : Except ε α) : Bool := match r with | .ok _ => true | .error _ => false

/-- The value of a result, or a default. -/
def okOr {α ε : Type} (r : Except ε α) (d : α) : α := match r with | .ok v => v | .error _ => d

/-- Whether reading gives exactly `s`. -/
def readsAs (d : ByteArray) (s : Source) : Bool :=
  match Source.read? d with | .ok r => r == s | .error _ => false

/-- Whether reading fails. -/
def readFails (d : ByteArray) : Bool := !isOk (Source.read? d)

/-- Whether `s` contains `t`. -/
def has (s t : String) : Bool := (s.splitOn t).length > 1

/-- Reading a prefix of the file either gives a value or an error (the result is forced). -/
def prefixesClean (d : ByteArray) : Bool :=
  (List.range (d.size / 7 + 1)).all fun k =>
    match Source.read? (d.extract 0 (k * 7)) with | .ok _ => true | .error _ => true

/-- The SVG checks. -/
def svgChecks : Array (String × Bool) :=
  let svg := figure.toSvg
  let out := okOr (withSourceSvg svg sample) ""
  let inserted := "\n" ++ "\n".intercalate (sample.svgNodes.map (Svg.render 2)).toList
  let doc := Svg.document 20 10 (sample.svgNodes ++ #[Svg.rect 0 0 5 5 none])
  let aw := okOr (withSourceSvg svg awkward) ""
  let empty := "<?xml version=\"1.0\"?>\n<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"1\"/>\n"
  let selfClosed := okOr (withSourceSvg empty sample) ""
  let ns := s!"xmlns:pilean=\"{svgNamespace}\""
  let hand := fun (attrs : String) =>
    s!"<svg><metadata><pilean:source {ns} {attrs}/></metadata></svg>"
  let ok := "module=\"m\" decl=\"d\" file=\"f\" line=\"3\" column=\"4\" version=\"1\""
  #[("svg: source round trip", readsAs out.toUTF8 sample),
    ("svg: the rest of the document is unchanged", out.replace inserted "" == svg),
    ("svg: title, description and metadata are the first children",
      has out "<title>PILeanTest.Examples.functions</title>" &&
        has out "<desc>Generated by PILeanTest.Examples.functions in PILeanTest/Examples.lean:59 \
          with PILean 0.1.0</desc>" && has out "<metadata>"),
    ("svg: the Node model round trip", readsAs doc.toUTF8 sample),
    ("svg: a figure without a source is byte-identical to the writer's output",
      figure.toSvg == svg && !has svg "pilean"),
    ("svg: no source in a plain document", readFails svg.toUTF8),
    ("svg: awkward values round trip", readsAs aw.toUTF8 awkward),
    ("svg: awkward values are escaped",
      has aw "a&quot;b&lt;c&gt;&amp;d&#39;e&#9;f" && !has aw "<c>"),
    ("svg: a self-closing root is opened", readsAs selfClosed.toUTF8 sample &&
      has selfClosed "</svg>"),
    ("svg: a second source is refused", !isOk (withSourceSvg out sample)),
    ("svg: no root element is refused", !isOk (withSourceSvg "<g/>" sample)),
    ("svg: hand-written element", readsAs (hand ok).toUTF8
      { module := "m", decl := "d", file := "f", line := 3, column := 4, version := "1" }),
    ("svg: unknown attributes are ignored", isOk (Source.read? (hand (ok ++ " x=\"y\"")).toUTF8)),
    ("svg: character references", readsAs (hand "module=\"&#x41;&#66;&amp;\" decl=\"d\" file=\"f\" \
      line=\"3\" column=\"4\" version=\"1\"").toUTF8
      { module := "AB&", decl := "d", file := "f", line := 3, column := 4, version := "1" }),
    ("svg: single-quoted values", isOk (Source.read? (hand "module='m' decl='d' file='f' \
      line='3' column='4' version='1'").toUTF8)),
    ("svg: an unknown entity is refused", readFails (hand "module=\"&bogus;\" decl=\"d\" \
      file=\"f\" line=\"3\" column=\"4\" version=\"1\"").toUTF8),
    ("svg: a character reference to NUL is refused", readFails (hand "module=\"&#0;\" decl=\"d\" \
      file=\"f\" line=\"3\" column=\"4\" version=\"1\"").toUTF8),
    ("svg: a character reference to a surrogate is refused", readFails (hand "module=\"&#xD800;\" \
      decl=\"d\" file=\"f\" line=\"3\" column=\"4\" version=\"1\"").toUTF8),
    ("svg: a duplicate attribute is refused", readFails (hand (ok ++ " module=\"n\"")).toUTF8),
    ("svg: a huge value is refused", readFails (hand ("module=\"" ++ String.ofList
      (List.replicate 5000 'a') ++ "\" decl=\"d\" file=\"f\" line=\"3\" column=\"4\" \
      version=\"1\"")).toUTF8),
    ("svg: a missing required key is refused", readFails (hand "module=\"m\"").toUTF8),
    ("svg: a non-numeric line is refused", readFails (hand "module=\"m\" decl=\"d\" file=\"f\" \
      line=\"3x\" column=\"4\" version=\"1\"").toUTF8),
    ("svg: a bad fingerprint is refused", readFails (hand (ok ++ " fingerprint=\"ABC\"")).toUTF8),
    ("svg: the wrong namespace is refused", readFails
      s!"<svg><pilean:source xmlns:pilean=\"urn:other\" {ok}/></svg>".toUTF8),
    ("svg: no namespace is refused", readFails s!"<svg><pilean:source {ok}/></svg>".toUTF8),
    ("svg: a source inside a comment is ignored",
      readFails s!"<svg><!-- <pilean:source {ns} {ok}/> --></svg>".toUTF8),
    ("svg: a source inside a CDATA section is ignored",
      readFails s!"<svg><![CDATA[<pilean:source {ns} {ok}/>]]></svg>".toUTF8),
    ("svg: two elements are refused", readFails
      s!"<svg><pilean:source {ns} {ok}/><pilean:source {ns} {ok}/></svg>".toUTF8),
    ("svg: an unclosed element is refused", readFails s!"<svg><pilean:source {ns} {ok}".toUTF8),
    ("svg: an unclosed value is refused", readFails s!"<svg><pilean:source {ns} module=\"m".toUTF8),
    ("svg: invalid UTF-8 is refused", readFails (("<svg>".toUTF8.push 0xFF) ++ "</svg>".toUTF8)),
    ("svg: truncated copies are values or errors", prefixesClean out.toUTF8)]

/-- The PNG and APNG checks. -/
def pngChecks : Array (String × Bool) :=
  let png := (figure.toPng).getD ByteArray.empty
  let out := okOr (withSourcePng png sample) ByteArray.empty
  let aw := okOr (withSourcePng png awkward) ByteArray.empty
  let apng := okOr movingSquare.toApng ByteArray.empty
  let aout := okOr (withSourcePng apng sample) ByteArray.empty
  let dec := fun (d : ByteArray) => Png.decode d
  let same := fun (a b : ByteArray) => match dec a, dec b with
    | .ok x, .ok y => x.image.width == y.image.width && x.image.height == y.image.height &&
        x.image.mode == y.image.mode && x.image.data == y.image.data
    | _, _ => false
  let frames := fun (d : ByteArray) => match Anim.readApng d with
    | .ok s => some (s.width, s.height, s.frames.map (fun (im : Image) => im.data), s.delays,
        s.loops)
    | .error _ => none
  let texts := match dec out with
    | .ok r => r.text.map (fun (e : Png.TextEntry) => e.keyword)
    | .error _ => #[]
  let dup := (png.extract 0 33) ++ (okOr sample.pngChunks ByteArray.empty) ++
    (okOr sample.pngChunks ByteArray.empty) ++ png.extract 33 png.size
  let bad := fun (k : Nat) => (out.extract 0 k) ++ ⟨#[(out.get! k) ^^^ 1]⟩ ++
    out.extract (k + 1) out.size
  let chunkAt := fun (d : ByteArray) (ty : String) => (findBytes d ty.toUTF8).getD d.size
  #[("png: source round trip", readsAs out sample),
    ("png: the image decodes to the same pixels", same png out),
    ("png: the writer's own reader sees nine text entries, all PILean keywords",
      texts.size == 9 && texts.all (fun (k : String) => k.startsWith "PILean:")),
    ("png: the source chunks come before IDAT, after IHDR",
      chunkAt out "iTXt" < chunkAt out "IDAT" && chunkAt out "IHDR" < chunkAt out "iTXt"),
    ("png: awkward values round trip", readsAs aw awkward),
    ("png: a javascript: repo is read as text and is not a safe link",
      (match Source.read? aw with
        | .ok s => s.repo == some "javascript:alert(1)" && (safeLink? "javascript:alert(1)").isNone
        | .error _ => false)),
    ("png: no source in a plain file", readFails png),
    ("png: a second source is refused", !isOk (withSourcePng out sample)),
    ("png: a duplicate key is refused", readFails dup),
    ("png: a flipped bit in a source chunk is refused", readFails (bad (chunkAt out "iTXt" + 20))),
    ("png: a file that is not a PNG with IHDR is refused",
      !isOk (withSourcePng "xx".toUTF8 sample)),
    ("png: truncated copies are values or errors", prefixesClean out),
    ("png: a file cut before IDAT is an error", readFails (out.extract 0 (chunkAt out "IDAT" + 2))),
    ("apng: source round trip", readsAs aout sample),
    ("apng: frames, delays and loops read back equal", (frames apng).isSome &&
      frames apng == frames aout),
    ("apng: the source comes before acTL", chunkAt aout "iTXt" < chunkAt aout "acTL"),
    ("apng: truncated copies are values or errors", prefixesClean aout)]

/-- The GIF checks. -/
def gifChecks : Array (String × Bool) :=
  let gif := okOr movingSquare.toGif ByteArray.empty
  let out := okOr (withSourceGif gif sample) ByteArray.empty
  let frames := fun (d : ByteArray) => match Anim.readGif d with
    | .ok s => some (s.width, s.height, s.frames.map (fun (im : Image) => im.data), s.delays,
        s.loops)
    | .error _ => none
  let nl : Source := { awkward with decl := "a\nb" }
  let bigSrc : Source := { sample with commit := some (String.ofList (List.replicate 4000 'c')),
                                       repo := some (String.ofList (List.replicate 4000 'r')) }
  let big := okOr (withSourceGif gif bigSrc) ByteArray.empty
  let start := okOr (gifBodyStart gif true) 13
  let comment := fun (text : String) => (gif.extract 0 start ++ commentExtension text.toUTF8) ++
    gif.extract start gif.size
  #[("gif: source round trip", readsAs out sample),
    ("gif: frames, delays and loops read back equal", (frames gif).isSome &&
      frames gif == frames out),
    ("gif: awkward values round trip", (match withSourceGif gif awkward with
      | .ok d => readsAs d awkward | .error _ => false)),
    ("gif: a line break in a value is refused", !isOk (withSourceGif gif nl)),
    ("gif: a comment of several sub-blocks round trips", big.size > gif.size + 8000 &&
      readsAs big bigSrc),
    ("gif: sub-blocks hold at most 255 bytes",
      (commentExtension (zeros 10)).size == 2 + (1024 / 255 + 1) + 1024 + 1 &&
        (commentExtension (zeros 8)).get! 2 == 255),
    ("gif: no source in a plain file", readFails gif),
    ("gif: a second source is refused", !isOk (withSourceGif out sample)),
    ("gif: unknown keys are ignored", match Source.read? (comment
        "PILean source 1\nmodule=m\ndecl=d\nfile=f\nline=3\ncolumn=4\nversion=1\nother=x\n") with
      | .ok s => s.module == "m" | .error _ => false),
    ("gif: a value may contain =", match Source.read? (comment
        "PILean source 1\nmodule=a=b\ndecl=d\nfile=f\nline=3\ncolumn=4\nversion=1\n") with
      | .ok s => s.module == "a=b" | .error _ => false),
    ("gif: a duplicate key is refused", readFails (comment
        "PILean source 1\nmodule=m\nmodule=n\ndecl=d\nfile=f\nline=3\ncolumn=4\nversion=1\n")),
    ("gif: a comment without the first line is ignored", readFails (comment
        "module=m\ndecl=d\nfile=f\nline=3\ncolumn=4\nversion=1\n")),
    ("gif: truncated copies are values or errors", prefixesClean out)]

/-- Whether every element of `xs` is `none`-free (used to force a list). -/
def allOk (xs : List Bool) : Bool := xs.all id

/-- The validation, the link rule, the escaping and the size cap. -/
def readerChecks : Array (String × Bool) :=
  let withNul := { sample with decl := "a\x00b" }
  let big := (zeros 26).push 0
  let png := (figure.toPng).getD ByteArray.empty
  #[("source: a NUL is refused for every format",
      !isOk withNul.validate && !isOk (withSourcePng png withNul) &&
        !isOk (withSource figure.toSvg.toUTF8 withNul)),
    ("source: a value above 4096 bytes is refused",
      !isOk { sample with file := String.ofList (List.replicate 4097 'x') }.validate),
    ("source: a fingerprint must be 64 lowercase hexadecimal digits",
      isOk sample.validate && !isOk { sample with fingerprint := some "abc" }.validate &&
        !isOk { sample with fingerprint := some (String.ofList (List.replicate 64 'A')) }.validate),
    ("source: the dispatcher finds the format", allOk [
      readsAs (okOr (withSource figure.toSvg.toUTF8 sample) ByteArray.empty) sample,
      readsAs (okOr (withSource png sample) ByteArray.empty) sample,
      readsAs (okOr (withSource (okOr movingSquare.toGif ByteArray.empty) sample)
        ByteArray.empty) sample] && !isOk (withSource "hello".toUTF8 sample)),
    ("source: input above the cap is refused without being read", readFails big),
    ("source: random bytes are refused", readFails (pattern 300) && readFails ByteArray.empty),
    ("link: https and http are safe",
      (safeLink? "https://github.com/eric-vergo/PILean").isSome &&
        (safeLink? "http://example.org/a?b=c#d").isSome),
    ("link: other schemes are not", ["javascript:alert(1)", "data:text/html,x", "ftp://x/y",
        "//x/y", "file:///etc/passwd", "HTTPS://x/y", "https:/x"].all fun u =>
      (safeLink? u).isNone),
    ("link: quotes, angle brackets, backslash, white space and controls are not",
      ["https://x/\"", "https://x/'", "https://x/<", "https://x/>", "https://x/ y",
        "https://x/\ty", "https://x/\n", "https://x/\x00", "https://x/\\", "https://x/`",
        "https://x/ä", "https://", "http://"].all fun u => (safeLink? u).isNone),
    ("escape: control characters are shown as escapes",
      escapeControl "a\nb\tc\x00d\\e\x1b" == "a\\nb\\tc\\u{0}d\\\\e\\u{1b}" ||
        escapeControl "a\nb\tc\x00d\\e\x1b" == "a\\nb\\tc\\u{0}d\\\\e\\u{1B}"),
    ("info: the lines of a written file", match infoLines
        (okOr (withSource png awkward) ByteArray.empty) with
      | .ok ls => ls == #["module: M", "decl: a\"b<c>&d'e\\tf", "file: dir/f&g.lean",
          "line: 1", "column: 0", "repo: javascript:alert(1)", "version: 1"]
      | .error _ => false),
    ("info: a file without a source is an error", !isOk (infoLines png))]

/-- The checks of SHA-256 and of the source information. -/
def checks : Array (String × Bool) :=
  shaChecks ++ svgChecks ++ pngChecks ++ gifChecks ++ readerChecks

/-- The timing of the hash of 8 MiB (printed) and its digest. -/
def ioChecks : IO (Array (String × Bool)) := do
  let t0 ← IO.monoMsNow
  let data := (zeros 23).set! 0 (t0 % 1).toUInt8
  let d := Sha256.hex (Sha256.hash data)
  IO.println s!"sha256: digest {d}"
  let t1 ← IO.monoMsNow
  IO.println s!"sha256: 8 MiB in {t1 - t0} ms"
  return #[("sha256: 8 MiB of zero bytes",
      d == "2daeb1f36095b44b318410b3f4e8b5d989dcc7bb023d1426c492dab0a3053e74"),
    ("sha256: 8 MiB in a few seconds", t1 - t0 < 15000)]

end PILeanTest.Trust
