/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean

/-!
# Bounded work on hostile input

The readers are run on inputs made to cost as much as their caps allow, each in a child process
(`pilean-probe KIND FILE`, built beside the test driver) under a CPU-time limit and a wall-clock
watchdog,
and the child's peak resident memory and CPU time are measured with `/usr/bin/time`. A check
fails if the child is killed, gives the wrong answer, uses more memory than the bound the
reader's documentation states (the decoded buffers plus a fixed allowance for the runtime) or
more CPU time than its case allows, or if either measurement is missing (`withinBounds`). The
bounds are fixed numbers with room to spare: they catch a large regression on these inputs; they
are not a proof of a reader's complexity.

The large inputs are generated here, not stored: a zlib stream of zeros made of 258-byte matches,
PNG and PDF files that wrap it, and PDF files of many pages, operators or nested arrays; the hostile graphs are made by the probe (`hostileGraph`), which
lays each out and writes its SVG, so the bounds cover the drawing as well as the layout (the
100,000 routes of the self-loop case make an SVG of about 36 MB).

## Main definitions

* `Run`, `runLimited`: a child under limits, and what it used.
* `ioChecks`: the checks.
-/

namespace PILeanTest.Bounds

open PILean

/-! ### Generated inputs -/

/-- A bit writer (least significant bit first, as DEFLATE packs bits). -/
structure BitOut where
  /-- The finished bytes. -/
  out : ByteArray := .empty
  /-- The pending bits. -/
  acc : Nat := 0
  /-- The number of pending bits. -/
  n : Nat := 0

/-- Appends the `k` low bits of `v`, least significant first. -/
def BitOut.bits (w : BitOut) (v k : Nat) : BitOut := Id.run do
  let mut acc := w.acc ||| ((v % (1 <<< k)) <<< w.n)
  let mut n := w.n + k
  let mut out := w.out
  for _ in [0:n / 8] do
    out := out.push (acc % 256).toUInt8
    acc := acc >>> 8
    n := n - 8
  return { out, acc, n }

/-- Appends a Huffman code of `k` bits, most significant bit first. -/
def BitOut.code (w : BitOut) (c k : Nat) : BitOut := Id.run do
  let mut w := w
  for i in [0:k] do
    w := w.bits ((c >>> (k - 1 - i)) &&& 1) 1
  return w

/-- The bytes, with the last partial byte padded by zeros. -/
def BitOut.finish (w : BitOut) : ByteArray := if w.n > 0 then w.out.push w.acc.toUInt8 else w.out

/-- A zlib stream of `n` zero bytes: one fixed-code block, a literal zero, then matches of 258
bytes at distance 1 (13 bits each) and literals for the rest. -/
def zerosZlib (n : Nat) : ByteArray := Id.run do
  let mut w : BitOut := { out := ⟨#[0x78, 0x01]⟩ }
  w := w.bits 1 1 |>.bits 1 2
  let mut left := n
  if left > 0 then
    w := w.code 0x30 8
    left := left - 1
  for _ in [0:left / 258] do
    w := w.code 0xC5 8 |>.code 0 5
  for _ in [0:left % 258] do
    w := w.code 0x30 8
  w := w.code 0 7
  let adler : UInt32 := ((n % 65521).toUInt32 <<< 16) ||| 1
  return w.finish ++ Png.be32 adler

/-- A PNG file with the given header fields and the given compressed image data. -/
def pngWith (w h depth colorType : Nat) (idat : ByteArray) : ByteArray :=
  let ihdr := Png.be32 w.toUInt32 ++ Png.be32 h.toUInt32 ++
    ⟨#[depth.toUInt8, colorType.toUInt8, 0, 0, 0]⟩
  Png.pngSignature ++ Png.chunk "IHDR" ihdr ++ Png.chunk "IDAT" idat ++
    Png.chunk "IEND" .empty

/-- An APNG of `n` frames of `w × h` RGBA pixels, every frame the whole canvas and every frame's
data a zlib stream of zeros (`zerosZlib`), so that the file is small and its frames large. -/
def apngZeros (w h n : Nat) : ByteArray := Id.run do
  let z := zerosZlib (h * (1 + w * 4))
  let ihdr := Png.be32 w.toUInt32 ++ Png.be32 h.toUInt32 ++ ⟨#[8, 6, 0, 0, 0]⟩
  let fctl := fun (seq : Nat) => Png.be32 seq.toUInt32 ++ Png.be32 w.toUInt32 ++
    Png.be32 h.toUInt32 ++ Png.be32 0 ++ Png.be32 0 ++ ⟨#[0, 1, 0, 10, 0, 0]⟩
  let mut out := Png.pngSignature ++ Png.chunk "IHDR" ihdr ++
    Png.chunk "acTL" (Png.be32 n.toUInt32 ++ Png.be32 0)
  let mut seq := 0
  for i in [0:n] do
    out := out ++ Png.chunk "fcTL" (fctl seq)
    seq := seq + 1
    if i == 0 then out := out ++ Png.chunk "IDAT" z
    else
      out := out ++ Png.chunk "fdAT" (Png.be32 seq.toUInt32 ++ z)
      seq := seq + 1
  return out ++ Png.chunk "IEND" .empty

/-- A 1 × 1 grey PNG with `n` text chunks before its image data, each with the keyword `k` and
no text: the most entries for the fewest bytes. -/
def pngManyTexts (n : Nat) : ByteArray := Id.run do
  let ihdr := Png.be32 1 ++ Png.be32 1 ++ ⟨#[8, 0, 0, 0, 0]⟩
  let text := Png.chunk "tEXt" ⟨#[107, 0]⟩
  let mut out := Png.pngSignature ++ Png.chunk "IHDR" ihdr
  for _ in [0:n] do out := out ++ text
  return out ++ Png.chunk "IDAT" (zerosZlib 2) ++ Png.chunk "IEND" .empty

/-- The number of entries with the keyword `k` and no text that the default text budget holds
(`Png.TextEntry.cost`). -/
def maxTextEntries : Nat := ({} : Png.Limits).maxTextBytes / (1 + Png.textEntryCost)

/-- The decompressed size of a non-interlaced PNG image (rows with their filter bytes). -/
def rawSize (w h bytesPerPixel : Nat) : Nat := h * (1 + w * bytesPerPixel)

/-- The output cap `pilean-probe zlib` uses. -/
def zlibCap : Nat := 1 <<< 28

/-- A PDF file whose page's content is `content` (a stream with the dictionary entries `dict`),
from the writer's `Pdf.document`. -/
def pdfWith (content : ByteArray) (dict : String := "") (resources : String := "<< >>") :
    ByteArray :=
  let page := "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 10 10] /Resources 4 0 R \
    /Contents 5 0 R >>"
  Pdf.document #["<< /Type /Catalog /Pages 2 0 R >>".toUTF8,
    "<< /Type /Pages /Kids [3 0 R] /Count 1 >>".toUTF8, page.toUTF8, resources.toUTF8,
    s!"<< {dict} /Length {content.size} >>\nstream\n".toUTF8 ++ content ++ "\nendstream".toUTF8] 1

/-- `n` copies of the text. -/
def repeatText (s : String) (n : Nat) : ByteArray := Id.run do
  let b := s.toUTF8
  let mut out := ByteArray.emptyWithCapacity (n * b.size)
  for _ in [0:n] do out := out ++ b
  return out

/-- A PDF file of `n` pages, each its own page object with a one-operator content stream. -/
def pdfPages (n : Nat) : ByteArray := Id.run do
  let kids := " ".intercalate ((List.range n).map fun k => s!"{3 + 2 * k} 0 R")
  let mut objs := #["<< /Type /Catalog /Pages 2 0 R >>".toUTF8,
    s!"<< /Type /Pages /Kids [{kids}] /Count {n} >>".toUTF8]
  for k in [0:n] do
    objs := objs.push
      s!"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 1 1] /Contents {4 + 2 * k} 0 R >>".toUTF8
    objs := objs.push "<< /Length 3 >>\nstream\nq Q\nendstream".toUTF8
  return Pdf.document objs 1

/-! ### Running under limits -/

/-- What a child used. -/
structure Run where
  /-- The exit status, or none if the watchdog killed it. -/
  status : Option UInt32
  /-- Its standard output. -/
  out : String
  /-- Its standard error. -/
  err : String := ""
  /-- The peak resident memory in bytes, if `/usr/bin/time` reported it. -/
  rss : Option Nat
  /-- The user CPU time in milliseconds, if reported. -/
  userMs : Option Nat

/-- The number in a line of `/usr/bin/time` output that follows or precedes `label`. -/
def timeField (err label : String) (before : Bool) : Option Nat := Id.run do
  for l in err.splitOn "\n" do
    if (l.splitOn label).length > 1 then
      let ws := (l.splitOn " ").filter (!·.isEmpty)
      let w := if before then ws.head? else ws.getLast?
      return w.bind String.toNat?
  return none

/-- A decimal number of seconds such as `9.20` in milliseconds. -/
def secondsMs (s : String) : Option Nat :=
  match s.splitOn "." with
  | [a] => a.toNat?.map (· * 1000)
  | [a, b] => do
    let f := (b ++ "000").take 3
    return (← a.toNat?) * 1000 + (← f.toString.toNat?)
  | _ => none

/-- The user time from `/usr/bin/time` output (`-l` on macOS, `-v` elsewhere). -/
def userTime (err : String) : Option Nat := Id.run do
  for l in err.splitOn "\n" do
    let ws := (l.splitOn " ").filter (!·.isEmpty)
    -- macOS: `  9.20 real  8.90 user  0.20 sys`
    if let some i := ws.idxOf? "user" then
      if i > 0 then return ws[i - 1]?.bind secondsMs
    -- GNU: `User time (seconds): 8.90`
    if (l.splitOn "User time (seconds):").length > 1 then return ws.getLast?.bind secondsMs
  return none

/-- Runs the executable `exe` (a sibling of the test driver) with `args` in its own process group
under a CPU limit of `cpuS` seconds, killed after `wallMs` milliseconds, and measures it with
`/usr/bin/time`. -/
def runLimited (exe : String) (args : Array String) (cpuS wallMs : Nat)
    (scratch : System.FilePath) : IO Run := do
  let app := ((← IO.appPath).parent.getD ".") / exe
  let outF := scratch / "child.out"
  let errF := scratch / "child.err"
  let timeF := scratch / "child.time"
  let mac := System.Platform.isOSX
  let flag := if mac then "-l" else "-v"
  let script := s!"ulimit -t {cpuS}; o=$1; e=$2; t=$3; shift 3; export o e; " ++
    s!"exec /usr/bin/time {flag} /bin/sh -c 'exec \"$@\" > \"$o\" 2> \"$e\"' sh \"$@\" " ++
    "2> \"$t\""
  let shArgs := #["-c", script, "sh", outF.toString, errF.toString, timeF.toString,
    app.toString] ++ args
  let child ← IO.Process.spawn { cmd := "/bin/sh", args := shArgs, setsid := true }
  let mut status : Option UInt32 := none
  for _ in [0:wallMs / 50 + 1] do
    if let some s ← child.tryWait then
      status := some s
      break
    IO.sleep 50
  if status.isNone then
    child.kill
    let _ ← child.wait
  let out ← try IO.FS.readFile outF catch _ => pure ""
  let err ← try IO.FS.readFile errF catch _ => pure ""
  let tm ← try IO.FS.readFile timeF catch _ => pure ""
  let rss := if mac then timeField tm "maximum resident set size" true
    else (timeField tm "Maximum resident set size" false).map (· * 1024)
  return { status := status, out := out.trimAscii.toString, err := err, rss := rss,
           userMs := userTime tm }

/-- One case: a file, how to decode it, the start of the expected output line, and the bound
on peak memory in bytes. -/
structure Case where
  /-- The case's name. -/
  name : String
  /-- The kind `pilean-probe` is given. -/
  kind : String
  /-- The input. -/
  bytes : IO ByteArray
  /-- The expected start of the child's output. -/
  expect : String
  /-- The bound on peak resident memory. -/
  maxRss : Nat
  /-- The bound on user CPU time, in milliseconds (far above what the case takes, so that a
  loaded machine does not fail it, and far below what unbounded work would take). -/
  maxUserMs : Nat := 30000
  /-- The arguments of `pilean-probe` when the case is not a file (a generated graph). -/
  argv : Option (Array String) := none

/-- The memory the runtime and the probe use besides the reader's buffers. -/
def baseRss : Nat := 32 <<< 20

/-- The cases. -/
def cases : Array Case :=
  let big := 8192 * 8191
  #[{ name := "png: RGBA 8-bit at the byte cap decodes into two buffers", kind := "png",
      bytes := pure (pngWith 8192 8191 8 6 (zerosZlib (rawSize 8192 8191 4))),
      expect := "ok 8192x8191", maxRss := baseRss + rawSize 8192 8191 4 + big * 4 },
    { name := "png: RGBA 16-bit over the byte cap is refused before allocating",
      kind := "png", bytes := pure (pngWith 8192 8191 16 6 (zerosZlib (rawSize 8192 8191 8))),
      expect := "error image too large", maxRss := baseRss + (16 <<< 20) },
    { name := "png: image data too short for its header is refused before allocating",
      kind := "png", bytes := pure (pngWith 8192 8191 8 6 (zerosZlib 1000)),
      expect := "error invalid image data", maxRss := baseRss },
    { name := "png: 300000 empty text chunks are held to the text budget", kind := "png",
      bytes := pure (pngManyTexts 300000), expect := s!"ok 1x1 1 text {maxTextEntries}",
      maxRss := baseRss + 300000 * 14 + 4 * (1 <<< 22) },
    { name := "zlib: a bomb over the cap is refused without its output", kind := "zlib",
      bytes := pure (zerosZlib (zlibCap + 1)), expect := "error decompressed data exceeds",
      maxRss := baseRss + (8 <<< 20) },
    { name := "zlib: output at the cap is allocated once", kind := "zlib",
      bytes := pure (zerosZlib zlibCap), expect := s!"ok {zlibCap}",
      maxRss := baseRss + zlibCap + (8 <<< 20) },
    { name := "gif: a 4096 x 4096 frame from 11 KB of LZW", kind := "gif",
      bytes := IO.FS.readBinFile ("PILeanTest" / "png" / "lzw-zeros-4096.gif"),
      expect := "ok 4096x4096", maxRss := baseRss + 4096 * 4096 * (4 * 3 + 1) },
    { name := "apng: 64 frames of 1024 x 1024 fill the byte cap; the 65th is refused",
      kind := "apng", bytes := pure (apngZeros 1024 1024 65),
      expect := "error PILean.Anim.AnimError.tooLarge \"composed frames\"",
      maxRss := baseRss + (1 <<< 28) + 8 * (1024 * 1024 * 4) },
    { name := "pdf: a content stream that inflates past the cap is refused without its output",
      kind := "pdf",
      bytes := pure (pdfWith (zerosZlib (Pdf.maxDecoded + 1)) "/Filter /FlateDecode"),
      expect := "error object 5: its Flate data is damaged", maxRss := baseRss + (16 <<< 20) },
    { name := "pdf: 200000 nested arrays stop at the nesting cap",
      kind := "pdf", bytes := pure (pdfWith .empty (resources := "<< /A " ++
        String.ofList (List.replicate 200000 '[') ++ " >>")),
      expect := "error", maxRss := baseRss + (16 <<< 20), maxUserMs := 5000 },
    { name := "pdf: a string of 8 MiB is refused at the string cap",
      kind := "pdf", bytes := pure (pdfWith .empty (resources := "<< /A (" ++
        String.ofList (List.replicate (8 <<< 20) 'x') ++ ") >>")),
      expect := "error a string is too long", maxRss := baseRss + (64 <<< 20), maxUserMs := 5000 },
    { name := "pdf: 20000 pages are walked in linear time",
      kind := "pdf", bytes := pure (pdfPages 20000), expect := "ok pages 20000",
      maxRss := 512 <<< 20, maxUserMs := 30000 },
    { name := "pdf: a content stream of a million operators",
      kind := "pdf", bytes := pure (pdfWith (repeatText "0 0 m 1 1 l S\n" 333334)),
      expect := "ok pages 1", maxRss := 512 <<< 20, maxUserMs := 30000 },
    { name := "pdf: 60 MiB with no cross-reference table is refused at once",
      kind := "source", bytes := pure ("%PDF-1.7\n".toUTF8 ++ repeatText "          " (6 <<< 20)),
      expect := "error no startxref", maxRss := baseRss + (192 <<< 20), maxUserMs := 5000 },
    { name := "graph: edges spanning thousands of layers get no dummy nodes beyond the cap",
      kind := "graph", bytes := pure .empty, argv := some #["graph", "fan", "3000"],
      expect := "ok 3000 nodes", maxRss := 128 <<< 20, maxUserMs := 10000 },
    { name := "graph: every pair of 300 nodes (44850 edges)", kind := "graph",
      bytes := pure .empty, argv := some #["graph", "dense", "300"], expect := "ok 300 nodes",
      maxRss := 256 <<< 20, maxUserMs := 10000 },
    { name := "graph: 20000 parallel edges between two nodes", kind := "graph",
      bytes := pure .empty, argv := some #["graph", "multi", "20000"],
      expect := "ok 20000 nodes", maxRss := 256 <<< 20, maxUserMs := 15000 },
    { name := "graph: 10000 nodes with ten self-loops each", kind := "graph",
      bytes := pure .empty, argv := some #["graph", "loops", "10000"],
      expect := "ok 10000 nodes", maxRss := 384 <<< 20, maxUserMs := 10000 },
    { name := "graph: 5000 orthogonal routes sideways in one gap (tracks placed pairwise)",
      kind := "graph", bytes := pure .empty, argv := some #["graph", "star", "5000", "orthogonal"],
      expect := "ok 5001 nodes", maxRss := 128 <<< 20, maxUserMs := 4000 },
    { name := "graph: 5000 bundled routes sideways in one channel (runs compared pairwise)",
      kind := "graph", bytes := pure .empty, argv := some #["graph", "star", "5000", "bundled"],
      expect := "ok 5001 nodes", maxRss := 512 <<< 20, maxUserMs := 20000 },
    { name := "graph: 20000 parallel edges between two nodes, bundled", kind := "graph",
      bytes := pure .empty, argv := some #["graph", "multi", "20000", "bundled"],
      expect := "ok 20000 nodes", maxRss := 512 <<< 20, maxUserMs := 30000 },
    { name := "graph: 10000 nodes with ten self-loops each, bundled", kind := "graph",
      bytes := pure .empty, argv := some #["graph", "loops", "10000", "bundled"],
      expect := "ok 10000 nodes", maxRss := 512 <<< 20, maxUserMs := 20000 },
    { name := "graph: 20000 nodes, 40000 random edges", kind := "graph", bytes := pure .empty,
      argv := some #["graph", "sparse", "20000"], expect := "ok 20000 nodes",
      maxRss := 512 <<< 20, maxUserMs := 40000 }]

/-- Whether a run of a case passed: it exited with status 0 and the expected answer, and its peak
memory and CPU time were both measured and within the case's bounds. A measurement that is
missing fails the case: a bound that was not checked is not a bound that held. -/
def withinBounds (c : Case) (run : Run) : Bool :=
  run.status == some 0 && run.out.startsWith c.expect &&
    (run.rss.map (fun m => decide (m ≤ c.maxRss))).getD false &&
    (run.userMs.map (fun t => decide (t ≤ c.maxUserMs))).getD false

/-- Checks of `withinBounds` and of the parsers of `/usr/bin/time` on made-up runs: a run with
either measurement missing, or with an empty time report, fails. -/
def verdictChecks : Array (String × Bool) :=
  let c : Case :=
    { name := "x", kind := "png", bytes := pure .empty, expect := "ok", maxRss := 100,
      maxUserMs := 100 }
  let good : Run := { status := some 0, out := "ok 1x1", rss := some 50, userMs := some 50 }
  let mac := "  0.10 real  0.05 user  0.01 sys\n  52428800  maximum resident set size\n"
  #[("bounds: a run within both measured bounds passes", withinBounds c good),
    ("bounds: a run without a memory measurement fails",
      !withinBounds c { good with rss := none }),
    ("bounds: a run without a CPU time fails", !withinBounds c { good with userMs := none }),
    ("bounds: a run over either bound fails",
      !withinBounds c { good with rss := some 101 } &&
        !withinBounds c { good with userMs := some 101 }),
    ("bounds: an empty time report gives no measurement",
      timeField "" "maximum resident set size" true == none && userTime "" == none),
    ("bounds: a macOS time report is read",
      timeField mac "maximum resident set size" true == some 52428800 && userTime mac == some 50)]

/-- Runs every case; each check says the child finished in time with the expected answer and
within its memory and CPU bounds, both of them measured. -/
def ioChecks : IO (Array (String × Bool)) := do
  let scratch ← IO.FS.createTempDir
  let mut r : Array (String × Bool) := #[]
  try
    for c in cases do
      let f := scratch / "input"
      let argv ← match c.argv with
        | some a => pure a
        | none => do IO.FS.writeBinFile f (← c.bytes); pure #[c.kind, f.toString]
      let run ← runLimited "pilean-probe" argv 120 240000 scratch
      let mem := match run.rss with
        | some m => s!"{m / 1048576} MiB (bound {c.maxRss / 1048576} MiB)"
        | none => "memory not measured"
      let cpu := match run.userMs with | some t => s!"{t} ms" | none => "?"
      IO.println s!"bounds: {c.name}: {run.out}; {mem}; user {cpu}"
      r := r.push (s!"bounds: {c.name}", withinBounds c run)
  finally
    IO.FS.removeDirAll scratch
  return verdictChecks ++ r

end PILeanTest.Bounds
