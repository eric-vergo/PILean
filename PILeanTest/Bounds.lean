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
fails if the child is killed, gives the wrong answer, or uses more memory than the bound the
reader's documentation states (the decoded buffers plus a fixed allowance for the runtime).

The large inputs are generated here, not stored: a zlib stream of zeros made of 258-byte matches,
and PNG files that wrap it; the hostile graphs are made by the probe (`hostileGraph`), which
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

/-- The decompressed size of a non-interlaced PNG image (rows with their filter bytes). -/
def rawSize (w h bytesPerPixel : Nat) : Nat := h * (1 + w * bytesPerPixel)

/-- The output cap `pilean-probe zlib` uses. -/
def zlibCap : Nat := 1 <<< 28

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
    { name := "zlib: a bomb over the cap is refused without its output", kind := "zlib",
      bytes := pure (zerosZlib (zlibCap + 1)), expect := "error decompressed data exceeds",
      maxRss := baseRss + (8 <<< 20) },
    { name := "zlib: output at the cap is allocated once", kind := "zlib",
      bytes := pure (zerosZlib zlibCap), expect := s!"ok {zlibCap}",
      maxRss := baseRss + zlibCap + (8 <<< 20) },
    { name := "gif: a 4096 x 4096 frame from 11 KB of LZW", kind := "gif",
      bytes := IO.FS.readBinFile ("PILeanTest" / "png" / "lzw-zeros-4096.gif"),
      expect := "ok 4096x4096", maxRss := baseRss + 4096 * 4096 * (4 * 3 + 1) },
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
    { name := "graph: 20000 nodes, 40000 random edges", kind := "graph", bytes := pure .empty,
      argv := some #["graph", "sparse", "20000"], expect := "ok 20000 nodes",
      maxRss := 512 <<< 20, maxUserMs := 40000 }]

/-- Runs every case; each check says the child finished in time with the expected answer and
within its memory bound. -/
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
      let ok := run.status == some 0 && run.out.startsWith c.expect &&
        (run.rss.map (fun m => decide (m ≤ c.maxRss))).getD true &&
        (run.userMs.map (fun t => decide (t ≤ c.maxUserMs))).getD true
      r := r.push (s!"bounds: {c.name}", ok)
  finally
    IO.FS.removeDirAll scratch
  return r

end PILeanTest.Bounds
