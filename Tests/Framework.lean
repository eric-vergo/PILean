import PILean

/-!
# Test framework

Zero-dependency test harness: explicit suite registration (one line per
suite in `Tests/Main.lean` — no attribute magic), assertion helpers with
useful failure output (first-mismatch offsets, hex context, pixel
mismatch maps), and golden-file comparison with `UPDATE_GOLDEN=1`
regeneration.
-/

namespace Tests

open PILean

/-- One test: a name and an `IO` action that throws on failure. -/
structure TestCase where
  name : String
  run : IO Unit

/-- A named group of tests. Every work package owns one suite file. -/
structure Suite where
  name : String
  cases : List TestCase := []

/-- Build a test case. -/
def test (name : String) (act : IO Unit) : TestCase := ⟨name, act⟩

/-- Fail the current test. -/
def fail (msg : String) : IO α := throw (IO.userError msg)

/-- Assert a condition. -/
def assertTrue (cond : Bool) (msg : String := "assertion failed") : IO Unit :=
  unless cond do fail msg

/-- Assert equality, showing both values on failure. -/
def assertEq [BEq α] [Repr α] (actual expected : α) (label : String := "value") : IO Unit :=
  unless actual == expected do
    fail s!"{label}: expected {repr expected}, got {repr actual}"

/-- Two lowercase hex digits for a byte. -/
def hexByte (b : UInt8) : String :=
  let d (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  ("".push (d (b.toNat / 16))).push (d (b.toNat % 16))

/-- Space-separated hex dump of `len` bytes of `b` starting at `start`. -/
def hexDump (b : ByteArray) (start len : Nat) : String := Id.run do
  let stop := min b.size (start + len)
  let mut out := ""
  for i in [start:stop] do
    unless out.isEmpty do out := out.push ' '
    out := out ++ hexByte (b.get! i)
  return out

/-- Assert byte equality; on failure reports sizes, the first mismatching
offset, and hex context around it from both sides. -/
def assertBytesEq (actual expected : ByteArray) (label : String := "bytes") : IO Unit := do
  if actual.size != expected.size then
    fail s!"{label}: size mismatch — got {actual.size} bytes, expected {expected.size}"
  let mut firstBad : Option Nat := none
  for i in [0:actual.size] do
    if actual.get! i != expected.get! i then
      firstBad := some i
      break
  if let some i := firstBad then
    let lo := i - 8
    let n := min (actual.size - lo) 17
    fail (s!"{label}: first mismatch at offset {i}: " ++
      s!"got 0x{hexByte (actual.get! i)}, expected 0x{hexByte (expected.get! i)}\n" ++
      s!"  got      [{lo}…]: {hexDump actual lo n}\n" ++
      s!"  expected [{lo}…]: {hexDump expected lo n}")

/-- Assert pixel-exact image equality (size, mode, then pixels via RGBA
promotion). On failure reports the first mismatching pixel, the total
count, and a ≤ 32×32 ASCII map of mismatch locations. -/
def assertImagesEq (actual expected : Image) (label : String := "image") : IO Unit := do
  unless actual.width == expected.width && actual.height == expected.height do
    fail (s!"{label}: size mismatch — got {actual.width}×{actual.height}, " ++
      s!"expected {expected.width}×{expected.height}")
  unless actual.mode == expected.mode do
    fail s!"{label}: mode mismatch — got {actual.mode}, expected {expected.mode}"
  let w := actual.width
  let h := actual.height
  let cols := min 32 w
  let rows := min 32 h
  let mut grid : Array Bool := Array.replicate (cols * rows) false
  let mut mismatches := 0
  let mut first : Option (Nat × Nat × Color × Color) := none
  for y in [0:h] do
    for x in [0:w] do
      let ca := actual.getPixel! x y
      let ce := expected.getPixel! x y
      unless ca == ce do
        mismatches := mismatches + 1
        if first.isNone then first := some (x, y, ca, ce)
        if cols > 0 && rows > 0 then
          let gi := (y * rows / h) * cols + (x * cols / w)
          grid := grid.set! gi true
  if let some (fx, fy, ca, ce) := first then
    let mut map := ""
    for r in [0:rows] do
      map := map.push '\n' ++ "  "
      for c in [0:cols] do
        map := map.push (if grid[r * cols + c]! then 'X' else '·')
    fail (s!"{label}: {mismatches} mismatching pixels of {w * h}; " ++
      s!"first at ({fx}, {fy}): got {repr ca}, expected {repr ce}\n" ++
      s!"  mismatch map ({cols}×{rows}):{map}")

/-- Directory of committed golden fixtures. -/
def goldenDir : System.FilePath := System.FilePath.mk "tests" / "golden"

/-- Compare `actual` against the committed fixture `tests/golden/<name>`.
With `UPDATE_GOLDEN=1` the fixture is (re)written instead and the test
passes. A missing fixture without the env var fails with instructions. -/
def golden (name : String) (actual : ByteArray) : IO Unit := do
  let path := goldenDir / name
  match ← IO.getEnv "UPDATE_GOLDEN" with
  | some "1" =>
    if let some d := path.parent then IO.FS.createDirAll d
    IO.FS.writeBinFile path actual
    IO.println s!"       [golden updated: {path}]"
  | _ =>
    unless ← path.pathExists do
      fail s!"golden fixture missing: {path} — run with UPDATE_GOLDEN=1 to create it"
    let expected ← IO.FS.readBinFile path
    assertBytesEq actual expected s!"golden {name}"

/-- Does `sub` occur in `s`? -/
def strContains (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Run every suite (honoring `--filter substring`), print results, and
return the number of failures as the exit code (0 = success). -/
def runAll (suites : List Suite) (args : List String := []) : IO UInt32 := do
  let filter := match args with
    | "--filter" :: f :: _ => some f
    | _ => none
  let mut passed := 0
  let mut failed := 0
  let mut skippedSuites := 0
  for s in suites do
    let cases := match filter with
      | some f => s.cases.filter fun (tc : TestCase) => strContains s!"{s.name}/{tc.name}" f
      | none => s.cases
    if cases.isEmpty then
      skippedSuites := skippedSuites + 1
    else
      IO.println s!"{s.name}:"
      for tc in cases do
        try
          tc.run
          passed := passed + 1
          IO.println s!"  ok   {tc.name}"
        catch e =>
          failed := failed + 1
          IO.println s!"  FAIL {tc.name}"
          IO.println s!"       {e}"
  IO.println s!"\n{passed} passed, {failed} failed"
  return UInt32.ofNat (min failed 255)

end Tests
