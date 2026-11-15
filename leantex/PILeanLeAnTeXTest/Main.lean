/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanLeAnTeX
import PILeanTest.Bounds

/-!
# The test driver

`lake test` (from this folder) loads the engine from LeAnTeX's fonts and checks:

* **goldens**: every file of `PILeanLeAnTeX.Examples.files` is byte for byte its file in
  `examples/`, and drawing it twice gives the same bytes; `lake exe pilean-leantex-test --update`
  rewrites the goldens;
* **SVG**: the gallery's SVG documents have no `text` element and are inert
  (`PILean.Svg.isInert`), also with a source record;
* **the engine**: measurements scale with the size, bold is wider, the shapes lie where the
  measurement says, strings LeAnTeX rejects are drawn by the lettering;
* **trust**: the engine's identity names the pinned revision and every font file, a changed font
  byte changes it, and the fingerprint of an output changes with the engine;
* **the pin**: `leantexRevision` is the revision of `lake-manifest.json` and `lakefile.lean`;
* **bounds**: hostile labels drawn by `pilean-leantex-probe` in child processes under a CPU limit,
  a wall-clock limit and a memory bound (`PILeanTest.Bounds.runLimited`).
-/

open PILean PILean.Plot PILeanLeAnTeX

namespace PILeanLeAnTeXTest

/-- Whether `s` contains `t`. -/
def has (s t : String) : Bool := (s.splitOn t).length > 1

/-- The checks on the engine itself. -/
def engineChecks (e : TextEngine) (fonts : LeAnTeX.Backend.Fonts) : Array (String × Bool) :=
  let w10 := e.measure "$x^2 + y^2$" 10
  let w20 := e.measure "$x^2 + y^2$" 20
  let shp := e.shape "Mass $m$" 20 1
  let bold := e.shape "Mass $m$" 20 1.5
  let box := shp.fill.bounds
  let rejected := "$\\frac{1}{"
  #[("engine: a formula has a width", w10 > 0),
    ("engine: the width scales with the size", (w20 - 2 * w10).abs < 1e-6),
    ("engine: bold is set in another font", shp.fill != bold.fill),
    ("engine: shapes are outlines to fill, not strokes", shp.strokes.cmds.isEmpty &&
      !shp.fill.cmds.isEmpty),
    ("engine: the shape lies within the measured width and the ascent and descent",
      match box with
      | some b => b.x0 > -1 && b.x1 < e.measure "Mass $m$" 20 + 1 &&
          b.y0 > -20 * (e.ascent + 0.1) && b.y1 < 20 * (e.descent + 0.1)
      | none => false),
    ("engine: not native, with an identity", !e.native && has e.id leantexRevision),
    ("engine: a rejected string is drawn by the lettering",
      (typesetLabel fonts rejected false).isOk == false &&
        e.measure rejected 16 == TextEngine.lettering.measure rejected 16 &&
        (e.shape rejected 16 1).strokes == (TextEngine.lettering.shape rejected 16 1).strokes),
    ("engine: a string over the cap is cut for the lettering",
      let long := String.ofList (List.replicate (maxLabel + 50) 'M')
      e.measure long 10 == TextEngine.lettering.measure (fallbackText long) 10 &&
        (fallbackText long).length == maxLabel + 1),
    ("engine: plain text, ligatures and Unicode minus set by LeAnTeX",
      (typesetLabel fonts "office −1.5" false).isOk)]

/-- The trust checks: the engine's identity and the fingerprints. -/
def trustChecks (e : TextEngine) : Array (String × Bool) :=
  let bytes := [("A.otf", "abc".toUTF8), ("B.otf", "def".toUTF8)]
  let changed := [("A.otf", "abc".toUTF8), ("B.otf", "deg".toUTF8)]
  let fig : Figure := { Examples.basel with style := { Style.light with text := e } }
  let plain : Figure := Examples.basel
  let outs := Trust.ToOutputs.outputs fig
  let src : Trust.SourceData :=
    { module := "M", decl := "d", file := "M.lean", line := 1, column := 0,
      sourceHash := String.ofList (List.replicate 64 'a') }
  let entry : Trust.FigureEntry := { src with outputs := fun _ => outs }
  let fp := fun (o : Trust.Output) => (entry.source o).fingerprint
  #[("trust: the identity changes with a font byte", engineId bytes != engineId changed),
    ("trust: the identity names the revision and the fonts",
      has (engineId bytes) leantexRevision && has (engineId bytes) "B.otf"),
    ("trust: outputs record the engine", outs.all (·.textEngine == e.id) &&
      (Trust.ToOutputs.outputs plain).all (·.textEngine.isEmpty)),
    ("trust: the renderer of the engine is not the lettering's",
      Trust.rendererWith e.id != Trust.rendererId && Trust.rendererWith "" == Trust.rendererId),
    ("trust: the fingerprint covers the engine",
      match outs[0]? with
      | some o => fp o != fp { o with textEngine := e.id ++ "x" } &&
          fp o != fp { o with textEngine := "" }
      | none => false)]

/-- Compares the gallery with `examples/` (or rewrites it with `update`). -/
def goldenChecks (e : TextEngine) (update : Bool) : IO (Array (String × Bool)) := do
  let mut r : Array (String × Bool) := #[]
  let first := Examples.files e
  let again := Examples.files e
  for i in [0:first.size] do
    let (name, bytes) := first[i]!
    let f := System.FilePath.mk "examples" / name
    let second : Except String ByteArray := (again[i]?.map (·.2)).getD (.error "missing")
    match bytes, second with
    | .ok b, .ok b2 =>
      r := r.push (s!"deterministic: {name}", b == b2)
      if update then
        IO.FS.writeBinFile f b
      else
        let old ← try IO.FS.readBinFile f catch _ => pure .empty
        r := r.push (s!"golden: {name}", old == b)
      if name.endsWith ".svg" then
        let svg := String.fromUTF8! b
        let s : Trust.Source :=
          { module := "PILeanLeAnTeX.Examples", decl := "basel",
            file := "PILeanLeAnTeX/Examples.lean", line := 1, column := 0,
            version := PILean.version }
        r := r.push (s!"svg: {name} has no text element and is inert",
          !has svg "<text" && Svg.isInert svg &&
            (match Trust.withSourceSvg svg s with | .ok t => Svg.isInert t | .error _ => false))
    | _, _ => r := r.push (s!"golden: {name} drawn", false)
  return r

/-- `leantexRevision` against the pins of `lake-manifest.json` and `lakefile.lean`. -/
def pinChecks : IO (Array (String × Bool)) := do
  let manifest ← IO.FS.readFile "lake-manifest.json"
  let lakefile ← IO.FS.readFile "lakefile.lean"
  return #[("pin: lake-manifest.json has the revision",
      has manifest s!"\"rev\": \"{leantexRevision}\""),
    ("pin: lakefile.lean requires the revision", has lakefile s!"\"{leantexRevision}\"")]

/-- A hostile label case: the probe's kind, the start of the expected output, the memory bound in
bytes and the CPU bound in milliseconds. -/
structure Case where
  /-- The kind `pilean-leantex-probe` is given. -/
  kind : String
  /-- The start of the expected output. -/
  expect : String
  /-- The bound on peak memory. -/
  maxRss : Nat := 768 <<< 20
  /-- The bound on user CPU time. -/
  maxUserMs : Nat := 20000

/-- The hostile labels (`PILeanLeAnTeXTest/Probe.lean` makes them). -/
def cases : Array Case :=
  #[{ kind := "recursive-macro", expect := "ok" }, { kind := "newcommand-bomb", expect := "ok" },
    { kind := "math-macro", expect := "ok" }, { kind := "deep-groups", expect := "ok" },
    { kind := "deep-scripts", expect := "ok" }, { kind := "deep-fractions", expect := "ok" },
    { kind := "long", expect := "ok" }, { kind := "too-long", expect := "ok" },
    { kind := "huge-rule", expect := "ok" }, { kind := "huge-math-size", expect := "ok" },
    { kind := "unbalanced", expect := "ok" }, { kind := "controls", expect := "ok" },
    { kind := "markup", expect := "ok" }, { kind := "many-formulas", expect := "ok" }]

/-- Runs every hostile case in a child under limits; each passes when the child ends in time with
`ok`, an inert SVG, within its memory and CPU bounds. -/
def boundChecks : IO (Array (String × Bool)) := do
  let scratch ← IO.FS.createTempDir
  let mut r := #[]
  try
    for c in cases do
      let run ← PILeanTest.Bounds.runLimited "pilean-leantex-probe" #[c.kind] 60 120000 scratch
      let mem := match run.rss with
        | some m => s!"{m / 1048576} MiB (bound {c.maxRss / 1048576} MiB)"
        | none => "memory not measured"
      let cpu := match run.userMs with | some t => s!"{t} ms" | none => "?"
      IO.println s!"bounds: {c.kind}: {run.out}; {mem}; user {cpu}"
      let ok := run.status == some 0 && run.out.startsWith c.expect &&
        has run.out "inert true" &&
        (run.rss.map (fun m => decide (m ≤ c.maxRss))).getD true &&
        (run.userMs.map (fun t => decide (t ≤ c.maxUserMs))).getD true
      r := r.push (s!"bounds: {c.kind}", ok)
  finally
    IO.FS.removeDirAll scratch
  return r

end PILeanLeAnTeXTest

open PILeanLeAnTeXTest in
/-- Runs the checks; exit status 1 if any fails. -/
def main (args : List String) : IO UInt32 := do
  let update := args == ["--update"]
  let (fonts, missing) ← LeAnTeX.Backend.Fonts.load defaultFontDir
  if !missing.isEmpty then
    IO.eprintln s!"FAIL fonts: {missing}"
    return 1
  let .ok e ← load | IO.eprintln "FAIL engine"; return 1
  let mut all := engineChecks e fonts ++ trustChecks e
  all := all ++ (← goldenChecks e update) ++ (← pinChecks)
  if !update then all := all ++ (← boundChecks)
  let mut failed := 0
  for (name, ok) in all do
    if ok then IO.println s!"ok {name}" else
      IO.println s!"FAIL {name}"
      failed := failed + 1
  IO.println s!"{all.size - failed} of {all.size} checks pass"
  return if failed == 0 then 0 else 1
