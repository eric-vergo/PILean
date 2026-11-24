/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanMathlibTest.Files
import PILeanMathlibTest.Mutations

/-!
# The test driver

`lake test` (from this folder) builds the library, and with it the theorems, and then checks what
the theorems do not cover:

* **goldens**: every file of `PILeanMathlibTest.files` is byte for byte its file in `examples/`,
  and drawing it twice gives the same bytes; `lake exe pilean-mathlib-test --update` rewrites
  the goldens;
* **floating point**: the 97 points of the figure's series, which are floating-point numbers,
  have the abscissae `-3 + k / 16`, lie within `1e-6` of the platform's `Float.sin`, the
  midpoints of consecutive points lie within `1 / 2000` of it, and every point has a position
  on the page;
* **pixels**: one unit of the ordinate is 143.5 pixels at the gallery size, the number the
  documents use to state the bound in pixels;
* **certified plots**: the points of the plots of the exponential, the cosine, the logarithm, the
  arctangent and the square root are as many as the grid's, within `1e-6` of the platform's
  function, their midpoints within the proved bound of it, and each bound under a quarter of a
  pixel at the gallery size;
* **the pin**: `lakefile.lean` and `lake-manifest.json` name the same Mathlib revision;
* **the diagrams**: the combinatorial figures, those of algebra and those of number theory pass
  the layout checks of plane figures in both themes;
* **the changes**: changes to the figures of number theory each break their theorem
  (`PILeanMathlibTest.Mutations`);
* **the modules**: every file below `PILeanMathlib/` on disk is imported by
  `PILeanMathlib/Axioms.lean`, whose axiom check covers the modules it imports, so a new file is
  reported even when that module's build comes from the cache.

None of these is a theorem.
-/

open PILean PILean.Plot PILeanMathlib PILeanMathlib.Examples

namespace PILeanMathlibTest

/-- Whether `s` contains `t`. -/
def has (s t : String) : Bool := (s.splitOn t).length > 1

/-- The checks on the floating-point points of the figure and on its page. -/
def floatChecks : Array (String × Bool) :=
  let ps := sineSeries.points
  let pairs := ps.toList.zip (ps.toList.drop 1)
  #[("points: 97 of them, from -3 to 3 in steps of 1/16",
      ps.size == 97 && (List.range 97).all fun k =>
        (ps[k]?.map (·.x)) == some (-3 + k.toFloat / 16)),
    ("points: within 1e-6 of the platform's sine",
      ps.all fun p => (p.y - Float.sin p.x).abs ≤ 1e-6),
    ("segments: the midpoints are within 1/2000 of the platform's sine",
      pairs.all fun (p, q) => ((p.y + q.y) / 2 - Float.sin ((p.x + q.x) / 2)).abs ≤ 1 / 2000),
    ("page: every point has a position on the panel",
      match sineFigure.layout[0]? with
      | some l => ps.all fun p => (l.pos p).isSome
      | none => false),
    ("pixels: one unit of the ordinate is 143.5 pixels, so 1/2000 is under a tenth of a pixel",
      pixelsPerUnit == 143.5 && pixelsPerUnit / 2000 < 0.1)]

/-- The certified plots with the platform's floating-point function of each. -/
def certified : Array (CertifiedPlot × (Float → Float)) :=
  #[(expPlot, Float.exp), (cosPlot, Float.cos), (logPlot, Float.log), (arctanPlot, Float.atan),
    (sqrtPlot, Float.sqrt)]

/-- The checks on the floating-point points of the certified plots and on their pages: the
points are `steps + 1`, within `1e-6` of the platform's function, the midpoints of consecutive
points within the proved bound of it, and the bound is under a tenth of a pixel in the gallery's
picture (640 × 400 pixels; the bound times the pixels per unit of the vertical axis, printed). -/
def certifiedChecks : IO (Array (String × Bool)) := do
  let mut out := #[]
  for (c, f) in certified do
    let ps := c.series.points
    let pairs := ps.toList.zip (ps.toList.drop 1)
    let d := PILean.Exact.toFloat c.delta
    let ppu := pixelsPerUnitOf c.figure
    IO.println s!"{c.name}: the bound {c.delta} is {d * ppu} pixels at the gallery size \
      ({ppu} pixels per unit)"
    out := out ++ #[
      (s!"{c.name}: {c.steps + 1} points", ps.size == c.steps + 1),
      (s!"{c.name}: the points are within 1e-6 of the platform's function",
        ps.all fun p => (p.y - f p.x).abs ≤ 1e-6),
      (s!"{c.name}: the midpoints are within {c.delta} of the platform's function",
        pairs.all fun (p, q) => ((p.y + q.y) / 2 - f ((p.x + q.x) / 2)).abs ≤ d),
      (s!"{c.name}: the bound is under a tenth of a pixel",
        ppu > 0 && d * ppu < 0.1 && c.figure.width == 640 && c.figure.height == 400)]
  return out

/-- The golden checks: each file is its file in `examples/` and is drawn the same twice; with
`update`, the files are rewritten. -/
def goldenChecks (update : Bool) : IO (Array (String × Bool)) := do
  let mut out := #[]
  let again := files
  for h : i in [0:files.size] do
    let (name, bytes) := files[i]
    match bytes with
    | .error m => out := out.push (s!"golden {name}: {m}", false)
    | .ok b =>
      let path : System.FilePath := "examples" / name
      if update then IO.FS.writeBinFile path b
      let same ← (do pure ((← IO.FS.readBinFile path) == b)) <|> pure false
      out := out.push (s!"golden examples/{name}", same)
      out := out.push (s!"deterministic {name}", match again[i]? with
        | some (_, .ok b') => b' == b
        | _ => false)
  return out

/-- The Mathlib revision of `lakefile.lean` is the one of `lake-manifest.json`. -/
def pinChecks : IO (Array (String × Bool)) := do
  let rev := "fc4f59e577feb1a4956671bc04ac18aaaf8cd842"
  let lakefile ← (IO.FS.readFile "lakefile.lean") <|> pure ""
  let manifest ← (IO.FS.readFile "lake-manifest.json") <|> pure ""
  return #[("pin: lakefile.lean and lake-manifest.json name the same Mathlib revision",
    has lakefile rev && has manifest s!"\"rev\": \"{rev}\"")]

/-- Every file below `PILeanMathlib/` but `PILeanMathlib/Axioms.lean` is named by an `import`
line of `PILeanMathlib/Axioms.lean`. -/
def moduleChecks : IO (Array (String × Bool)) := do
  let mods ← (PILean.Trust.modulesBelow "PILeanMathlib" `PILeanMathlib) <|> pure #[]
  let axioms ← (IO.FS.readFile ("PILeanMathlib" / "Axioms.lean")) <|> pure ""
  let imports := (axioms.splitOn "\n").filterMap fun l =>
    if l.startsWith "import " then some (l.drop 7).trimAscii.toString else none
  let missing := mods.filter fun m =>
    m != `PILeanMathlib.Axioms && !imports.contains m.toString
  unless missing.isEmpty do
    IO.eprintln s!"modules below PILeanMathlib/ that the axiom check does not import: {missing}"
  return #[("modules: every file below PILeanMathlib/ is imported by the axiom check",
    !mods.isEmpty && missing.isEmpty)]

/-- The diagrams (combinatorics, algebra, number theory) pass the layout checks of plane figures
in both themes (the points of a plot as `PILean.Diagram.plotProblems` checks them). -/
def diagramChecks : Array (String × Bool) :=
  diagrams.flatMap fun (n, d) =>
    let light := PILean.Diagram.plotProblems d.toPlane
    let dark := PILean.Diagram.plotProblems d.dark.toPlane
    #[(s!"layout checks: {n} has no problems {light}", light.isEmpty),
      (s!"layout checks: {n}-dark has no problems {dark}", dark.isEmpty)]

end PILeanMathlibTest

open PILeanMathlibTest in
/-- Runs the checks; `--update` rewrites the goldens. -/
def main (args : List String) : IO UInt32 := do
  let all := floatChecks ++ (← certifiedChecks) ++ (← goldenChecks (args == ["--update"])) ++
    (← pinChecks) ++
    (← moduleChecks) ++ diagramChecks ++ (← Mutations.ioChecks)
  let mut failed := 0
  for (name, ok) in all do
    if ok then IO.println s!"ok {name}" else
      IO.println s!"FAIL {name}"
      failed := failed + 1
  IO.println s!"{all.size - failed} of {all.size} checks pass"
  return if failed == 0 then 0 else 1
