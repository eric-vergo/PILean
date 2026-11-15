/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanMathlibTest.Files

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
* **the pin**: `lakefile.lean` and `lake-manifest.json` name the same Mathlib revision.

None of these is a theorem.
-/

open PILean PILean.Plot PILeanMathlib.Examples

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
  let rev := "56a005855ea17e0b0958f73ec801ae140b0a1679"
  let lakefile ← (IO.FS.readFile "lakefile.lean") <|> pure ""
  let manifest ← (IO.FS.readFile "lake-manifest.json") <|> pure ""
  return #[("pin: lakefile.lean and lake-manifest.json name the same Mathlib revision",
    has lakefile rev && has manifest s!"\"rev\": \"{rev}\"")]

end PILeanMathlibTest

open PILeanMathlibTest in
/-- Runs the checks; `--update` rewrites the goldens. -/
def main (args : List String) : IO UInt32 := do
  let all := floatChecks ++ (← goldenChecks (args == ["--update"])) ++ (← pinChecks)
  let mut failed := 0
  for (name, ok) in all do
    if ok then IO.println s!"ok {name}" else
      IO.println s!"FAIL {name}"
      failed := failed + 1
  IO.println s!"{all.size - failed} of {all.size} checks pass"
  return if failed == 0 then 0 else 1
