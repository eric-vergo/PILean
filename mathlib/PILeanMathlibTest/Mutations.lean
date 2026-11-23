/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanTest.SpecMutations

/-!
# Changes to the figures of number theory that must break their theorems

The figures live in a module without Mathlib (`PILeanMathlib/Examples/NumberTheoryFigures.lean`)
and their theorems in one that imports it (`PILeanMathlib/Examples/NumberTheory.lean`). A change
to a figure is checked on one file that joins the two: the imports of both (but the figures'
module), then the figures, then the theorems. The change is made in the figures' part by the core's
`SpecMutation.apply`, and the joined file is compiled with the `lean` of the build (`LEAN`, which
`lake test` sets, with Mathlib on its path). A change passes when the unchanged joined file
compiles, and the changed one fails with no error in the figures' part and at least one inside the
named theorem, from its docstring to its `figure_proves` line (a lemma the theorem uses may fail
first, which then fails the theorem's link).

## Main definitions

* `joined`, `checkJoined`, `numberTheoryMutations`, `ioChecks`.
-/

namespace PILeanMathlibTest.Mutations

open PILeanTest.SpecMutations

/-- The figures' module, relative to this package's root. -/
def figuresFile : System.FilePath := "PILeanMathlib" / "Examples" / "NumberTheoryFigures.lean"

/-- The theorems' module, relative to this package's root. -/
def theoremsFile : System.FilePath := "PILeanMathlib" / "Examples" / "NumberTheory.lean"

/-- The import lines of a file and the rest of it. -/
def splitImports (text : String) : List String × List String :=
  let ls := text.splitOn "\n"
  (ls.filter (·.startsWith "import "), ls.filter fun l => !l.startsWith "import ")

/-- The joined file: the imports of both files but the figures' module, the figures' text, the
theorems' text; and the line (from 1) where the theorems' text begins. -/
def joined (figures theorems : String) : String × Nat :=
  let (fi, fb) := splitImports figures
  let (ti, tb) := splitImports theorems
  let imports := (fi ++ ti.filter (· != "import PILeanMathlib.Examples.NumberTheoryFigures"))
    |>.eraseDups
  let head := imports ++ fb
  ("\n".intercalate (head ++ tb), head.length + 1)

/-- Whether the change breaks the theorem `m.spec` and nothing in the figures: the changed
joined file fails with no error before `start` (the figures' part) and at least one in the
theorem's lines. The copy is written to `scratch`. -/
def checkJoined (lean : String) (scratch : System.FilePath) (text : String) (start : Nat)
    (m : SpecMutation) (k : Nat) : IO (Except String Unit) := do
  let mutated ← match m.apply text with
    | .ok t => pure t
    | .error e => return .error e
  let some (lo, hi) := specLines mutated m.spec | return .error s!"no lines for {m.spec}"
  let changed := scratch / s!"NumberTheoryChanged{k}.lean"
  IO.FS.writeFile changed mutated
  let (c1, out1) ← compile lean changed
  let errs := errorLines out1 changed.toString
  if c1 == 0 || errs.isEmpty then return .error "the changed file compiles"
  if errs.any (· < start) then
    return .error s!"an error in the figures (before line {start}): errors at {errs}"
  if !errs.any (fun l => lo ≤ l && l ≤ hi) then
    return .error s!"no error inside {m.spec} (lines {lo} to {hi}): errors at {errs}"
  return .ok ()

/-- The changes to the figures of number theory that their theorems must catch: a value, a
range, a name, a curve, a marking, a text, a heading, a window, a period or a colour changed. -/
def numberTheoryMutations : Array SpecMutation :=
  let f : System.FilePath := "joined"
  #[{ file := f, what := "the totient counts the a ≤ n", anchor := "def totient' (n : Nat) : Nat :=",
      edits := [("(List.range n)", "(List.range (n + 1))")], spec := "totientFigure_spec" },
    { file := f, what := "the totient is plotted up to 99", anchor := "def totientPlot : SeqPlot :=",
      edits := [("hi := 100", "hi := 99")], spec := "totientFigure_spec" },
    { file := f, what := "the totient is named ϕ(n)", anchor := "def totientPlot : SeqPlot :=",
      edits := [("\"φ(n)\"", "\"ϕ(n)\"")], spec := "totientFigure_spec" },
    { file := f, what := "the divisors are counted from 2", anchor := "def divisorCount (n : Nat)",
      edits := [("(List.range' 1 n)", "(List.range' 2 n)")], spec := "divisorFigure_spec" },
    { file := f, what := "the prime count starts at 3", anchor := "def primeCountPlot : SeqPlot :=",
      edits := [("lo := 2", "lo := 3")], spec := "primeCountFigure_spec" },
    { file := f, what := "the comparison curve is n / (Hₙ - 2)",
      anchor := "def primeCountPlot : SeqPlot :=",
      edits := [("harmonic' n - 1", "harmonic' n - 2")], spec := "primeCountFigure_spec" },
    { file := f, what := "the spiral marks 1 as well", anchor := "def ulamPlot : CellPlot :=",
      edits := [("ulamCells 441 isPrime'", "ulamCells 441 (fun n => isPrime' n || n == 1)")],
      spec := "ulamFigure_spec" },
    { file := f, what := "the spiral stops at 440", anchor := "def ulamPlot : CellPlot :=",
      edits := [("ulamCells 441", "ulamCells 440")], spec := "ulamFigure_spec" },
    { file := f, what := "the cells of 0 are marked as residues", anchor := "def residueCell",
      edits := [("marked := legendre' p a == 1", "marked := legendre' p a != -1")],
      spec := "residueFigure_spec" },
    { file := f, what := "the symbols are written with a hyphen", anchor := "def residueCell",
      edits := [("text := symbolText (legendre' p a)", "text := toString (legendre' p a)")],
      spec := "residueFigure_spec" },
    { file := f, what := "the table has a row for 17", anchor := "def residuePrimes : List Nat",
      edits := [("[3, 5, 7, 11, 13]", "[3, 5, 7, 11, 13, 17]")], spec := "residueFigure_spec" },
    { file := f, what := "the residues are headed x", anchor := "def residuePlot : CellPlot where",
      edits := [("(\"a\", (-1, 3 / 2))", "(\"x\", (-1, 3 / 2))")], spec := "residueFigure_spec" },
    { file := f, what := "the primes 1 mod 4 count as Gaussian primes on the axes",
      anchor := "def gaussianPrime (a b : Int) : Bool :=",
      edits := [("k % 4 == 3", "k % 4 == 1")], spec := "gaussianFigure_spec" },
    { file := f, what := "the window loses its top row", anchor := "def gaussianLattice :",
      edits := [("hi := (7, 7)", "hi := (7, 6)")], spec := "gaussianFigure_spec" },
    { file := f, what := "the points that are not prime are drawn in the ink",
      anchor := "def gaussianLattice :",
      edits := [("plainInk := .faint", "plainInk := .ink")], spec := "gaussianFigure_spec" },
    { file := f, what := "the lattice's second period is (1/2, 3/4)", anchor := "def hexLattice :",
      edits := [("w2 := (1 / 2, 7 / 8)", "w2 := (1 / 2, 3 / 4)")], spec := "latticeFigure_spec" },
    { file := f, what := "the lattice's window ends at height 1", anchor := "def hexLattice :",
      edits := [("hi := (3, 2)", "hi := (3, 1)")], spec := "latticeFigure_spec" },
    { file := f, what := "the lattice marks its origin", anchor := "def hexLattice :",
      edits := [("hi := (3, 2) }", "hi := (3, 2), marked := fun m n => m == 0 && n == 0 }")],
      spec := "latticeFigure_spec" }]

/-- The most compilations run at once (each loads Mathlib). -/
def parallel : Nat := 5

/-- The checks of the changes, named `the change breaks SPEC: WHAT`, `parallel` at a time after
the unchanged joined file has compiled; without `LEAN` in the environment the check fails instead
of running a `lean` of unknown origin. -/
def ioChecks : IO (Array (String × Bool)) := do
  let some lean ← IO.getEnv "LEAN"
    | return #[("the changes to the figures of number theory are checked (LEAN is not set)",
        false)]
  let scratch ← IO.FS.createTempDir
  let (text, start) := joined (← IO.FS.readFile figuresFile) (← IO.FS.readFile theoremsFile)
  let plain := scratch / "NumberTheoryPlain.lean"
  IO.FS.writeFile plain text
  let (c0, out0) ← compile lean plain
  if c0 != 0 || !(errorLines out0 plain.toString).isEmpty then
    IO.eprintln s!"the joined file of number theory does not compile: {(out0.take 800).toString}"
    IO.FS.removeDirAll scratch
    return #[("the joined file of the figures of number theory and their theorems compiles",
      false)]
  let ms := numberTheoryMutations.zipIdx
  let mut out := #[("the joined file of the figures of number theory and their theorems compiles",
    true)]
  for g in [0:(ms.size + parallel - 1) / parallel] do
    let batch := ms.extract (g * parallel) ((g + 1) * parallel)
    let tasks ← batch.mapM fun (m, k) => IO.asTask (checkJoined lean scratch text start m k)
    for ((m, _), t) in batch.zip tasks do
      let name := s!"the change breaks {m.spec}: {m.what}"
      match t.get with
      | .ok (.ok ()) => out := out.push (name, true)
      | .ok (.error why) => IO.eprintln s!"{name}: {why}"; out := out.push (name, false)
      | .error e => IO.eprintln s!"{name}: {e}"; out := out.push (name, false)
  IO.FS.removeDirAll scratch
  return out

end PILeanMathlibTest.Mutations
