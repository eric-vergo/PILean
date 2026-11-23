/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# Changes to a figure that must break its specification

A figure's specification writes out what the figure draws, so that a change to the figure breaks
the build. `SpecMutation` describes one such change: edits to the source file of the figure, made
in its definitions (after an anchor and before the specification), and the specification they
must break. `check` compiles a copy of the file with the edits, with the `lean` of the build
(`LEAN`, which `lake test` sets), and holds when the copy fails to compile with every error inside
the specification or its `figure_proves` line, and the unchanged copy compiles. The changes of
the core's figures are `mutations`; the LeAnTeX package checks its own with the same `check`.

## Main definitions

* `SpecMutation`, `SpecMutation.apply`, `errorLines`, `specLines`, `check`, `checkAll`,
  `diagramMutations`, `algebraMutations`, `numberMutations`, `explorerMutations`, `complexMutations`, `mutations`,
  `ioChecks`.
-/

namespace PILeanTest.SpecMutations

/-- A change to the definitions of a figure that its specification must catch. -/
structure SpecMutation where
  /-- The source file, relative to the package's root. -/
  file : System.FilePath
  /-- What the change does, as the check names it. -/
  what : String
  /-- The text after which the edits are made: it occurs once in the file, before the
  specification. -/
  anchor : String
  /-- Each edit replaces the first occurrence of its first text after the anchor with its
  second; every occurrence replaced must end before the specification. -/
  edits : List (String × String)
  /-- The name of the specification, as written after `theorem`. -/
  spec : String

/-- The byte position of the first occurrence of `pat` in `s` at or after `start`. -/
def findFrom (s pat : String) (start : Nat) : Option Nat := Id.run do
  let b := s.toUTF8
  let p := pat.toUTF8
  if p.size == 0 then return none
  let mut i := start
  while i + p.size ≤ b.size do
    if (List.range p.size).all fun k => b[i + k]! == p[k]! then return some i
    i := i + 1
  return none

/-- The number of occurrences of `pat` in `s`. -/
def occurrences (s pat : String) : Nat := (s.splitOn pat).length - 1

/-- The text of `s` between the byte positions `a` and `b`. -/
def slice (s : String) (a b : Nat) : String :=
  (String.fromUTF8? (s.toUTF8.extract a b)).getD ""

/-- The file's text with the edits made, or why they cannot be: the anchor or the specification
does not occur exactly once, an edit's text is not found after the anchor, or an edit would
reach into the specification. -/
def SpecMutation.apply (m : SpecMutation) (text : String) : Except String String := do
  if occurrences text m.anchor != 1 then throw s!"the anchor {m.anchor.quote} is not unique"
  let specHead := s!"theorem {m.spec} "
  if occurrences text specHead != 1 then throw s!"no single theorem {m.spec}"
  let mut t := text
  for (old, new) in m.edits do
    let some a := findFrom t m.anchor 0 | throw "the anchor is gone"
    let some sp := findFrom t specHead 0 | throw "the specification is gone"
    let some i := findFrom t old a | throw s!"{old.quote} does not occur after the anchor"
    if i + old.utf8ByteSize > sp then throw s!"{old.quote} is not before the specification"
    t := slice t 0 i ++ new ++ slice t (i + old.utf8ByteSize) t.utf8ByteSize
  return t

/-- The lines (from 1) of the errors in the output of `lean` for the file `path`. -/
def errorLines (out : String) (path : String) : Array Nat :=
  (out.splitOn "\n").toArray.filterMap fun l =>
    if l.startsWith (path ++ ":") then
      match ((l.drop (path.length + 1)).toString.splitOn ":") with
      | line :: _ :: rest => if (":".intercalate rest).trimAsciiStart.startsWith "error" then
          line.toNat? else none
      | _ => none
    else none

/-- The lines (from 1) of the specification in `text`: from its docstring (Lean reports an error
of the whole declaration there) or, without one, its `theorem` line, to the `figure_proves` line
that names it. -/
def specLines (text spec : String) : Option (Nat × Nat) := do
  let ls := (text.splitOn "\n").toArray
  let thm ← ls.findIdx? (·.startsWith s!"theorem {spec} ")
  let last ← ls.findIdx? fun l => l.startsWith "figure_proves " && l.endsWith s!" {spec}"
  let above := if thm = 0 then "" else (ls[thm - 1]!).trimAsciiEnd.toString
  let first := if above.endsWith "-/" then
      ((List.range thm).reverse.find? fun i => (ls[i]!).startsWith "/--").getD thm
    else thm
  return (first + 1, last + 1)

/-- Runs the `lean` of the build on a file; its exit code and its output. -/
def compile (lean : String) (path : System.FilePath) : IO (UInt32 × String) := do
  let r ← IO.Process.output { cmd := lean, args := #[path.toString] }
  return (r.exitCode, r.stdout ++ r.stderr)

/-- Whether the change breaks the specification and nothing else: the copy with the edits fails
to compile, with at least one error and every error inside the specification's lines; and the
copy without them compiles. The copies are written to `scratch`. -/
def check (lean : String) (scratch : System.FilePath) (m : SpecMutation) (k : Nat) :
    IO (Except String Unit) := do
  let text ← IO.FS.readFile m.file
  let mutated ← match m.apply text with
    | .ok t => pure t
    | .error e => return .error e
  let some (lo, hi) := specLines mutated m.spec | return .error s!"no lines for {m.spec}"
  let stem := (m.file.fileStem.getD "Spec")
  let plain := scratch / s!"{stem}Plain{k}.lean"
  let changed := scratch / s!"{stem}Changed{k}.lean"
  IO.FS.writeFile plain text
  IO.FS.writeFile changed mutated
  let (c0, out0) ← compile lean plain
  if c0 != 0 || !(errorLines out0 plain.toString).isEmpty then
    return .error s!"the unchanged copy does not compile: {(out0.take 400).toString}"
  let (c1, out1) ← compile lean changed
  let errs := errorLines out1 changed.toString
  if c1 == 0 || errs.isEmpty then return .error "the changed copy compiles"
  if errs.any (fun l => l < lo || l > hi) then
    return .error s!"an error outside {m.spec} (lines {lo} to {hi}): errors at {errs}"
  return .ok ()

/-- The checks of the changes, named `the change breaks SPEC: WHAT`, run side by side; each fails
with its reason printed. Without `LEAN` in the environment (set by `lake test` and `lake env`) the
check fails instead of running a `lean` of unknown origin. -/
def checkAll (ms : Array SpecMutation) : IO (Array (String × Bool)) := do
  let some lean ← IO.getEnv "LEAN"
    | return #[("the changes to the figures are checked (LEAN is not set)", false)]
  let scratch ← IO.FS.createTempDir
  let tasks ← ms.zipIdx.mapM fun (m, k) => IO.asTask (check lean scratch m k)
  let mut out := #[]
  for (m, t) in ms.zip tasks do
    let name := s!"the change breaks {m.spec}: {m.what}"
    match t.get with
    | .ok (.ok ()) => out := out.push (name, true)
    | .ok (.error why) => IO.eprintln s!"{name}: {why}"; out := out.push (name, false)
    | .error e => IO.eprintln s!"{name}: {e}"; out := out.push (name, false)
  IO.FS.removeDirAll scratch
  return out

/-- The changes to the data of the gallery's combinatorial diagrams (`PILeanTest/Diagrams.lean`)
that their specifications must catch: an edge, a cover, a cell, an entry, an incidence, a step or
a drawing changed. -/
def diagramMutations : Array SpecMutation :=
  let f : System.FilePath := "PILeanTest" / "Diagrams.lean"
  #[{ file := f, what := "the Petersen graph loses the condition on its last pair",
      anchor := "def petersenGraph : FinGraph where",
      edits := [("a != c && a != d && b != c && b != d", "a != c && a != d && b != c")],
      spec := "petersen_spec" },
    { file := f, what := "the subsets are ordered by size instead of inclusion",
      anchor := "def booleanLattice : FinPoset where",
      edits := [("le i j := i.val &&& j.val == i.val", "le i j := decide (i.val ≤ j.val)")],
      spec := "cube_spec" },
    { file := f, what := "the Young diagram has the shape (5, 3, 2, 1)",
      anchor := "def shape5331 : YoungShape", edits := [("[5, 3, 3, 1]", "[5, 3, 2, 1]")],
      spec := "young_spec" },
    { file := f, what := "an entry of the tableau is 3 instead of 4",
      anchor := "def ssyt : Tableau", edits := [("[[1, 1, 2, 4],", "[[1, 1, 2, 3],")],
      spec := "tableau_spec" },
    { file := f, what := "the wiring figure draws the matrix",
      anchor := "def permWiring : Diagram :=",
      edits := [("perm.figure FinPerm.wiring", "perm.figure FinPerm.matrix")],
      spec := "permWiring_spec" },
    { file := f, what := "vertex 11 hangs from vertex 6", anchor := "def treeParents :",
      edits := [("some 7, some 7]", "some 7, some 6]")], spec := "tree_spec" },
    { file := f, what := "the third set is the multiples of 7",
      anchor := "def multiples : SetSystem",
      edits := [("[2, 3, 5].map", "[2, 3, 7].map")], spec := "venn_spec" },
    { file := f, what := "a line of the Fano plane is changed",
      anchor := "def fanoPlane : SetSystem",
      edits := [("[2, 4, 5]]", "[2, 4, 6]]")], spec := "fano_spec" },
    { file := f, what := "the Dyck word ends with two downs", anchor := "def dyckWord : List Bool",
      edits := [("true, false]", "false, false]")], spec := "dyck_spec" },
    { file := f, what := "the board has the shape (4, 2, 1)", anchor := "def board : Polyomino",
      edits := [("[4, 3, 1]", "[4, 2, 1]")], spec := "ferrers_spec" }]

/-- The changes to the data of the gallery's diagrams of algebra
(`PILeanTest/AlgebraDiagrams.lean`) that their specifications must catch: a map, an arrow, a
generator, a name or a loop changed. -/
def algebraMutations : Array SpecMutation :=
  let f : System.FilePath := "PILeanTest" / "AlgebraDiagrams.lean"
  #[{ file := f, what := "the right map of the square reduces modulo 3",
      anchor := "def reductionMaps : FinMaps where",
      edits := [("reduction 6 2,", "reduction 6 3,")], spec := "square_spec" },
    { file := f, what := "the doubling sends 1 to 0, so it is not injective",
      anchor := "def exactMaps : FinMaps where",
      edits := [("#[0, 2]", "#[0, 0]")], spec := "exact_spec" },
    { file := f, what := "an edge of the cube joins ℤ/15 to ℤ/2",
      anchor := "def reductionCube : CommDiagram where",
      edits := [("{ src := 1, tgt := 4 }", "{ src := 1, tgt := 6 }")], spec := "cube_spec" },
    { file := f, what := "the names of (1 2) and (2 3) are exchanged", anchor := "def s3 : FinMagma",
      edits := [("\"(1 2)\", \"(2 3)\"", "\"(2 3)\", \"(1 2)\"")], spec := "cayleyTable_spec" },
    { file := f, what := "the Cayley graph is drawn for (1 3 2) instead of (1 2 3)",
      anchor := "def cayleyGraph : Diagram :=",
      edits := [("⟨4, by decide +kernel⟩] s3Positions", "⟨5, by decide +kernel⟩] s3Positions")],
      spec := "cayleyGraph_spec" },
    { file := f, what := "the loop is at the first vertex", anchor := "def quiverData : FinQuiver",
      edits := [("(2, 2, \"ℓ\")", "(0, 0, \"ℓ\")")], spec := "quiver_spec" }]

/-- The changes to the data of the gallery's plots, grids and lattices
(`PILeanTest/NumberDiagrams.lean`) that their specifications must catch: a value, a name, the
range, a marking, a text, a window, a period or a colour changed. -/
def numberMutations : Array SpecMutation :=
  let f : System.FilePath := "PILeanTest" / "NumberDiagrams.lean"
  #[{ file := f, what := "the totient counts the a ≤ n", anchor := "def phi (n : Nat) : Nat :=",
      edits := [("(List.range n)", "(List.range (n + 1))")], spec := "totient_spec" },
    { file := f, what := "the plot ends at 99", anchor := "def totientPlot : SeqPlot :=",
      edits := [("hi := 100", "hi := 99")], spec := "totient_spec" },
    { file := f, what := "the sequence is named ϕ(n)", anchor := "def totientPlot : SeqPlot :=",
      edits := [("\"φ(n)\"", "\"ϕ(n)\"")], spec := "totient_spec" },
    { file := f, what := "the plot gains a curve", anchor := "def totientPlot : SeqPlot :=",
      edits := [("fun n => phi n)] }", "fun n => phi n)], curves := [(\"n\", fun n => n)] }")],
      spec := "totient_spec" },
    { file := f, what := "1 counts as a prime", anchor := "def isPrime (n : Nat) : Bool :=",
      edits := [("2 ≤ n &&", "1 ≤ n &&")], spec := "sieve_spec" },
    { file := f, what := "each cell shows the number before its own", anchor := "def sievePlot :",
      edits := [("text := toString (i + 1)", "text := toString i")], spec := "sieve_spec" },
    { file := f, what := "the rows run from the bottom", anchor := "def sievePlot :",
      edits := [("-((i / 10 : Nat) : Int)", "((i / 10 : Nat) : Int)")], spec := "sieve_spec" },
    { file := f, what := "the primes 1 mod 4 count as Gaussian primes on the axes",
      anchor := "def gaussianPrime (a b : Int) : Bool :=",
      edits := [("k % 4 == 3", "k % 4 == 1")], spec := "gaussian_spec" },
    { file := f, what := "the window loses its lowest row", anchor := "def gaussianLattice :",
      edits := [("lo := (-4, -4)", "lo := (-4, -3)")], spec := "gaussian_spec" },
    { file := f, what := "the plain points are drawn in the ink", anchor := "def gaussianLattice :",
      edits := [("plainInk := .faint", "plainInk := .ink")], spec := "gaussian_spec" },
    { file := f, what := "the second period is (1/2, 5/4)", anchor := "def skewLattice :",
      edits := [("w2 := (1 / 2, 3 / 2)", "w2 := (1 / 2, 5 / 4)")], spec := "skew_spec" },
    { file := f, what := "the skew lattice marks its origin", anchor := "def skewLattice :",
      edits := [("hi := (3, 3) }", "hi := (3, 3), marked := fun m n => m == 0 && n == 0 }")],
      spec := "skew_spec" }]

/-- The changes to the proved explorers (`PILeanTest/Explorers.lean`) that their theorems must
catch: a value of a grid, the generator, the title, the window, the reference pairs. -/
def explorerMutations : Array SpecMutation :=
  let f : System.FilePath := "PILeanTest" / "Explorers.lean"
  #[{ file := f, what := "the moduli reach 13", anchor := "def moduli : ExplorerParam Nat :=",
      edits := [("11, 12]", "11, 12, 13]")], spec := "cayleyExplorer_spec" },
    { file := f, what := "the generator is a + 1", anchor := "def generator (n a : Nat)",
      edits := [("⟨a % n,", "⟨(a + 1) % n,")], spec := "cayleyExplorer_spec" },
    { file := f, what := "the title speaks of generators", anchor := "def cayleyDiagram (n a : Nat)",
      edits := [("for the generator {a}", "for the generators {a}")],
      spec := "cayleyExplorer_spec" },
    { file := f, what := "an involution's pairs drawn twice", anchor := "def cayleyPairs (n a : Nat)",
      edits := [("== 0 && !(g < t)", "== 1 && !(g < t)")], spec := "cayleyExplorer_spec" },
    { file := f, what := "the window loses a row", anchor := "def lattice (x y : Rat)",
      edits := [("lo := (-3, -2)", "lo := (-3, -1)")], spec := "latticeExplorer_spec" },
    { file := f, what := "the second period's x reaches 1", anchor := "def periodX :",
      edits := [("1 / 2, 3 / 4]", "1 / 2, 3 / 4, 1]")], spec := "latticeExplorer_spec" },
    { file := f, what := "the second period's y starts at 0 (dependent periods)",
      anchor := "def periodY :", edits := [("#[1 / 2,", "#[0, 1 / 2,")],
      spec := "latticeExplorer_spec" }]

/-- The changes to the zeros and poles of the rational function (`PILeanTest/ComplexDiagrams.lean`)
that its theorem must catch: a multiplicity, a zero, a coefficient, the window. -/
def complexMutations : Array SpecMutation :=
  let f : System.FilePath := "PILeanTest" / "ComplexDiagrams.lean"
  #[{ file := f, what := "the zero 1/2 is simple", anchor := "def rationalData : RationalPlot",
      edits := [("((1 / 2, 0), 2)]", "((1 / 2, 0), 1)]")], spec := "rationalFigure_spec" },
    { file := f, what := "the zero i is 2i", anchor := "def rationalData : RationalPlot",
      edits := [("((0, 1), 1),", "((0, 2), 1),")], spec := "rationalFigure_spec" },
    { file := f, what := "the pole −3/2 is −1/2", anchor := "def rationalData : RationalPlot",
      edits := [("((-3 / 2, 0), 1)]", "((-1 / 2, 0), 1)]")], spec := "rationalFigure_spec" },
    { file := f, what := "a coefficient of the numerator changed",
      anchor := "def rationalData : RationalPlot",
      edits := [("num := [1 / 4, -1,", "num := [1 / 4, -2,")], spec := "rationalFigure_spec" },
    { file := f, what := "the pole 1 − i left out", anchor := "def rationalData : RationalPlot",
      edits := [("((1, 1), 1), ((1, -1), 1),", "((1, 1), 1),")], spec := "rationalFigure_spec" },
    { file := f, what := "the window is narrower", anchor := "def rationalData : RationalPlot",
      edits := [("lo := (-2, -3 / 2)", "lo := (-1, -3 / 2)")], spec := "rationalFigure_spec" }]

/-- The changes to the core's figures with specifications (`PILeanTest.Examples` and
`PILeanTest.PlaneExact`), with those of the diagrams' galleries and the proved explorers. -/
def mutations : Array SpecMutation :=
  let disks : System.FilePath := "PILeanTest" / "Examples.lean"
  let plane : System.FilePath := "PILeanTest" / "PlaneExact.lean"
  #[{ file := disks, what := "the point E is not drawn", anchor := "def items : Array Item :=",
      edits := [("lowerCrossing, pointNegE, pointE,", "lowerCrossing, pointNegE,")],
      spec := "disks_spec" },
    { file := disks, what := "the label E is at -E", anchor := "def items : Array Item :=",
      edits := [("Plane.Exact.label \"E\" chordEnd", "Plane.Exact.label \"E\" (-chordEnd)")],
      spec := "disks_spec" },
    { file := disks, what := "the disks' colours are swapped", anchor := "def leftDisk : Item :=",
      edits := [("leftCentre critical |>.accent 0", "leftCentre critical |>.accent 1"),
        ("rightCentre critical |>.accent 1", "rightCentre critical |>.accent 0")],
      spec := "disks_spec" },
    { file := disks, what := "the angle mark's radius is 50 pixels",
      anchor := "def items : Array Item :=", edits := [("(some 46)", "(some 50)")],
      spec := "disks_spec" },
    { file := disks, what := "the upper crossing is a dot",
      anchor := "def upperCrossing : Item :=", edits := [("|>.marker .ring", "|>.marker .dot")],
      spec := "disks_spec" },
    { file := plane, what := "the point E is at 2E", anchor := "def items : Array Item :=",
      edits := [("pointZero, pointE,", "pointZero, Plane.Exact.point (E + E),")],
      spec := "reference_spec" },
    { file := plane, what := "the left circle's radius is 2", anchor := "def leftCircle : Item :=",
      edits := [("Plane.Exact.disk left R", "Plane.Exact.disk left (⟨⟨4, 0⟩⟩ : SqrtOf QSqrt5)")],
      spec := "reference_spec" },
    { file := plane, what := "the corners do not record the lens",
      anchor := "def cornerPoint (c : Zeta5) : Item :=",
      edits := [("\n    |>.incident .on \"the lens\"", "")], spec := "reference_spec" },
    { file := plane, what := "the first piece and its label are drawn in the other order",
      anchor := "def items : Array Item :=",
      edits := [("pieceS1, pieceLabel (-E) (-F) \"s1\" \"S₁\",",
        "pieceLabel (-E) (-F) \"s1\" \"S₁\", pieceS1,")], spec := "reference_spec" },
    { file := plane, what := "the second piece's label reads S₄",
      anchor := "def items : Array Item :=", edits := [("\"s2\" \"S₂\"", "\"s2\" \"S₄\"")],
      spec := "reference_spec" },
    { file := plane, what := "the steps are in accent 1", anchor := "def stepItems (j : Nat)",
      edits := [("then .accent 0 else", "then .accent 1 else")], spec := "zetaSteps_spec" },
    { file := plane, what := "the label of ζ² reads ζ2", anchor := "def stepLabel (j : Nat)",
      edits := [("\"ζ²\"", "\"ζ2\"")], spec := "zetaSteps_spec" },
    { file := plane, what := "the points do not record the window",
      anchor := "def stepPoint (j : Nat) : Item :=",
      edits := [("Plane.Exact.pointNearDisk (Zeta5.pow j) windowCentre windowRadius \"the window\"",
        "Plane.Exact.point (Zeta5.pow j)")], spec := "zetaSteps_spec" }] ++ diagramMutations ++
    algebraMutations ++ numberMutations ++ explorerMutations ++ complexMutations

/-- The checks of `mutations`. -/
def ioChecks : IO (Array (String × Bool)) := checkAll mutations

end PILeanTest.SpecMutations
