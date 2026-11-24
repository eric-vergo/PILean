/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanTest.SpecMutations

/-!
# Changes to the figures that must break their theorems

The figures live in a module without Mathlib (`PILeanMathlib/Examples/NumberTheoryFigures.lean`,
`PILeanMathlib/Examples/RealFigures.lean`) and their theorems in one that imports it
(`PILeanMathlib/Examples/NumberTheory.lean`, `PILeanMathlib/Examples/Real.lean`). A change
to a figure is checked on one file that joins the two: the imports of both (but the figures'
module), then the figures, then the theorems. The change is made in the figures' part by the core's
`SpecMutation.apply`, and the joined file is compiled with the `lean` of the build (`LEAN`, which
`lake test` sets, with Mathlib on its path). A change passes when the unchanged joined file
compiles, and the changed one fails with no error in the figures' part and at least one inside the
named theorem, from its docstring to its `figure_links` line (a lemma the theorem uses may fail
first, which then fails the theorem's link).

## Main definitions

* `Group`, `joined`, `checkJoined`, `numberTheoryMutations`, `realMutations`, `sineMutations`,
  `groups`,
  `ioChecks`.
-/

namespace PILeanMathlibTest.Mutations

open PILeanTest.SpecMutations

/-- A module of figures, the module of their theorems, and the changes to check. -/
structure Group where
  /-- What the figures are, as the checks name them. -/
  what : String
  /-- The figures' module file, relative to this package's root. -/
  figuresFile : System.FilePath
  /-- The figures' module name, as the theorems' module imports it. -/
  figuresModule : String
  /-- The theorems' module file, relative to this package's root. -/
  theoremsFile : System.FilePath
  /-- The changes. -/
  mutations : Array SpecMutation
  /-- Modules of the kind the figures are made with (file and module name), joined before the
  figures so that a change to the kind is checked too. -/
  kinds : List (System.FilePath × String) := []
  /-- The theorems of the figures' module (a module of the core, whose figures carry their own
  theorems) inside which a change may fail too; anywhere else in the figures' part an error fails
  the check. -/
  allowed : List String := []

/-- The import lines of a file and the rest of it. -/
def splitImports (text : String) : List String × List String :=
  let ls := text.splitOn "\n"
  (ls.filter (·.startsWith "import "), ls.filter fun l => !l.startsWith "import ")

/-- The joined file: the imports of the kinds' files (`kinds`, each a module name and its text),
of the figures and of the theorems but the joined modules themselves, then the kinds' texts, the
figures' text, the theorems' text; and the line (from 1) where the theorems' text begins. -/
def joined (figuresModule figures theorems : String) (kinds : List (String × String) := []) :
    String × Nat :=
  let own := figuresModule :: kinds.map (·.1)
  let parts := kinds.map (splitImports ·.2) ++ [splitImports figures]
  let (ti, tb) := splitImports theorems
  let imports := (parts.flatMap (·.1) ++ ti)
    |>.filter (fun l => !own.any (l == s!"import {·}")) |>.eraseDups
  let head := imports ++ parts.flatMap (·.2)
  ("\n".intercalate (head ++ tb), head.length + 1)

/-- Whether the change breaks the theorem `m.spec` and nothing in the figures: the changed
joined file fails with no error before `start` (the figures' part) and at least one in the
theorem's lines. The copy is written to `scratch`. -/
def checkJoined (lean : String) (scratch : System.FilePath) (text : String) (start : Nat)
    (m : SpecMutation) (k : Nat) (allowed : List String := []) : IO (Except String Unit) := do
  let mutated ← match m.apply text with
    | .ok t => pure t
    | .error e => return .error e
  let some (lo, hi) := specLines mutated m.spec | return .error s!"no lines for {m.spec}"
  let changed := scratch / s!"Changed{k}.lean"
  IO.FS.writeFile changed mutated
  let (c1, out1) ← compile lean changed
  let errs := errorLines out1 changed.toString
  if c1 == 0 || errs.isEmpty then return .error "the changed file compiles"
  let inAllowed := fun (l : Nat) =>
    allowed.any fun a => match specLines mutated a with
      | some (lo, hi) => lo ≤ l && l ≤ hi
      | none => false
  if errs.any (fun l => l < start && !inAllowed l) then
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
    { file := f, what := "the Gaussian figure's title says |a|, |b| ≤ 5",
      anchor := "def gaussianFigure : Diagram :=",
      edits := [("|a|, |b| ≤ 7\"", "|a|, |b| ≤ 5\"")], spec := "gaussianFigure_spec" },
    { file := f, what := "the residues' column numbers stand higher",
      anchor := "def residuePlot : CellPlot where",
      edits := [("((a : Rat) + 1 / 2, 3 / 2)", "((a : Rat) + 1 / 2, 5 / 2)")],
      spec := "residueFigure_spec" },
    { file := f, what := "the lattice's second period is (1/2, 3/4)", anchor := "def hexLattice :",
      edits := [("w2 := (1 / 2, 7 / 8)", "w2 := (1 / 2, 3 / 4)")], spec := "latticeFigure_spec" },
    { file := f, what := "the lattice's window ends at height 1", anchor := "def hexLattice :",
      edits := [("hi := (3, 2)", "hi := (3, 1)")], spec := "latticeFigure_spec" },
    { file := f, what := "the lattice marks its origin", anchor := "def hexLattice :",
      edits := [("hi := (3, 2) }", "hi := (3, 2), marked := fun m n => m == 0 && n == 0 }")],
      spec := "latticeFigure_spec" }]

/-- The changes to the certified plots of real functions that their theorems must catch: a
bound, an interval, a number of steps, a name, a coefficient or a number of terms changed, and
the kind's panel changed (a domain forced on an axis, a logarithmic axis). -/
def realMutations : Array SpecMutation :=
  let f : System.FilePath := "joined"
  #[{ file := f, what := "the exponential's bound is 1/2000", anchor := "def expPlot :",
      edits := [("delta := 1 / 1000", "delta := 1 / 2000")], spec := "expFigure_spec" },
    { file := f, what := "the exponential is plotted from -3", anchor := "def expPlot :",
      edits := [("lo := -2", "lo := -3")], spec := "expFigure_spec" },
    { file := f, what := "the exponential is named e^x", anchor := "def expPlot :",
      edits := [("name := \"exp x\"", "name := \"e^x\"")], spec := "expFigure_spec" },
    { file := f, what := "the exponential's curve is named a polynomial of degree 3",
      anchor := "def expPlot :",
      edits := [("degree 15\"", "degree 3\"")], spec := "expFigure_spec" },
    { file := f, what := "a coefficient of the cosine's polynomial is 1/25",
      anchor := "def cosTaylor (x : Rat) : Rat :=",
      edits := [("x ^ 4 / 24", "x ^ 4 / 25")], spec := "cosFigure_spec" },
    { file := f, what := "the cosine is sampled in 48 steps", anchor := "def cosPlot :",
      edits := [("steps := 96", "steps := 48")], spec := "cosFigure_spec" },
    { file := f, what := "the logarithm's series has 5 terms", anchor := "def logApprox",
      edits := [("-logSum 20 (1 - x)", "-logSum 5 (1 - x)")], spec := "logFigure_spec" },
    { file := f, what := "the arctangent's series has no signs", anchor := "def arctanSum :",
      edits := [("(-1) ^ n * x", "1 ^ n * x")], spec := "arctanFigure_spec" },
    { file := f, what := "the square roots have 6 binary digits", anchor := "def sqrtApprox",
      edits := [("(x * 4 ^ 30)", "(x * 4 ^ 6)"), ("/ 2 ^ 30", "/ 2 ^ 6")],
      spec := "sqrtFigure_spec" },
    { file := f, what := "the kind forces the y axis's domain to (0, 1)",
      anchor := "def figure (c : CertifiedPlot) : Figure where",
      edits := [("y := { label := \"y\" }", "y := { label := \"y\", domain := some (0, 1) }")],
      spec := "expFigure_spec",
      others := ["cosFigure_spec", "logFigure_spec", "arctanFigure_spec", "sqrtFigure_spec"] },
    { file := f, what := "the kind draws the x axis logarithmic",
      anchor := "def figure (c : CertifiedPlot) : Figure where",
      edits := [("x := { label := \"x\" }", "x := { label := \"x\", scale := .log }")],
      spec := "expFigure_spec",
      others := ["cosFigure_spec", "logFigure_spec", "arctanFigure_spec", "sqrtFigure_spec"] },
    { file := f, what := "the kind names the y axis f(x)",
      anchor := "def figure (c : CertifiedPlot) : Figure where",
      edits := [("y := { label := \"y\" }", "y := { label := \"f(x)\" }")],
      spec := "cosFigure_spec",
      others := ["expFigure_spec", "logFigure_spec", "arctanFigure_spec", "sqrtFigure_spec"] }]

/-- The changes to the combinatorial figures that their theorems must catch: a label that no
longer names its object, a mark added, a title that names another object, a colour role. -/
def combinatoricsMutations : Array SpecMutation :=
  let f : System.FilePath := "joined"
  #[{ file := f, what := "the Petersen graph's vertices are no longer named by their 2-subsets",
      anchor := "def kneserGraph : FinGraph where",
      edits := [("s!\"{a}{b}\"", "s!\"{a}{(b + 1) % 5}\"")], spec := "petersenFigure_spec" },
    { file := f, what := "an eleventh vertex with a name is drawn in the Petersen graph",
      anchor := "def petersenFigure : Diagram :=",
      edits := [("width := 340 }", "width := 340, marks := (kneserGraph.draw kneserLayout).marks \
          ++ [{ part := .vertex 10, shape := .dot (0, 0) }, \
          { part := .vertex 10, shape := .text \"55\" (0, 0) .auto }] }")],
      spec := "petersenFigure_spec" },
    { file := f, what := "the subsets' labels {0} and {1} are swapped",
      anchor := "def subsetOrder : FinPoset where",
      edits := [("\"{0}\", \"{1}\"", "\"{1}\", \"{0}\"")], spec := "subsetsFigure_spec" },
    { file := f, what := "the cell (0, 0) of the Young diagram is drawn a second time elsewhere",
      anchor := "def youngFigure : Diagram :=",
      edits := [("width := 220 }", "width := 220,
    marks := (YoungShape.mk [5, 3, 3, 1] .english).figure.marks ++
      [{ part := .cell 0 0, shape := .rect (5, -1) (6, 0) }] }")], spec := "youngFigure_spec" },
    { file := f, what := "the title of the cycle diagram states (1 5)(3 4)",
      anchor := "def cyclesFigure : Diagram :=",
      edits := [("(1 4)(3 5)", "(1 5)(3 4)")], spec := "cyclesFigure_spec" },
    { file := f, what := "the numbers of the Venn diagram are written one too low",
      anchor := "def multiples : SetSystem where",
      edits := [("toString (x + 1)).toArray", "toString x).toArray")], spec := "vennFigure_spec" },
    { file := f, what := "the divisors of 60 are labelled with half their value",
      anchor := "def divisorOrder : FinPoset where",
      edits := [("(divisors60.map toString)", "(divisors60.map fun d => toString (d / 2))")],
      spec := "divisorsFigure_spec" },
    { file := f, what := "the highest-weight tableau's title names the shape (5, 2, 1)",
      anchor := "def highestWeightFigure : Diagram :=",
      edits := [("shape (4, 3, 1)\"", "shape (5, 2, 1)\"")], spec := "highestWeightFigure_spec" },
    { file := f, what := "the set 5ℤ is named 7ℤ", anchor := "def multiples : SetSystem where",
      edits := [("\"5ℤ\"]", "\"7ℤ\"]")], spec := "vennFigure_spec" },
    { file := f, what := "the Dyck path's title spells another word",
      anchor := "def dyckFigure : Diagram :=",
      edits := [("Dyck word UUDUUDDDUD\"", "Dyck word UDUDUDUDUD\"")], spec := "dyckFigure_spec" },
    { file := f, what := "a strand of the wiring diagram is drawn in accent 2",
      anchor := "def wiringFigure : Diagram :=",
      edits := [("of 42513\" }", "of 42513\", marks := (sigma.figure FinPerm.wiring).marks.map \
          fun m => if m.part == .strand 0 then { m with ink := .accent 2 } else m }")],
      spec := "wiringFigure_spec" },
    { file := f, what := "the Petersen graph's title names another graph",
      anchor := "def petersenFigure : Diagram :=",
      edits := [("\"The Petersen graph\"", "\"The Heawood graph\"")],
      spec := "petersenFigure_spec" },
    { file := f, what := "the Petersen graph is drawn 360 pixels wide",
      anchor := "def petersenFigure : Diagram :=", edits := [("width := 340 }", "width := 360 }")],
      spec := "petersenFigure_spec" },
    { file := f, what := "the Petersen graph's inner star has radius 2/3",
      anchor := "def kneserLayout : Layout", edits := [("(1 / 2)", "(2 / 3)")],
      spec := "petersenFigure_spec" }]

/-- The changes to the figures of algebra that their theorems must catch: an object's name, two
arrows' labels exchanged, the generators' colours exchanged, a title, a name of the group's
elements. -/
def algebraMutations : Array SpecMutation :=
  let f : System.FilePath := "joined"
  #[{ file := f, what := "the object ℤ/6 of the square is labelled ℤ/5",
      anchor := "def squareObjects : Array String :=",
      edits := [("\"ℤ/12\", \"ℤ/6\"", "\"ℤ/12\", \"ℤ/5\"")], spec := "commSqFigure_spec" },
    { file := f, what := "the labels π₆ and π₄ of the square are swapped",
      anchor := "def squareLabels : Array String :=",
      edits := [("#[\"π₆\", \"π₄\"", "#[\"π₄\", \"π₆\"")], spec := "commSqFigure_spec" },
    { file := f, what := "the generators of the Cayley graph come in the other order",
      anchor := "def d4Generators : List (Fin d4Table.n) :=",
      edits := [("[⟨1, by decide⟩, ⟨4, by decide⟩]", "[⟨4, by decide⟩, ⟨1, by decide⟩]")],
      spec := "d4CayleyFigure_spec" },
    { file := f, what := "the title of the square names another category",
      anchor := "def commSqFigure : Diagram :=",
      edits := [("category of types\"", "category of sets\"")], spec := "commSqFigure_spec" },
    { file := f, what := "the Cayley graph's title names the generators s and r",
      anchor := "def d4CayleyFigure : Diagram :=",
      edits := [("for r and s\"", "for s and r\"")], spec := "d4CayleyFigure_spec" },
    { file := f, what := "the short exact sequence's middle object is named D",
      anchor := "def shortExactDiagram : CommDiagram where",
      edits := [("#[\"0\", \"A\", \"B\", \"C\", \"0\"]", "#[\"0\", \"A\", \"D\", \"C\", \"0\"]")],
      spec := "shortExactFigure_spec" },
    { file := f, what := "the subgroups' title says the normal ones are grey",
      anchor := "def d4SubgroupsFigure : Diagram :=",
      edits := [("normal ones in colour\"", "normal ones in grey\"")],
      spec := "d4SubgroupsFigure_spec" }]

/-- The changes to the zeros and poles of the rational function (`PILeanTest/ComplexDiagrams.lean`)
that the theorem in Mathlib's terms must catch: a multiplicity, a zero, the title, the label. -/
def complexMutations : Array SpecMutation :=
  let f : System.FilePath := "joined"
  #[{ file := f, what := "the zero 1/2 is simple", anchor := "def rationalData : RationalPlot",
      edits := [("((1 / 2, 0), 2)]", "((1 / 2, 0), 1)]")], spec := "rationalFigure_roots" },
    { file := f, what := "the pole −3/2 is −1/2", anchor := "def rationalData : RationalPlot",
      edits := [("((-3 / 2, 0), 1)]", "((-1 / 2, 0), 1)]")], spec := "rationalFigure_roots" },
    { file := f, what := "the title names another function", anchor := "def rationalFigure : Diagram",
      edits := [("(z + 3/2))\"", "(z + 1/2))\"")], spec := "rationalFigure_roots" }]

/-- The changes to the explorers that the theorems in Mathlib's terms must catch: a parameter's
name, a value of a grid, the generator, the window, a title. -/
def explorerMutations : Array SpecMutation :=
  let f : System.FilePath := "joined"
  #[{ file := f, what := "the slider's parameter is named m", anchor := "def moduli :",
      edits := [("name := \"n\"", "name := \"m\"")], spec := "cayleyExplorer_zmod" },
    { file := f, what := "the moduli reach 13", anchor := "def moduli :",
      edits := [("11, 12]", "11, 12, 13]")], spec := "cayleyExplorer_zmod" },
    { file := f, what := "the generator is a + 1", anchor := "def generator (n a : Nat)",
      edits := [("⟨a % n,", "⟨(a + 1) % n,")], spec := "cayleyExplorer_zmod" },
    { file := f, what := "the lattice's parameter y is named x", anchor := "def periodY :",
      edits := [("name := \"y\"", "name := \"x\"")], spec := "latticeExplorer_span" },
    { file := f, what := "the lattice's window loses a row", anchor := "def lattice (x y : Rat)",
      edits := [("lo := (-3, -2)", "lo := (-3, -1)")], spec := "latticeExplorer_span" },
    { file := f, what := "the lattice's title names the first period (0, 1)",
      anchor := "def latticeDiagram (x y : Rat)",
      edits := [("ℤ(1, 0) + ℤ({x}, {y})\" }", "ℤ(0, 1) + ℤ({x}, {y})\" }")],
      spec := "latticeExplorer_span" }]

/-- The changes to the sine's figure that its theorem must catch: the series' name, which is the
legend's text, an axis's name, the title, the number of steps. -/
def sineMutations : Array SpecMutation :=
  let f : System.FilePath := "joined"
  #[{ file := f, what := "the sine's legend says degree 17", anchor := "def sineSeries : Series",
      edits := [("degree 15\"", "degree 17\"")], spec := "sineFigure_spec" },
    { file := f, what := "the sine's x axis is named t", anchor := "def sineFigure : Figure where",
      edits := [("x := { label := \"x\" }", "x := { label := \"t\" }")],
      spec := "sineFigure_spec" },
    { file := f, what := "the sine's title says 98 samples", anchor := "def sineFigure : Figure where",
      edits := [("from 97 exact", "from 98 exact")], spec := "sineFigure_spec" }]

/-- The groups of figures and their changes. -/
def groups : Array Group :=
  #[{ what := "number theory",
      figuresFile := "PILeanMathlib" / "Examples" / "NumberTheoryFigures.lean",
      figuresModule := "PILeanMathlib.Examples.NumberTheoryFigures",
      theoremsFile := "PILeanMathlib" / "Examples" / "NumberTheory.lean",
      mutations := numberTheoryMutations },
    { what := "real functions",
      figuresFile := "PILeanMathlib" / "Examples" / "RealFigures.lean",
      figuresModule := "PILeanMathlib.Examples.RealFigures",
      theoremsFile := "PILeanMathlib" / "Examples" / "Real.lean",
      mutations := realMutations,
      kinds := [("PILeanMathlib" / "CertifiedPlot.lean", "PILeanMathlib.CertifiedPlot"),
        ("PILeanMathlib" / "CertifiedPlotBound.lean", "PILeanMathlib.CertifiedPlotBound")] },
    { what := "the sine",
      figuresFile := "PILeanMathlib" / "Examples" / "SineFigure.lean",
      figuresModule := "PILeanMathlib.Examples.SineFigure",
      theoremsFile := "PILeanMathlib" / "Examples" / "Sine.lean",
      mutations := sineMutations },
    { what := "combinatorics",
      figuresFile := "PILeanMathlib" / "Examples" / "CombinatoricsFigures.lean",
      figuresModule := "PILeanMathlib.Examples.CombinatoricsFigures",
      theoremsFile := "PILeanMathlib" / "Examples" / "Combinatorics.lean",
      mutations := combinatoricsMutations },
    { what := "algebra",
      figuresFile := "PILeanMathlib" / "Examples" / "AlgebraFigures.lean",
      figuresModule := "PILeanMathlib.Examples.AlgebraFigures",
      theoremsFile := "PILeanMathlib" / "Examples" / "Algebra.lean",
      mutations := algebraMutations },
    { what := "zeros and poles",
      figuresFile := ".." / "PILeanTest" / "ComplexDiagrams.lean",
      figuresModule := "PILeanTest.ComplexDiagrams",
      theoremsFile := "PILeanMathlib" / "Examples" / "Complex.lean",
      mutations := complexMutations, allowed := ["rationalFigure_spec"] },
    { what := "explorers",
      figuresFile := ".." / "PILeanTest" / "Explorers.lean",
      figuresModule := "PILeanTest.Explorers",
      theoremsFile := "PILeanMathlib" / "Examples" / "Explorers.lean",
      mutations := explorerMutations,
      allowed := ["cayleyExplorer_spec", "latticeExplorer_spec"] }]

/-- The most compilations run at once (each loads Mathlib). -/
def parallel : Nat := 5

/-- The checks of one group: the unchanged joined file compiles, then each change, `parallel` at a
time, breaks its theorem. -/
def groupChecks (lean : String) (scratch : System.FilePath) (g : Group) :
    IO (Array (String × Bool)) := do
  let kinds ← g.kinds.mapM fun (f, m) => do return (m, ← IO.FS.readFile f)
  let (text, start) := joined g.figuresModule (← IO.FS.readFile g.figuresFile)
    (← IO.FS.readFile g.theoremsFile) kinds
  let dir := scratch / g.what.replace " " "-"
  IO.FS.createDirAll dir
  let plain := dir / "Plain.lean"
  IO.FS.writeFile plain text
  let (c0, out0) ← compile lean plain
  let name0 := s!"the joined file of the figures of {g.what} and their theorems compiles"
  if c0 != 0 || !(errorLines out0 plain.toString).isEmpty then
    IO.eprintln s!"{name0}: no: {(out0.take 800).toString}"
    return #[(name0, false)]
  let ms := g.mutations.zipIdx
  let mut out := #[(name0, true)]
  for b in [0:(ms.size + parallel - 1) / parallel] do
    let batch := ms.extract (b * parallel) ((b + 1) * parallel)
    let tasks ← batch.mapM fun (m, k) =>
      IO.asTask (checkJoined lean dir text start m k g.allowed)
    for ((m, _), t) in batch.zip tasks do
      let name := s!"the change breaks {m.spec}: {m.what}"
      match t.get with
      | .ok (.ok ()) => out := out.push (name, true)
      | .ok (.error why) => IO.eprintln s!"{name}: {why}"; out := out.push (name, false)
      | .error e => IO.eprintln s!"{name}: {e}"; out := out.push (name, false)
  return out

/-- The checks of every group; without `LEAN` in the environment the check fails instead of
running a `lean` of unknown origin. -/
def ioChecks : IO (Array (String × Bool)) := do
  let some lean ← IO.getEnv "LEAN"
    | return #[("the changes to the figures are checked (LEAN is not set)", false)]
  let scratch ← IO.FS.createTempDir
  let mut out := #[]
  for g in groups do
    out := out ++ (← groupChecks lean scratch g)
  IO.FS.removeDirAll scratch
  return out

end PILeanMathlibTest.Mutations
