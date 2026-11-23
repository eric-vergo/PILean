/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Trust.Attr
import PILeanTest.ProvedExamples
import PILeanTest.Color
import PILeanTest.Units
import PILeanTest.Examples
import PILeanTest.Raster
import PILeanTest.Blur
import PILeanTest.Png
import PILeanTest.Image
import PILeanTest.Anim
import PILeanTest.Plots
import PILeanTest.Lettering
import PILeanTest.Graphs
import PILeanTest.GraphOrder
import PILeanTest.GraphQuality
import PILeanTest.GraphDot
import PILeanTest.Exact
import PILeanTest.Enclosures
import PILeanTest.FigureChecks
import PILeanTest.GraphRoutes
import PILeanTest.GraphBundles
import PILeanTest.Plane
import PILeanTest.PlaneExact
import PILeanTest.Trust
import PILeanTest.TrustBuild
import PILeanTest.Inert
import PILeanTest.SpecMutations
import PILeanTest.Bounds
import PILeanTest.Tools
import PILeanTest.Diagrams
import PILeanTest.Standing

/-!
# The axioms of the library, checked by the build

`#assert_standard_axioms PILean PILeanTest` goes through every declaration (theorems,
definitions, opaque constants, inductive types with their constructors and recursors alike) of
every imported module whose name starts with one of the given prefixes and fails, and with it
the build of the tests, if one of them depends on an axiom other than `propext`,
`Classical.choice` and `Quot.sound`. A `sorry` (`sorryAx`), a
`native_decide` or a `bv_decide` (`Lean.ofReduceBool`, `Lean.trustCompiler`) in the library
would be such an axiom. The check does not rely on a list of theorem names, so a theorem added
later is covered without anyone remembering to list it. It sees the modules this file imports:
`PILean` (whose root file imports every module of the library but `PILean.Trust.Attr`, imported
here), and the test modules listed above. A check below fails if a module of the library is
missing, and `Axioms.coverageChecks`, which the test driver runs with the test modules of its own
imported environment (`test_modules%`), fails if a test module the driver imports is not among
those this file was compiled against.

An `axiom` declared in one of those modules, or in this one, is reported too, whether anything
uses it or not.

`#assert_modules_imported PILean` runs when this file is compiled. `Axioms.ioChecks`, which the
test driver runs on every `lake test`, compares the files below `PILean/` on disk at that moment
with the modules this file was compiled against, so a new library file that nothing imports is
reported even when the build of this file comes from the cache.

`Axioms.ioChecks` also reads the `import` lines of the sources and fails if `import PILean` reaches
`Lean` or `PILean.Trust.Attr`, or any module outside `Init` and `Std`.

`#assert_figure_links` checks every link made by `figure_proves` in the imported modules again,
by the check of `figure_proves` (`PILean.Trust.figureTheoremProblem?`).

`#assert_standard_axioms` and `#assert_modules_imported` are defined in `PILean.Trust.Attr`, so
that a package built on PILean can run them on its own modules; the Mathlib package does.
-/

open Lean Elab Command PILean.Trust

namespace PILeanTest

-- An axiom declared in a checked module is reported even when nothing uses it, and so is a
-- theorem that uses one, and an inductive type, its constructor and its recursor whose types
-- mention one. The declarations are made and checked inside `withoutModifyingEnv`,
-- so they are not part of this module.
#guard_msgs in
run_cmd do
  let bad ← withoutModifyingEnv do
    let (bare, used, usesIt) := (mkIdent `_root_.PILeanTest.Planted.bare,
      mkIdent `_root_.PILeanTest.Planted.used, mkIdent `_root_.PILeanTest.Planted.usesIt)
    elabCommand (← `(axiom $bare : Nat))
    elabCommand (← `(axiom $used : 1 = 2))
    elabCommand (← `(theorem $usesIt : 1 = 2 := $(mkIdent `PILeanTest.Planted.used)))
    let (ty, ctorAx) := (mkIdent `_root_.PILeanTest.Planted.T, mkIdent `_root_.Planted.inCtor)
    elabCommand (← `(axiom $ctorAx : Nat))
    elabCommand (← `(inductive $ty where
      | $(mkIdent `mk):ident : Fin $(mkIdent `Planted.inCtor) → $(mkIdent `PILeanTest.Planted.T)))
    liftCoreM (nonStandardAxioms (`PILeanTest).isPrefixOf)
  for p in [(`PILeanTest.Planted.bare, `PILeanTest.Planted.bare),
      (`PILeanTest.Planted.used, `PILeanTest.Planted.used),
      (`PILeanTest.Planted.usesIt, `PILeanTest.Planted.used),
      (`PILeanTest.Planted.T, `Planted.inCtor), (`PILeanTest.Planted.T.mk, `Planted.inCtor),
      (`PILeanTest.Planted.T.rec, `Planted.inCtor)] do
    unless bad.contains p do throwError "{p.2} was not reported for {p.1}"

/-- `#assert_figure_links n` fails unless the imported modules link at least `n` theorems to
figures with `figure_proves` and each link still passes the check of `figure_proves`
(`PILean.Trust.figureTheoremProblem?`). -/
elab "#assert_figure_links " n:num : command => do
  let env ← getEnv
  let figures := (PILean.Trust.registeredFigures env).map (·.decl)
  let mut links := 0
  for fig in figures do
    for thm in PILean.Trust.figureTheorems env fig do
      links := links + 1
      if let some msg ← liftCoreM (PILean.Trust.figureTheoremProblem? fig thm) then
        throwError "the link from {fig} to {thm}: {msg}"
  unless n.getNat ≤ links do
    throwError "{links} links from figures to theorems, expected at least {n.getNat}"

/-- `checked_modules%` is the `Array Name` of the modules of `PILean` this module imports, as
they were when it was compiled. -/
elab "checked_modules%" : term => do
  let names := (← getEnv).header.moduleNames.filter (`PILean).isPrefixOf
  return toExpr names

/-- The modules of `PILean` the checks of this file cover. -/
def checkedModules : Array Name := checked_modules%

/-- `test_modules%` is the `Array Name` of the modules of `PILeanTest` that the module it is
written in imports, directly or not, read from its imported environment when it is compiled. -/
elab "test_modules%" : term => do
  let names := (← getEnv).header.moduleNames.filter (`PILeanTest).isPrefixOf
  return toExpr names

/-- The modules of `PILeanTest` the checks of this file cover. -/
def checkedTestModules : Array Name := test_modules%

/-- The modules of `driver` other than this one that are not in `checked`. -/
def uncoveredModules (driver checked : Array Name) : Array Name :=
  driver.filter fun m => m != `PILeanTest.Axioms && !checked.contains m

/-- The checks that the axiom check covers every test module of the test driver, given the
modules the driver imports (`test_modules%` written in the driver); and that a module missing
from the check is reported. -/
def Axioms.coverageChecks (driver : Array Name) : Array (String × Bool) :=
  let missing := uncoveredModules driver checkedTestModules
  #[(s!"axioms: every test module the test driver imports is covered by the axiom check \
      (not covered: {missing})", missing.isEmpty && driver.contains `PILeanTest.Axioms &&
      driver.size > 10),
    ("axioms: a test module of the driver that the check does not import is reported",
      uncoveredModules #[`X.A, `X.B, `PILeanTest.Axioms] #[`X.A] == #[`X.B])]

/-- The modules a source file imports: the lines `import M` that follow its licence comment. -/
def headerImports (src : String) : Array Name := Id.run do
  let mut out := #[]
  let mut started := false
  for line in src.splitOn "\n" do
    if !started then
      started := line.trimAscii.toString == "-/"
    else if line.startsWith "import " then
      out := out.push (line.drop 7).trimAscii.toString.toName
    else if !line.trimAscii.isEmpty then
      break
  return out

/-- The modules `root` imports, directly or not, among those whose sources are found from the
current folder (`A.B` as `A/B.lean`), and the modules outside that tree that they import
(`Init`, `Std` and the like). -/
partial def importClosure (root : Name) : IO (Array Name × Array Name) := do
  let mut seen : Array Name := #[]
  let mut external : Array Name := #[]
  let mut todo := #[root]
  while !todo.isEmpty do
    let m := todo.back!
    todo := todo.pop
    unless seen.contains m do
      seen := seen.push m
      let file : System.FilePath := (m.components.foldl (· / ·.toString) "." : System.FilePath)
        |>.withExtension "lean"
      if root.isPrefixOf m && (← file.pathExists) then
        todo := todo ++ headerImports (← IO.FS.readFile file)
      else
        external := external.push m
  return (seen, external)

/-- The checks of the test driver: every `.lean` file below `PILean/` on disk when `lake test`
runs is one of the modules this file checked when it was compiled, so that a new file that no
module imports is reported even when this file is not rebuilt; and the comparison reports a
stray file in a scratch folder. -/
def Axioms.ioChecks : IO (Array (String × Bool)) := do
  let missing ← unknownModules "PILean" `PILean checkedModules
  unless missing.isEmpty do
    IO.eprintln s!"modules below PILean/ that the axiom check does not cover: {missing}"
  let dir ← IO.FS.createTempDir
  let stray ← try
      IO.FS.createDirAll (dir / "X" / "B")
      IO.FS.writeFile (dir / "X" / "A.lean") ""
      IO.FS.writeFile (dir / "X" / "B" / "C.lean") ""
      IO.FS.writeFile (dir / "X" / "notes.txt") ""
      unknownModules (dir / "X") `X #[`X.A]
    finally IO.FS.removeDirAll dir
  let (closure, external) ← importClosure `PILean
  let leanFree := external.all fun m => m == `Init || m == `Std || (`Std).isPrefixOf m
  return #[
    ("imports: `import PILean` reaches Init and Std only, not Lean",
      leanFree && closure.size > 50 && !external.isEmpty && !closure.contains `PILean.Trust.Attr),
    ("imports: the module with the attribute `figure` imports Lean",
      headerImports (← IO.FS.readFile "PILean/Trust/Attr.lean") |>.contains `Lean),
    ("axioms: every module below PILean/ is covered by the axiom check",
      missing.isEmpty && checkedModules.contains `PILean.Trust.Attr),
    ("axioms: a module file that is not imported is reported", stray == #[`X.B.C])]

#assert_modules_imported PILean

#assert_standard_axioms PILean PILeanTest

#assert_figure_links 19

end PILeanTest
