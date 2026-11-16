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
import PILeanTest.GraphQuality
import PILeanTest.GraphDot
import PILeanTest.Exact
import PILeanTest.Trust
import PILeanTest.TrustBuild
import PILeanTest.Inert
import PILeanTest.Bounds
import PILeanTest.Tools

/-!
# The axioms of the library, checked by the build

`#assert_standard_axioms PILean PILeanTest` goes through every declaration (theorems,
definitions and opaque constants alike) of every imported module whose name starts with one of
the given prefixes and fails, and with it the build of the tests, if one of them depends on an
axiom other than `propext`, `Classical.choice` and `Quot.sound`. A `sorry` (`sorryAx`), a
`native_decide` or a `bv_decide` (`Lean.ofReduceBool`, `Lean.trustCompiler`) in the library
would be such an axiom. The check does not rely on a list of theorem names, so a theorem added
later is covered without anyone remembering to list it. It sees the modules this file imports:
`PILean` (whose root file imports every module of the library but `PILean.Trust.Attr`, imported
here), and the test modules listed above, which are those the test driver imports; a check below
fails if a module of the library is missing.

An `axiom` declared in one of those modules, or in this one, is reported too, whether anything
uses it or not.

`#assert_modules_imported PILean` runs when this file is compiled. `Axioms.ioChecks`, which the
test driver runs on every `lake test`, compares the files below `PILean/` on disk at that moment
with the modules this file was compiled against, so a new library file that nothing imports is
reported even when the build of this file comes from the cache.

`#assert_figure_links` checks every link made by `figure_proves` in the imported modules again,
by the check of `figure_proves` (`PILean.Trust.figureTheoremProblem?`).
-/

open Lean Elab Command

namespace PILeanTest

/-- The module of the declaration `n` in the environment: the current module for a declaration
of the file being elaborated. -/
def declModule (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => env.mainModule

/-- The declarations of the environment whose module (`declModule`, the current module
included) satisfies `inScope`, paired with each axiom outside
`PILean.Trust.allowedAxioms` that they declare or depend on: an `axiom` is reported with itself,
whether anything uses it or not; a theorem, definition or opaque constant with each axiom it
depends on. -/
def nonStandardAxioms (inScope : Name → Bool) : CoreM (Array (Name × Name)) := do
  let env ← getEnv
  let decls := env.constants.fold (init := #[]) fun acc c info =>
    if inScope (declModule env c) then acc.push (c, info) else acc
  let mut bad := #[]
  for (c, info) in decls do
    match info with
    | .axiomInfo _ =>
      unless PILean.Trust.allowedAxioms.contains c do bad := bad.push (c, c)
    | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
      for a in ← collectAxioms c do
        unless PILean.Trust.allowedAxioms.contains a do bad := bad.push (c, a)
    | _ => pure ()
  return bad

/-- `#assert_standard_axioms A B …` fails unless no declaration of the imported modules (and of
this one) whose names start with `A`, `B`, … is an axiom or depends on an axiom other than those
of `PILean.Trust.allowedAxioms`, and unless each prefix has at least one theorem. -/
elab "#assert_standard_axioms " roots:(ppSpace ident)+ : command => do
  let env ← getEnv
  let roots := roots.map (·.getId)
  for r in roots do
    let found := env.constants.fold (init := false) fun acc c info =>
      acc || (info matches .thmInfo _ && r.isPrefixOf (declModule env c))
    unless found do
      throwError "no theorem found in the modules of {r}: nothing was checked"
  let bad ← liftCoreM (nonStandardAxioms fun m => roots.any (·.isPrefixOf m))
  unless bad.isEmpty do
    let lines := bad.toList.map fun (c, a) =>
      if c == a then m!"the axiom {a} is declared" else m!"{c} depends on the axiom {a}"
    throwError "declarations with a non-standard axiom:{indentD (MessageData.joinSep lines "\n")}"

-- An axiom declared in a checked module is reported even when nothing uses it, and so is a
-- theorem that uses one. The declarations are made and checked inside `withoutModifyingEnv`,
-- so they are not part of this module.
#guard_msgs in
run_cmd do
  let bad ← withoutModifyingEnv do
    let (bare, used, usesIt) := (mkIdent `_root_.PILeanTest.Planted.bare,
      mkIdent `_root_.PILeanTest.Planted.used, mkIdent `_root_.PILeanTest.Planted.usesIt)
    elabCommand (← `(axiom $bare : Nat))
    elabCommand (← `(axiom $used : 1 = 2))
    elabCommand (← `(theorem $usesIt : 1 = 2 := $(mkIdent `PILeanTest.Planted.used)))
    liftCoreM (nonStandardAxioms (`PILeanTest).isPrefixOf)
  for p in [(`PILeanTest.Planted.bare, `PILeanTest.Planted.bare),
      (`PILeanTest.Planted.used, `PILeanTest.Planted.used),
      (`PILeanTest.Planted.usesIt, `PILeanTest.Planted.used)] do
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

/-- The modules below the folder `dir` (relative to the package root, where Lake runs Lean):
one name for each `.lean` file, with the folder's name as the first component. -/
partial def modulesBelow (dir : System.FilePath) (pre : Name) : IO (Array Name) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then
      out := out ++ (← modulesBelow e.path (pre.str e.fileName))
    else if e.fileName.endsWith ".lean" then
      out := out.push (pre.str (e.fileName.dropEnd 5).toString)
  return out

/-- The modules below the folder `dir` (named from `pre`, as in `modulesBelow`) that are not in
`known`. -/
def unknownModules (dir : System.FilePath) (pre : Name) (known : Array Name) :
    IO (Array Name) := do
  return (← modulesBelow dir pre).filter (!known.contains ·)

/-- `#assert_modules_imported PILean` fails unless every `.lean` file below the folder `PILean`
is a module this file imports, directly or not, so that no module of the library is outside the
checks of this file. -/
elab "#assert_modules_imported " root:ident : command => do
  let env ← getEnv
  let r := root.getId
  if (← modulesBelow r.toString r).isEmpty then throwError "no module found below the folder {r}"
  let missing ← unknownModules r.toString r env.header.moduleNames
  unless missing.isEmpty do
    throwError "modules that are not imported, and so not checked: {missing}"

/-- `checked_modules%` is the `Array Name` of the modules of `PILean` this module imports, as
they were when it was compiled. -/
elab "checked_modules%" : term => do
  let names := (← getEnv).header.moduleNames.filter (`PILean).isPrefixOf
  return toExpr names

/-- The modules of `PILean` the checks of this file cover. -/
def checkedModules : Array Name := checked_modules%

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
  return #[
    ("axioms: every module below PILean/ is covered by the axiom check",
      missing.isEmpty && checkedModules.contains `PILean.Trust.Attr),
    ("axioms: a module file that is not imported is reported", stray == #[`X.B.C])]

#assert_modules_imported PILean

#assert_standard_axioms PILean PILeanTest

#assert_figure_links 4

end PILeanTest
