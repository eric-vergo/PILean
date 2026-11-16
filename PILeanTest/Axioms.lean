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

`#assert_figure_theorems_name_figures` checks every link made by `figure_proves` in the imported
modules again, by the rule of `figure_proves` (`PILean.Trust.statementNamesFigure`): the
statement of the theorem names the figure itself.
-/

open Lean Elab Command

namespace PILeanTest

/-- `#assert_standard_axioms A B …` fails unless every declaration of the imported modules whose
names start with `A`, `B`, … depends on no axiom other than those of
`PILean.Trust.allowedAxioms`, and unless each prefix has at least one theorem. -/
elab "#assert_standard_axioms " roots:(ppSpace ident)+ : command => do
  let env ← getEnv
  let roots := roots.map (·.getId)
  let moduleOf (c : Name) : Option Name :=
    (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!
  let decls := env.constants.fold (init := #[]) fun acc c info =>
    match info, moduleOf c with
    | .thmInfo _, some m | .defnInfo _, some m | .opaqueInfo _, some m =>
      if roots.any (·.isPrefixOf m) then acc.push (c, m, info matches .thmInfo _) else acc
    | _, _ => acc
  for r in roots do
    unless decls.any fun (_, m, isThm) => isThm && r.isPrefixOf m do
      throwError "no theorem found in the modules of {r}: nothing was checked"
  let mut bad : Array MessageData := #[]
  for (c, _, _) in decls do
    for a in ← liftCoreM (collectAxioms c) do
      unless PILean.Trust.allowedAxioms.contains a do
        bad := bad.push m!"{c} depends on the axiom {a}"
  unless bad.isEmpty do
    throwError "declarations with a non-standard axiom:\
      {indentD (MessageData.joinSep bad.toList "\n")}"

/-- `#assert_figure_theorems_name_figures n` fails unless the imported modules link at least `n`
theorems to figures with `figure_proves` and the statement of each mentions its figure. -/
elab "#assert_figure_theorems_name_figures " n:num : command => do
  let env ← getEnv
  let figures := (PILean.Trust.registeredFigures env).map (·.decl)
  let mut links := 0
  for fig in figures do
    for thm in PILean.Trust.figureTheorems env fig do
      links := links + 1
      unless ← liftCoreM (PILean.Trust.statementNamesFigure fig thm) do
        throwError "the statement of {thm} does not mention the figure {fig}"
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

/-- `#assert_modules_imported PILean` fails unless every `.lean` file below the folder `PILean`
is a module this file imports, directly or not, so that no module of the library is outside the
checks of this file. -/
elab "#assert_modules_imported " root:ident : command => do
  let env ← getEnv
  let r := root.getId
  let found ← modulesBelow r.toString r
  if found.isEmpty then throwError "no module found below the folder {r}"
  let missing := found.filter fun m => !env.header.moduleNames.contains m
  unless missing.isEmpty do
    throwError "modules that are not imported, and so not checked: {missing}"

#assert_modules_imported PILean

#assert_standard_axioms PILean PILeanTest

#assert_figure_theorems_name_figures 4

end PILeanTest
