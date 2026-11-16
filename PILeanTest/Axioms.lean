/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Trust.Attr
import PILeanTest.ProvedExamples

/-!
# The axioms of the library, checked by the build

`#assert_standard_axioms PILean PILeanTest` goes through every declaration (theorems,
definitions and opaque constants alike) of every imported module whose name starts with one of
the given prefixes and fails, and with it the build of the tests, if one of them depends on an
axiom other than `propext`, `Classical.choice` and `Quot.sound`. A `sorry` (`sorryAx`), a
`native_decide` or a `bv_decide` (`Lean.ofReduceBool`, `Lean.trustCompiler`) in the library
would be such an axiom. The check does not rely on a list of theorem names, so a theorem added
later is covered without anyone remembering to list it.

`#assert_figure_theorems_name_figures` checks every link made by `figure_proves` in the imported
modules: the statement of the theorem must mention the figure itself, which is more than the rule
of `figure_proves` asks (it also accepts a statement about a definition the figure uses).
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
      let some info := env.find? thm | throwError "unknown theorem {thm}"
      unless info.type.getUsedConstants.contains fig do
        throwError "the statement of {thm} does not mention the figure {fig}"
  unless n.getNat ≤ links do
    throwError "{links} links from figures to theorems, expected at least {n.getNat}"

#assert_standard_axioms PILean PILeanTest

#assert_figure_theorems_name_figures 4

end PILeanTest
