/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Trust.Attr
import PILeanMathlib.Category
import PILeanMathlib.Group
import PILeanMathlib.Examples.Algebra
import PILeanMathlib.Examples.AlgebraFigures
import PILeanMathlib.Combinatorics
import PILeanMathlib.Examples.Combinatorics
import PILeanMathlib.Examples.CombinatoricsFigures
import PILeanMathlib.ExactPlot
import PILeanMathlib.Examples.Sine
import PILeanMathlib.Examples.SineFigure
import PILeanMathlib.Interpolation
import PILeanMathlib.NumberTheory
import PILeanMathlib.Examples.NumberTheory
import PILeanMathlib.Examples.NumberTheoryFigures
import PILeanMathlib.Polyline

/-!
# The axioms of the library, checked by the build

`#assert_standard_axioms PILeanMathlib` goes through every declaration (theorems, definitions,
opaque constants, inductive types with their constructors and recursors alike) of every module
of this library and fails, and with it the build, if
one of them is an axiom or depends on an axiom other than `propext`, `Classical.choice` and
`Quot.sound`. A `sorry`, a `native_decide` or a `bv_decide` in a proof would add such an axiom,
and an `axiom` declared in one of the modules is reported whether anything uses it or not. The
check walks the modules, not a list of names, so a theorem added later is covered without anyone
remembering to list it.

`#assert_modules_imported PILeanMathlib` fails unless every file below the folder
`PILeanMathlib` is one of the modules this file imports (or this file), so that no module of the
library is outside the check.

Both commands are PILean's (`PILean.Trust.Attr`), the same that check PILean itself.
-/

open Lean Elab Command PILean.Trust

-- The checks are commands that run when this file is built; Mathlib's style keeps `#`-commands
-- out of its own sources, which are not checks of this kind.
set_option linter.hashCommand false

namespace PILeanMathlib

-- An axiom declared in a module of this library is reported even when nothing uses it, and so
-- is a theorem that uses one. The declarations are made and checked inside
-- `withoutModifyingEnv`, so they are not part of this module.
#guard_msgs in
run_cmd do
  let bad ← withoutModifyingEnv do
    let (bare, usesIt) :=
      (mkIdent `_root_.PILeanMathlib.Planted.bare, mkIdent `_root_.PILeanMathlib.Planted.usesIt)
    elabCommand (← `(axiom $bare : 1 = 2))
    elabCommand (← `(theorem $usesIt : 1 = 2 := $(mkIdent `PILeanMathlib.Planted.bare)))
    liftCoreM (nonStandardAxioms (`PILeanMathlib).isPrefixOf)
  for p in [(`PILeanMathlib.Planted.bare, `PILeanMathlib.Planted.bare),
      (`PILeanMathlib.Planted.usesIt, `PILeanMathlib.Planted.bare)] do
    unless bad.contains p do throwError "{p.2} was not reported for {p.1}"

#assert_modules_imported PILeanMathlib

#assert_standard_axioms PILeanMathlib

end PILeanMathlib
