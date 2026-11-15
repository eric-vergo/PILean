/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Lake

/-!
# PILean's plots against the real numbers

The library `PILeanMathlib`: what it means, over the real numbers, for the polyline that PILean
draws through the exact samples of a function to be near the graph of a real function, and
theorems that bound the distance. `PILeanMathlib.Examples.SineFigure` is a figure (it needs
PILean only); `PILeanMathlib.Examples.Sine` is the theorem about it. The gallery generator
`pilean-mathlib-gallery` writes `examples/`; `lake test` runs the checks.

PILean itself (the package in the parent directory) has no dependencies; this package adds
Mathlib, at a fixed commit.
-/

open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"
require pilean from ".."

package «pilean-mathlib» where
  allowNonModules := true
  leanOptions := #[⟨`linter.missingDocs, true⟩, ⟨`autoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩, ⟨`weak.linter.mathlibStandardSet, true⟩,
    -- the files' header has a licence line and an authors line, and no copyright line
    ⟨`weak.linter.style.header, false⟩]

@[default_target]
lean_lib PILeanMathlib

lean_lib PILeanMathlibTest

/-- Writes the gallery `examples/*.svg` and `*.png` from `PILeanMathlib.Examples.SineFigure`.
It imports no module that imports Mathlib. -/
lean_exe «pilean-mathlib-gallery» where
  root := `PILeanMathlibTest.Gallery

/-- The test driver: `lake test` runs it from this folder. -/
@[test_driver]
lean_exe «pilean-mathlib-test» where
  root := `PILeanMathlibTest.Main
  needs := #[PILeanMathlib]
