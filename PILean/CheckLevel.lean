/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# How strictly a figure's checks apply

Plane figures (`PILean.Plane.Check`) and plots (`PILean.Plot.Check`) check what a reader would
object to in them; a figure's `checks` field says what a rendering does with the problems found.

## Main definitions

* `CheckLevel`.
-/

namespace PILean

/-- How strictly a figure's checks are applied when it is rendered: not at all, as warnings, or
as errors that stop its rendering. -/
inductive CheckLevel where
  /-- The checks are not run. -/
  | ignore
  /-- Problems are reported as warnings. -/
  | warn
  /-- A problem stops the figure from being rendered. -/
  | fail
  deriving BEq, Inhabited, Repr

end PILean
