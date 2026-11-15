/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanLeAnTeX.Outline
import PILeanLeAnTeX.Engine
import PILeanLeAnTeX.Examples

/-!
# PILean's text through LeAnTeX

`PILeanLeAnTeX.load` reads New Computer Modern and gives a `PILean.TextEngine` whose strings are
LaTeX (`PILeanLeAnTeX.Engine`); `PILeanLeAnTeX.outline` draws LeAnTeX's display lists as PILean
paths.
-/
