/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILean
import PILean.Trust.Attr
import PILeanVersoManual
import PILeanManual.Meta
import PILeanManual.Pictures

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open PILeanVerso.Manual
open PILeanManual

#doc (Manual) "Text Engines" =>
%%%
tag := "text"
%%%

```lean -show
namespace PILeanManual.TextGuide
open PILean
```

Text reaches pictures through one interface, {name}`PILean.TextEngine`: what a plot needs of a
typesetter. An engine measures a string at a size, gives the ascent and descent, and shapes a
string as filled outlines, centre lines to stroke, or both ({name}`PILean.TextShape`). It also
says who it is ({name}`PILean.TextEngine.id`, which the fingerprint of every figure drawn with it
covers) and whether its strings are plain text that SVG may keep as `text` elements
({name}`PILean.TextEngine.native`).

The style's engine ({name}`PILean.Style.text`) measures every label for the layout. In SVG, the
text of a native engine is written as `text` elements in the style's font family, so it stays
selectable and small (a browser's font may run a little wider or narrower than the measurement);
`Figure.toSvg (outlines := true)` writes the engine's shapes instead. In PNG, text is always the
engine's shapes, drawn by the rasteriser. The text of an engine that is not native is written as
shapes in SVG too.

# The Built-in Lettering
%%%
tag := "text-lettering"
%%%

{name}`PILean.TextEngine.lettering` is a single-stroke lettering drawn for PILean: 430 characters
(ASCII, Latin-1, Greek, scripts, mathematical signs, arrows, typographic punctuation), tabular
digits, a stroke 78/1000 of the size and never thinner than a pixel. It needs no font file and is
the default.

```lean (name := letteringEx)
#eval TextEngine.lettering.measure "Lean 4" 12
#eval TextEngine.lettering.measure "0123456789" 12 == TextEngine.lettering.measure "1111111111" 12
#eval (TextEngine.lettering.shape "αβγ → ∞" 20 1).strokes.cmds.size
```

```leanResult letteringEx
```

```lean
open PILean.Canvas in
/-- A line of lettering at three sizes, drawn as the engine's shapes. -/
@[figure]
def lettering : PILeanManual.Drawing where
  width := 480
  height := 150
  draw st :=
    let line (s : String) (size y : Float) : Shape :=
      let sh := st.text.shape s size 1
      .group #[.path sh.strokes none
          (some { ink := st.inkPrimary, width := sh.strokeWidth, cap := "round", join := "round" })]
        (Affine.translate 16 y)
    .group #[.path (rect 0 0 480 150) (some (.solid st.background)),
      line "Sphinx of black quartz, judge my vow." 22 40,
      line "∀ ε > 0, ∃ δ > 0 : |x − y| < δ → |f x − f y| < ε" 16 82,
      line "αβγδ ← → ⇒ ≤ ≥ ≠ ± × ÷ ∑ ∫ √ ∞ — “quoted” ½ ¼ ©" 13 120]
```

:::figure PILeanManual.TextGuide.lettering (alt := "Three lines of single-stroke lettering: the pangram 'Sphinx of black quartz, judge my vow.', the epsilon-delta definition of continuity in symbols, and a row of Greek letters, arrows and mathematical signs.")
:::

# Other Engines
%%%
tag := "text-engines"
%%%

Any value of {name}`PILean.TextEngine` can be put into a style
(`{ Style.light with text := e }`). An engine whose strings are markup sets `native := false`, so
that its text is never written as SVG text, and names its code and data in `id`, so that the
fingerprint of a figure changes when they change ({name}`PILean.Trust.rendererWith`).

The package `pilean-leantex` (the folder `leantex/` of the repository) is such an engine, backed
by LeAnTeX: titles, axis and tick labels, legend entries and node labels are LaTeX, formulas in
`$…$`, typeset on one line and drawn as glyph outlines of New Computer Modern, in SVG (as paths,
so the picture needs no font) and in PNG. A string LeAnTeX rejects, or one longer than 1,000
characters, is drawn by the built-in lettering instead; every string is typeset under caps on
tokens, expansions, nesting and line-breaking work. Its identity names the LeAnTeX commit and the
SHA-256 of every font file it reads. It is a separate package because LeAnTeX is large and reads
about 20 MB of fonts at run time: as a dependency of the core it would weigh on every user. See
{ref "packages"}[] for how to require it; this manual does not depend on it.
