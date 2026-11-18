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

#doc (Manual) "Colours and Styles" =>
%%%
tag := "colour"
%%%

```lean -show
namespace PILeanManual.Colour
open PILean
```

# Colours
%%%
tag := "colour-rgba"
%%%

A colour is an {name}`PILean.Rgba`: four bytes, 8-bit sRGB with straight (not premultiplied)
alpha. The arithmetic around it ({api}`PILean.Color`) works in three spaces: the sRGB bytes,
linear light ({name}`PILean.LinearRgba`, where light adds up, so compositing and gradients are
done there), and Björn Ottosson's OKLab and its polar form OKLCH ({name}`PILean.OkLab`,
{name}`PILean.OkLch`), where equal steps look roughly equally different.

```lean (name := colourHex)
#eval Rgba.hex ⟨0, 114, 178, 255⟩
#eval Rgba.hex ⟨0, 114, 178, 128⟩
#eval Rgba.ofHex? "#0072b2"
#eval Rgba.ofHex? "#08f"
#eval Rgba.ofHex? "javascript:alert(1)"
```

```leanResult colourHex
```

{name}`PILean.Rgba.ofHex?` reads untrusted text: it accepts the four CSS forms and nothing else,
and rejects any string longer than nine bytes before looking at its characters.

OKLCH is the space to choose colours in: lightness, chroma and hue. A colour named there may lie
outside what sRGB can show; {name}`PILean.Rgba.ofOkLch` brings it inside by CSS Color 4's gamut
mapping (chroma is reduced at the same lightness and hue until clipping changes the colour
less than a just-noticeable difference), so the result is always a valid colour:

```lean (name := colourOklch)
#eval (Rgba.ofOkLch ⟨0.7, 0.1, 250⟩).hex
#eval (Rgba.ofOkLch ⟨0.7, 0.4, 250⟩).hex
#eval (Rgba.ofHex? "#0072b2").map fun c =>
  let l := c.toOkLch
  (l.l, l.c, l.h)
```

```leanResult colourOklch
```

The second colour asks for more chroma than sRGB has at that lightness and hue, and gets the
most there is.

Contrast is measured as WCAG 2 defines it ({name}`PILean.relLum`, {name}`PILean.contrast`, from
1 to 21); compositing is Porter and Duff's source-over in linear light
({name}`PILean.Rgba.over`); {name}`PILean.Rgba.mixOk` interpolates in OKLab.

```lean (name := colourContrast)
#eval contrast ⟨0, 0, 0, 255⟩ ⟨255, 255, 255, 255⟩
#eval contrast Style.light.inkMuted Style.light.background
#eval (Rgba.over ⟨255, 0, 0, 128⟩ ⟨0, 0, 255, 255⟩).hex
#eval (Rgba.mixOk ⟨255, 0, 0, 255⟩ ⟨0, 0, 255, 255⟩ 0.5).hex
```

```leanResult colourContrast
```

Every conversion from a floating-point channel to a byte clamps it into `[0, 1]` first, rounds
half up, and maps `NaN` to 0, so no input gives an invalid colour.

# Styles
%%%
tag := "style"
%%%

Every visual constant of PILean's plots and graphs is a field of one record,
{name}`PILean.Style`: the page, three steps of ink for text, the axis and grid colours, the series
palette, the font family of SVG text, the text engine, the sizes of text, the margins and gaps,
line widths, marker sizes and the colours of graph nodes and edges. A change of look is a change
of fields:

```lean
open PILean.Plot in
def bigTitles (fig : Figure) : Figure :=
  { fig with style := { fig.style with titleSize := 20, lineWidth := 3 } }
```

{name}`PILean.Style.light` is the default and {name}`PILean.Style.dark` its counterpart for dark
pages. Both follow the same rules: text is never drawn in a series colour; axes are a mid grey and
the grid a hairline barely darker (or lighter) than the page, so that the data carry the contrast;
the palette is Okabe and Ito's colour-blind-safe set, ordered so that neighbouring colours stay
apart under the common colour-vision deficiencies, and stepped for the dark page in the dark
style. A seventh series takes the first colour again, dashed ({name}`PILean.Style.seriesColor`):

```lean (name := colourSeries)
#eval (List.range 8).map fun i =>
  let (c, dashed) := Style.light.seriesColor i
  (c.hex, dashed)
```

```leanResult colourSeries
```

The two palettes, drawn from the styles themselves (in this manual each figure in the style of
the page's theme; switch the theme to see the other):

```lean
open PILean.Canvas in
/-- The series colours of a style, one swatch each, on the style's page colour. -/
@[figure]
def palette : PILeanManual.Drawing where
  width := 480
  height := 96
  draw st := .group (#[.path (rect 0 0 480 96) (some (.solid st.background))] ++
    st.palette.mapIdx fun i c =>
      .group #[
        .path (Path.roundedRect (16 + 76 * i.toFloat) 16 64 40 6) (some (.solid c)),
        .text c.hex ⟨48 + 76 * i.toFloat, 78⟩ 11 st.inkSecondary .middle])
```

:::figure PILeanManual.Colour.palette (alt := "Six rounded swatches in a row, each labelled with its hexadecimal value: the series colours of the style, in order: blue, orange, green, vermilion, reddish purple and sky blue in the light style.")
:::

The manual draws light and dark versions of every plot and graph whose style is
{name}`PILean.Style.light` by putting {name}`PILean.Style.dark`'s colours into it
(`PILeanVerso.Style.darkVariant?`, in the package `pilean-verso-manual`); a figure with colours
of its own is shown as it is in both themes.
