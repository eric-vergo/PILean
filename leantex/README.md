# PILean labels through LeAnTeX

`pilean-leantex` is a `PILean.TextEngine` backed by [LeAnTeX](https://github.com/eric-vergo/LeAnTeX):
titles, axis labels, tick labels, legend entries and graph node labels are LaTeX, typeset by
LeAnTeX's text layer (formulas in `$…$` by its KaTeX-compatible math layout) and drawn as glyph
outlines of New Computer Modern, in SVG (as paths, so the picture needs no font and passes
`PILean.Svg.isInert`) and in PNG (through PILean's rasteriser).

PILean itself has no dependencies. This package, in its own folder, adds LeAnTeX (pinned in
`lakefile.lean`) and depends on PILean through the parent folder. Why it is a separate package
is in [`docs/DESIGN.md`](../docs/DESIGN.md), "Text in images".

## Use

In a project's `lakefile.lean`:

```lean
require «pilean-leantex» from git "https://github.com/eric-vergo/PILean" @ "<commit>" / "leantex"
```

```lean
import PILeanLeAnTeX
open PILean PILean.Plot

def fig (e : TextEngine) : Figure where
  title := "The Gaussian $e^{-x^2/2}$"
  style := { Style.light with text := e }
  panels := #[{
    x := { label := "$x$" }, y := { label := "$\\varphi(x)$" },
    series := #[.function "$\\frac{1}{\\sqrt{2\\pi}} e^{-x^2/2}$"
      (fun x => (-x * x / 2).exp / 2.5066282746310002) (-4) 4] }]

def main : IO Unit := do
  match ← PILeanLeAnTeX.load with
  | .ok e => IO.FS.writeFile "gauss.svg" (fig e).toSvg
  | .error msg => IO.eprintln msg
```

`PILeanLeAnTeX.load` reads the fonts from LeAnTeX's copy in the project's package folder
(`.lake/packages/leantex/fonts/newcomputermodern`, relative to the project root; another folder
can be passed) and hashes them for the engine's identity.

## Behaviour

* A string at size `s` pixels is set in LaTeX's ten-point article setup scaled so that its em is
  `s` pixels; a weight above 1.15 sets it in bold.
* The TeX-rule math layout is not used, because it depends on a TeX installation's metric files:
  a picture is a function of its strings, the LeAnTeX commit and the font files, the same on every
  machine.
* A string LeAnTeX rejects, or one longer than 1,000 characters, is drawn by PILean's built-in
  lettering (cut to 1,000 characters). Every string is typeset under tight caps on tokens,
  expansions, nesting and line-breaking work.
* Colours inside a label (`\color`) are not drawn apart: a label has one ink.
* The engine's identity (the LeAnTeX commit and the SHA-256 of each font file) is part of the
  fingerprint of every figure drawn with it.

## Gallery and tests

`lake exe pilean-leantex-gallery` writes `examples/` (two plots, light and dark, and a graph, as
SVG and PNG). `lake test` checks the gallery byte for byte against those files and for
determinism, that its SVG has no `text` element and is inert (also with a source record), the
engine's measurements and shapes, the fallback to the lettering, the engine's identity and the
fingerprint, that `leantexRevision` matches the pin, and runs hostile labels (recursive macros,
macro bombs, deep nesting, huge rules, a million characters, control characters, markup) in
child processes under a CPU limit and a memory bound.
