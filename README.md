# PILean

A pure-Lean image library, in the role Pillow has in Python: colours, geometry, vector paths,
SVG output and plots today; a rasteriser, PNG, a drawing canvas and graphs of nodes and edges
next. Every image is meant to be traceable to the Lean that made it.

PILean depends on Lean's `Init` and `Std` only (no Mathlib), so any Lean program can use it.

## Status

| Part | State |
|---|---|
| Colour: 8-bit sRGB with alpha, linear light, OKLab and OKLCH, gamut mapping, WCAG contrast, hex, compositing | done, checked against published values |
| Geometry: points, affine transforms, boxes | done |
| Paths: lines, quadratic and cubic Béziers, flattening to a tolerance, tight and control boxes | done |
| SVG writer: typed document model, deterministic output, escaping of all text | done |
| Plots: function graphs and data lines, nice-number ticks, legends, written from a `Figure` value | first version; see `examples/` |
| Rasteriser, PNG (pure-Lean deflate, CRC), canvas, text, graphs, traceability | designed in [`docs/DESIGN.md`](docs/DESIGN.md), not started |

## Use

```lean
import PILean
open PILean.Plot

def fig : Figure where
  title := "Trigonometric functions"
  xLabel := "x"
  marks := #[.function "sin x" Float.sin (-3.14) 3.14]

#eval IO.FS.writeFile "sin.svg" fig.toSvg
```

The gallery (`examples/*.svg`) is written by `lake exe pilean-gallery` from the figures in
`PILeanTest/Examples.lean`.

## Tests

```
lake build --wfail
lake test
```

`lake test` runs the named checks (colour, geometry, paths, SVG writer, ticks) and compares each
gallery figure with its file in `examples/`, byte for byte. `lake exe pilean-test --update`
rewrites those files after a deliberate change.

## Trust model (outline)

PILean treats what it is given as untrusted: text in a figure (titles, labels) is escaped before
it reaches SVG, characters XML cannot carry are dropped, element and attribute names are checked,
and every loop is bounded by its input (curve flattening has a cap per curve). The planned
traceability layer records in each image the Lean file and declaration that produced it, a
fingerprint of the specification, and a manifest with a checker; theorems tie a figure to the
Lean object it shows. The rasteriser will compute in floating point and is tested, not proved.
`docs/DESIGN.md` has the details and the open choices.

## Licence

Apache License 2.0 (`LICENSE`). PILean follows the shape of Pillow's API in places; no Pillow code
is used (`THIRD-PARTY.md`).
