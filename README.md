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
| Images: modes L, RGB, RGBA; `new`, `getpixel`, `putpixel`, `crop`, `paste` with a mask, `convert`, flips and quarter turns, `resize` (nearest, bilinear, box, Lanczos) | done; sizes and flips proved |
| Rasteriser: anti-aliased fill by exact area coverage in integer arithmetic (non-zero and even-odd), clipping to rectangles and paths, strokes (caps, joins, miter limit, dashes), solid and gradient paints, compositing in linear light, group opacity; an `ImageDraw`-like `Draw` | done; checked against known areas and against macOS's SVG renderer |
| PNG: CRC-32, Adler-32, zlib/DEFLATE (stored, fixed and dynamic Huffman with LZ77), writer (grey, RGB, RGBA, filters 0–4, `sRGB`, `gAMA`, `tEXt`, `iTXt`) and reader (every colour type and depth, palette, Adam7, size caps) | done; checksums and framing proved, the codec tested against Python's `zlib` and macOS's `sips` |
| Plots as PNG: the same picture as the SVG, drawn from the same nodes (text not yet drawn in PNGs) | done; see [`examples/`](examples/README.md) |
| Canvas, text, graphs, traceability | designed in [`docs/DESIGN.md`](docs/DESIGN.md), not started |

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

The gallery (`examples/*.svg`, `examples/*.png`, [`examples/README.md`](examples/README.md)) is
written by `lake exe pilean-gallery` from the figures in `PILeanTest/Examples.lean`.

```lean
open PILean PILean.Raster

def picture : Image :=
  let d := Draw.new 300 200
  let d := d.rectangle 20 20 280 60
    (fill := some (.linear ⟨20, 0⟩ ⟨280, 0⟩ #[⟨0, ⟨230, 30, 30, 255⟩⟩, ⟨1, ⟨20, 60, 220, 255⟩⟩]))
  let d := d.line #[⟨20, 100⟩, ⟨120, 160⟩, ⟨200, 90⟩] (.solid ⟨0, 0, 0, 255⟩) 6 .round .round
  d.toImage

#eval match picture.writePng with
  | .ok bytes => IO.FS.writeBinFile "picture.png" bytes
  | .error e => IO.println e.toString
```

## Tests

```
lake build --wfail
lake test
```

`lake test` runs the named checks (colour, geometry, paths, SVG writer, ticks, PNG and DEFLATE
with their reader fixtures and mutated files, image operations, rasteriser) and compares each
gallery figure's SVG and PNG with its files in `examples/`, byte for byte.
`lake exe pilean-test --update` rewrites those files after a deliberate change.

Checks against tools already on a Mac (nothing to install):

```
lake exe pilean-test --png-out /tmp/pilean-png && python3 -I tools/png-check.py scratch /tmp/pilean-png
lake exe pilean-test --compare-out /tmp/pilean-cmp && python3 -I tools/compare-render.py /tmp/pilean-cmp
lake exe pilean-test --bench
```

The first decodes PILean's zlib streams and PNGs with Python's `zlib`; the second renders the
gallery's SVGs with `sips` and compares their pixels with PILean's PNGs.

## Trust model (outline)

PILean treats what it is given as untrusted: text in a figure (titles, labels) is escaped before
it reaches SVG, characters XML cannot carry are dropped, element and attribute names are checked,
and every loop is bounded by its input (curve flattening has a cap per curve). The planned
traceability layer records in each image the Lean file and declaration that produced it, a
fingerprint of the specification, and a manifest with a checker; theorems tie a figure to the
Lean object it shows. PNG and DEFLATE data read from files are untrusted: every length is
checked, the output size is capped, and mutated files end in clean errors. The rasteriser
computes coverage in integers, so its output is the same on every machine.
`docs/DESIGN.md` has the details and the open choices.

## Licence

Apache License 2.0 (`LICENSE`). PILean follows the shape of Pillow's API in places; no Pillow code
is used (`THIRD-PARTY.md`).
