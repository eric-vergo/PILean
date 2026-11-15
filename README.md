# PILean

A pure-Lean image library, in the role Pillow has in Python: colours, geometry, vector paths,
a drawing canvas, SVG and PNG output, plots, graphs of nodes and edges, and animations (animated
SVG, APNG, GIF).
Every image is meant to be traceable to the Lean that made it.

PILean depends on Lean's `Init` and `Std` only (no Mathlib), so any Lean program can use it.

## Status

| Part | State |
|---|---|
| Colour: 8-bit sRGB with alpha, linear light, OKLab and OKLCH, gamut mapping, WCAG contrast, hex, compositing | done, checked against published values |
| Geometry: points, affine transforms, boxes | done |
| Paths: lines, quadratic and cubic Béziers, flattening to a tolerance, tight and control boxes | done |
| SVG writer: typed document model, deterministic output, escaping of all text | done |
| Plots: a `Figure` of panels in a grid (shared axes), linear and logarithmic axes with nice major and minor ticks, grid, titles, axis labels, legends, annotations; lines (with markers), scatter, steps, areas and bands (fill between), grouped and stacked bars, histograms, functions sampled adaptively (broken at poles and jumps), error bars; light and dark styles from one `Style` record; awkward data (empty, constant, huge, non-finite) handled; SVG and PNG from the same drawing | done; see [`examples/`](examples/README.md); ticks proved ascending and inside their interval |
| Images: modes L, RGB, RGBA; `new`, `getpixel`, `putpixel`, `crop`, `paste` with a mask, `convert`, flips and quarter turns, `resize` (nearest, bilinear, box, Lanczos) | done; sizes and flips proved |
| Rasteriser: anti-aliased fill by exact area coverage in integer arithmetic (non-zero and even-odd), clipping to rectangles and paths, strokes (caps, joins, miter limit, dashes), solid and gradient paints, compositing in linear light, group opacity; an `ImageDraw`-like `Draw` | done; checked against known areas and against macOS's SVG renderer |
| PNG: CRC-32, Adler-32, zlib/DEFLATE (stored, fixed and dynamic Huffman with LZ77), writer (grey, RGB, RGBA, filters 0–4, `sRGB`, `gAMA`, `tEXt`, `iTXt`) and reader (every colour type and depth, palette, Adam7, size caps) | done; checksums and framing proved, the codec tested against Python's `zlib` and macOS's `sips` |
| Animated images: a `FrameSeq` written as APNG (`toApng`) or GIF (`toGif`, optionally dithered) and read back composed (`Anim.readApng`, `Anim.readGif`); frame differencing, merged equal frames, exact rational delays, size and frame caps | done; written and read back exactly (GIF when it has at most 256 colours), LZW and the quantiser tested, mutated and truncated files rejected cleanly, the files checked by `tools/anim-check.py` (Python's `zlib` and `struct`, its own LZW decoder) and by macOS's `sips` |
| Canvas: shapes, paths, groups with transforms, opacity and clips, gradients, text; written as SVG or drawn as PNG from the same SVG nodes | done |
| Text in images: a `TextEngine` interface; the built-in single-stroke lettering (430 characters: ASCII, Latin-1, Greek, scripts, math signs, arrows, typographic punctuation) draws labels into PNGs; SVG keeps real `<text>` | done ([specimen](examples/lettering-specimen.png)) |
| Animations: one `Animation` (a drawing as a function of time, frame rate, duration, loops) written as animated SVG (SMIL only, interpolated attributes or frame switching), APNG and GIF, with a poster frame for reduced motion | done; outputs read back by PILean's readers and opened by macOS's ImageIO; the animated SVGs of the gallery checked in headless Chromium (frames differ with time, poster shown under reduced motion, `tools/anim-browser-check.py`) |
| Graphs: nodes, edges and clusters; layered (Sugiyama) layout with cycle removal, network simplex layering, weighted-median crossing reduction, Brandes–Köpf and network simplex coordinates, spline or orthogonal edges, arrowheads, edge labels; circular and tree layouts; SVG and PNG | done; layers and edge indices proved; about 0.7 s for 3000 nodes (under load), within 1.4 times the crossings of Graphviz's `dot` and about its edge length on 100 to 800 nodes; compared with Graphviz in [`docs/DESIGN.md`](docs/DESIGN.md) |
| Source information: the Lean declaration, file, line, repository, commit and version recorded in SVG (`<metadata>`, `<title>`, `<desc>`), PNG and APNG (`iTXt`) and GIF (comment) files and read back by a size-capped reader; `lake exe pilean-info FILE` prints it; SHA-256 in pure Lean; `Svg.isInert` checks that an SVG runs no script and loads nothing | done; see [`docs/TRUST.md`](docs/TRUST.md); round trips tested on every format with hostile input, SHA-256 against FIPS and NIST vectors and `shasum`, padding and digest size proved |
| Traceable builds: the attribute `@[figure]` and the term `figures%` collect the figures of a project; fingerprints (SHA-256 of the drawing's SVG encoding, the declaration's source text and position, and the version); `lake exe pilean-build` renders them deterministically with a `manifest.json` (`--check` compares a directory with the build), `lake exe pilean-verify DIR` checks a directory against its manifest | done; see [`docs/TRUST.md`](docs/TRUST.md) (including use in CI); tested end to end with damaged, missing, extra and hostile files |
| Theorems tying a figure to its Lean object: an exact function plot (the curve is the exact samples on a stated grid), a data plot (the points are the input list), a graph (nodes and edges are the relation and one route is drawn per edge) and an animation (frame `i` is the drawing at `i / fps`) | done for these four; see [`docs/PROOFS.md`](docs/PROOFS.md) for what is proved, tested and trusted; one example of each in the gallery |

## Use

```lean
import PILean
open PILean PILean.Plot

def fig : Figure where
  title := "Trigonometric functions"
  panels := #[{ x := { label := "x" }, y := { label := "y" },
    series := #[.function "sin x" Float.sin (-3.14) 3.14,
      .function "cos x" Float.cos (-3.14) 3.14] }]

#eval IO.FS.writeFile "sin.svg" fig.toSvg
#eval match fig.toPng with
  | some png => IO.FS.writeBinFile "sin.png" png
  | none => pure ()
#eval IO.FS.writeFile "sin-dark.svg" { fig with style := Style.dark }.toSvg
```

A graph is a value too, laid out in layers (or on a circle, or as a tree) and written as SVG or PNG:

```lean
open PILean

def deps : Graph := Graph.ofLabelled [("Main", "Parser"), ("Main", "Eval"), ("Parser", "Lexer"),
  ("Eval", "Parser")]

#eval IO.FS.writeFile "deps.svg" (deps.toSvg)
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
with their reader fixtures and mutated files, image operations, rasteriser, LZW, the palette
quantiser, the animated-image codecs with their mutated files, and the graph layouts) and compares each
gallery figure's SVG and PNG with its files in `examples/`, byte for byte.
`lake exe pilean-test --update` rewrites those files after a deliberate change.

Checks against tools already on a Mac (nothing to install):

```
lake exe pilean-test --png-out /tmp/pilean-png && python3 -I tools/png-check.py scratch /tmp/pilean-png
lake exe pilean-test --compare-out /tmp/pilean-cmp && python3 -I tools/compare-render.py /tmp/pilean-cmp
lake exe pilean-test --anim-out /tmp/pilean-anim && python3 -I tools/anim-check.py /tmp/pilean-anim
lake exe pilean-test --bench
lake exe pilean-test --graph-bench
lake exe pilean-test --graph-compare-out /tmp/pilean-graphs && python3 -I tools/graph-compare.py /tmp/pilean-graphs
```

The first decodes PILean's zlib streams and PNGs with Python's `zlib`; the second renders the
gallery's SVGs with `sips` and compares their pixels with PILean's PNGs; the third composes the
sample APNG and GIF files with a decoder written in Python and checks that both formats show the
same frames. The last compares the layered graph layout with Graphviz's `dot` (when it is on the
path) by crossings, edge length and area. `python3 tools/anim-browser-check.py` loads the
animated SVGs of the gallery in a headless Chromium through Playwright, when that is installed, and
checks that the picture changes with time and that reduced motion shows the poster frame.

## Trust model (outline)

PILean treats what it is given as untrusted: text in a figure (titles, labels) is escaped before
it reaches SVG, characters XML cannot carry are dropped, element and attribute names are checked,
and every loop is bounded by its input (curve flattening has a cap per curve). The traceability layer
records in each image the Lean file and declaration that produced it and a fingerprint of the
drawing and the declaration, with a manifest and two checkers (`pilean-build --check`,
`pilean-verify`); theorems tie a figure to the Lean object it shows ([`docs/PROOFS.md`](docs/PROOFS.md)). PNG and DEFLATE data read from files are untrusted: every length is
checked, the output size is capped, and mutated files end in clean errors. With the default
limits, reading a PNG of `n` bytes holds at most the input, the image data (at most `n` bytes)
and two buffers whose sizes together are at most `Limits.maxBytes` (512 MiB), allocated only after
the header has been checked against the caps, and its work is linear in those sizes; a zlib stream
is measured before its output is allocated, so a bomb is refused without its output; GIF and APNG
hold the composed frames (at most `Limits.maxBytes`) and a constant number of frame-sized buffers.
The graph layout's work is bounded by the numbers of nodes and edges and two work budgets
(`LayeredOptions.layerWork`, `coordinateWork`), with a cap on dummy nodes (`maxLayoutNodes`). The
command-line tools read only regular files, follow no symbolic link below the folder they are
given, and print what they read escaped. `lake test` runs the readers, the layout and the tools on
hostile inputs in child processes and checks their memory and CPU time
(`PILeanTest/Bounds.lean`, `PILeanTest/Tools.lean`). The rasteriser
computes coverage in integers, so its output is the same on every machine.
`docs/DESIGN.md` has the details and the open choices.

## Licence

Apache License 2.0 (`LICENSE`). PILean follows the shape of Pillow's API in places; no Pillow code
is used (`THIRD-PARTY.md`).
