# PILean

A pure-Lean image library, in the role Pillow has in Python: colours, geometry, vector paths,
a drawing canvas, SVG, PNG and PDF output, plots, graphs of nodes and edges, and animations
(animated SVG, APNG, GIF).
Every image is meant to be traceable to the Lean that made it.

The drawing library (`import PILean`) depends on Lean's `Init` and `Std` only (no Mathlib), so any
Lean program can use it. The one module that needs more, `PILean.Trust.Attr` (the attribute
`@[figure]` and the build-time checks), imports `Lean`; `import PILean` does not import it, and
only code that uses the attribute or the checks does.

## Status

| Part | State |
|---|---|
| Colour: 8-bit sRGB with alpha, linear light, OKLab and OKLCH, gamut mapping, WCAG contrast, hex, compositing | done, checked against published values |
| Geometry: points, affine transforms, boxes | done |
| Paths: lines, quadratic and cubic Béziers, flattening to a tolerance, tight and control boxes | done |
| SVG writer: typed document model, deterministic output, escaping of all text | done |
| Plots: a `Figure` of panels in a grid (shared axes, equal-aspect panels, shaded bands), linear and logarithmic axes with nice major and minor ticks, grid, titles, axis labels, legends, annotations; lines (with markers), scatter, steps, areas and bands (fill between), grouped and stacked bars, histograms, functions sampled adaptively (broken at poles and jumps), error bars; light and dark styles from one `Style` record; awkward data (empty, constant, huge, non-finite) handled; labelling checks (axis labels, series named by a legend or direct labels, an explicit opt-out); SVG and PNG from the same drawing | done; see [`examples/`](examples/README.md); the integer multipliers of the tick step proved ascending and exactly the integers of their range (the floating-point tick values are tested) |
| Images: modes L, RGB, RGBA; `new`, `getpixel`, `putpixel`, `crop`, `paste` with a mask, `convert`, flips and quarter turns, `resize` (nearest, bilinear, box, Lanczos) | done; proved: the sizes of the results and that a flip twice is the identity; `resize` is tested |
| Rasteriser: anti-aliased fill by exact area coverage in integer arithmetic (non-zero and even-odd), clipping to rectangles and paths, strokes (caps, joins, miter limit, dashes), solid and gradient paints, compositing in linear light, group opacity; an `ImageDraw`-like `Draw`; Gaussian blur of an alpha layer and drop shadows, exact and deterministic | done; tested, not proved: checked against known areas and against macOS's SVG renderer; the blur against the Gaussian's closed form |
| PNG: CRC-32, Adler-32, zlib/DEFLATE (stored, fixed and dynamic Huffman with LZ77), writer (grey, RGB, RGBA, filters 0–4, `sRGB`, `gAMA`, `pHYs`, `tEXt`, `iTXt`) and reader (every colour type and depth, palette, Adam7, size caps) | done; the CRC-32 and Adler-32 code proved equal to their definitions and three facts of the zlib framing proved; the codec itself is tested, against Python's `zlib` and macOS's `sips` |
| Animated images: a `FrameSeq` written as APNG (`toApng`) or GIF (`toGif`, optionally dithered) and read back composed (`Anim.readApng`, `Anim.readGif`); frame differencing, merged equal frames, exact rational delays, size and frame caps | done; written and read back exactly (GIF when it has at most 256 colours), LZW and the quantiser tested, mutated and truncated files rejected cleanly, the files checked by `tools/anim-check.py` (Python's `zlib` and `struct`, its own LZW decoder) and by macOS's `sips` |
| Canvas: shapes, paths (with circular arcs as cubic pieces within a stated error), groups with transforms, opacity and clips, gradients, text, and per-shape metadata (accessible title and description, CSS class, id, a Lean declaration: SVG `title`, `desc`, `class`, `id` and `data-lean-decl`, left out of images); written as SVG or drawn as PNG from the same SVG nodes | done; metadata escaped, ids and classes reduced to safe characters, output inert (tested) |
| Plane figures (`PILean.Plane`): points, segments, lines and rays clipped to the frame, arrows, circles, closed disks, intersections, unions and differences of disks bounded by exact arcs, arcs, sectors, polygons and regular polygons, angle marks with an arrowhead, ticks across lines, marker shapes with halos, labels attached to a point or beside a segment, placed automatically to avoid collisions; layout checks (overlaps, undecidable incidences, recorded incidences held to the elements they name, contrast at each colour's opacity against what it is drawn on, in both themes, numbers that are not finite, radii that are not positive, colours an inline dark theme would restyle wrongly); direction controls and invisible characters dropped from labels; named colour roles with light and dark values; images composited in sRGB like browsers; narrow renditions for small screens; graphs at given positions inside a figure; explorers for web pages (a figure as a function of one or two parameters over a grid, `Explorer.family₂`, or a step sequence; every frame computed in Lean and a file of its own; proved explorers by a theorem quantified over the grid); world coordinates with `y` up and one scale for both axes, fitted with a padding into a page width (labels and markers keep their pixel sizes and are fitted too); colours by role from `Style.plane` (ink, three accents, faint, fill opacity), light and dark meeting WCAG contrast on their backgrounds; metadata on every item; LaTeX labels with `pilean-leantex`; SVG and PNG; `@[figure]` | done; see [`examples/`](examples/README.md); fitting, clipping, label placement, contrast and metadata tested |
| Exact plane points (`PILean.Exact.Plane`, `PILean.Exact.Algebraic`): the classes `Exact.RealValue` and `Exact.PlanePoint` (rational balls around a value at a requested precision), instances for rationals and integers, ℚ(√d) (its order and equality only for a `d` that is not a square, `QSqrt.NonSquare`), ℤ[ζ₅], exact square roots, midpoints, feet, circle–circle and line–circle meetings (two points, a tangent point, none, undecided, or degenerate for a radius not decided positive) as enclosures, divisions undefined on a ball holding 0, exact incidence with a disk, builders of plane items from exact points, specifications that write out a figure's items | done; proved: a rational point is its own ball and is drawn at its converted coordinates, and an exact point is drawn as a marker at the frame's image of its conversion (a figure of points: one marker each, in order); the gallery's disks, `zetaSteps` and reference figure and the LeAnTeX example write out every item they draw (labels with their text, point and placement, colours, titles, recorded incidences), which `lake test` checks by changing the figures and requiring each change to break the specification, and check their recorded incidences by exact arithmetic in ℚ(√5) computed from ℤ[ζ₅]; not pinned: the layout, fonts, the style's colour values and the pixels; worked instances for ℚ(√5) and ℤ[ζ₅] in the tests, their balls checked exactly by squaring |
| Text in images: a `TextEngine` interface; the built-in single-stroke lettering (430 characters: ASCII, Latin-1, Greek, scripts, math signs, arrows, typographic punctuation) draws labels into PNGs; SVG keeps real `<text>` | done ([specimen](examples/lettering-specimen.png)) |
| LaTeX labels: the package `pilean-leantex` (folder [`leantex/`](leantex/README.md)) typesets titles, axis and tick labels, legends and node labels with [LeAnTeX](https://github.com/eric-vergo/LeAnTeX), drawn as glyph outlines in SVG and PNG | done; goldens, inert SVG, hostile labels under CPU and memory bounds ([gallery](leantex/examples/)) |
| PDF for papers: every picture as a one-page vector PDF 1.7 written in pure Lean (paths, fills by both rules, strokes with caps, joins, miter limit and dashes, opacities, transparency groups, clips, gradients as shadings, raster images with soft masks; text as outlines, so no fonts; deterministic bytes); the source record in the information dictionary; `Pdf.check`, a structural check of PDF files (bounded: each page-tree node read once, each stream decoded once, at most 32 MiB of decoded content per document, every use counted) | done; every gallery PDF passes the check in `lake test` (planted faults refused, mutated files read without a crash; hostile files, among them page trees that list a node twice and streams that inflate to 200 MiB used by many pages, refused within bounds of 1 s of CPU and 80 MiB that the probe measures; about 0.2 s and 10 MiB on the development machine) and `qpdf --check`; rendered by Ghostscript and Quick Look and compared with the PNGs (`tools/pdf-compare.py`); see [Formats](#formats) |
| Animations: one `Animation` (a drawing as a function of time, frame rate, duration, loops) written as animated SVG (SMIL only, interpolated attributes or frame switching), APNG and GIF, with a poster frame for reduced motion | done; outputs read back by PILean's readers and opened by macOS's ImageIO; the animated SVGs of the gallery checked in headless Chromium (frames differ with time, poster shown under reduced motion, `tools/anim-browser-check.py`) |
| Graphs: nodes, edges and nested clusters; layered (Sugiyama) layout with cycle removal, network simplex layering, weighted-median crossing reduction with sifting and seeded starts, and under cluster constraints, Brandes–Köpf and network simplex coordinates, spline or orthogonal edges that keep clear of nodes, or bundled orthogonal edges (one entry and one exit port per node with shared stems, tracks in channels, parallel lanes with concentric corners), arrowheads, edge labels; circular and tree layouts, layouts at given positions (edges straight or bent around nodes); components laid out apart and packed, mirrored layouts; a bounded DOT reader and laid-out DOT writer; SVG and PNG, and SVG for a web page (classes, ids and titles on nodes, edges and clusters) | done; proved: after cycle removal every edge between two different nodes points to a deeper layer (by a final repair pass; self-loops are drawn apart) and the layout has one route per valid edge (both ends among the nodes); where nodes and routes lie is tested (cluster boxes, edge clearance); compared with Graphviz's `dot` in [`docs/DESIGN.md`](docs/DESIGN.md) |
| Diagrams of algebra (`PILean.Diagram`): commutative diagrams (objects at exact positions; arrows straight, bent, parallel or loops, with the tips of monomorphisms, epimorphisms, isomorphisms, inclusions, equalities, `↦` and dashed arrows; labels beside them; 2-cells), Cayley tables (a colour per element) and Cayley graphs (a colour per generator) of finite groups given by their tables, quivers with dimension vectors, Hasse diagrams with marked elements (the normal subgroups among the subgroups) | done; see the table of kinds below; proved for each kind: every mark, class by class, is the builder's at its exact position (arrow bodies = the data's arrows with their ends, texts = their labels; cell `(a, b)` holds `a * b` in the colour of `a * b`); decidable on finite data: that maps between finite sets make a diagram commute and fit the marks of their arrows, that a table is a group; `pilean-mathlib` states commutation, `Mono`/`Epi`/`IsIso` and exactness for morphisms of a category, and binds tables, Cayley graphs and lattices of subgroups to Mathlib's groups |
| Combinatorial diagrams (`PILean.Diagram`): finite graphs and digraphs on circles, grids or given exact positions (or the layered layout), Hasse diagrams of finite orders, Young diagrams and tableaux (English and French), permutations (one-line and two-line notation, matrix, cycles, wiring diagram), rooted trees and forests and binary trees (tidy layout of Reingold and Tilford), set systems (Venn diagrams of up to three sets, incidence drawings), lattice and Dyck paths, polyominoes and Ferrers boards; drawn from plain data in exact rational coordinates as plane figures, light and dark; caps on every kind | done; see the table of kinds below and [`examples/`](examples/README.md); proved for each kind: the drawn parts, read back from the diagram, are exactly the parts of the data, in order, at the layout's exact positions (edges = relation, Hasse edges = covers with the strict order their transitive closure, cells `(i, j)` with `j < λᵢ`, entries = filling, wiring crossings = inversions, Venn regions = membership); the layouts' qualities and everything after the exact marks are tested |
| Analysis and number theory (`PILean.Diagram`): plots of sequences with comparison curves (axes apart from the points, round ticks, points sized by their number), grids of numbers (tables, sieves, the Ulam spiral), lattices of the plane with their fundamental parallelogram and marked points, zeros and poles of rational functions with their multiplicities; domain colouring of complex functions as an openly marked illustration | done; see the table of kinds below; proved for each kind: every mark, class by class, is the builder's at its exact position (points = `(n, f n)` on the range, cells = the data, dots = the lattice points of the window); `pilean-mathlib` states the gallery's figures against `Nat.totient`, `σ 0`, `Nat.primeCounting`, `Nat.Prime`, `legendreSym`, `Prime` in `GaussianInt` and `Submodule.span ℤ`, soundness and completeness both, and checks that changed figures break their theorems |
| Source information: the Lean declaration, file, line, repository, commit and version recorded in SVG (`<metadata>`, `<title>`, `<desc>`), PNG and APNG (`iTXt`), GIF (comment) and PDF (information dictionary) files and read back by a size-capped reader; `lake exe pilean-info FILE` prints it; SHA-256 in pure Lean; `Svg.isInert` checks that an SVG runs no script and loads nothing | done; see [`docs/TRUST.md`](docs/TRUST.md); round trips tested on every format with hostile input, SHA-256 against FIPS and NIST vectors and `shasum`, padding and digest size proved |
| Standing of a figure: `linked` (a theorem linked by `figure_links` passes its rule: it is proved from the standard axioms and its statement names the figure; what it says is not checked) or `illustration` (`@[figure illustration]` marks one openly); recorded in each file's source record and the manifest, printed by `pilean-info` and `pilean-verify`; `pilean-build --require-standing` refuses a figure that is neither | done; see [`docs/TRUST.md`](docs/TRUST.md) ("Standing") |
| Traceable builds: the attribute `@[figure]` and the term `figures%` collect the figures of a project; fingerprints (SHA-256 of the drawing's SVG encoding, the declaration's source text and position, and the version); `lake exe pilean-build` renders them deterministically with a `manifest.json` (`--check` compares a directory with the build), `lake exe pilean-verify DIR` checks a directory against its manifest | done; see [`docs/TRUST.md`](docs/TRUST.md) (including use in CI); tested end to end with damaged, missing, extra and hostile files |
| Theorems about a figure and its Lean object: a plot of an exact function on the rationals (the plotted points are exactly its values on a stated grid; nothing is proved between two samples), a data plot (the points are the input list), a graph (nodes and edges are the relation and the layout has one route per edge), an animation (frame `i` is the drawing at `i / fps`) and a plane figure of exact points (each point drawn at the frame's image of its conversion). The theorems are about exact numbers and lists; the step from them to pixels is floating point and tested, not proved | done for these five; see [`docs/PROOFS.md`](docs/PROOFS.md) for what is proved, tested and trusted; one example of each in the gallery |
| Real-number bounds: the optional package `pilean-mathlib` (folder [`mathlib/`](mathlib/README.md), requires Mathlib) states over ℝ what it means for the polyline through exact samples to be within `δ` of the graph of a function, measured vertically, and proves the bound `ε + M h² / 8` from an error `ε` at the grid points and `\|f''\| ≤ M` | done: one general theorem and, as a kind (`CertifiedPlot`), certified plots of the sine, exponential, cosine, logarithm, arctangent and square root, each with its interval, number of steps and bound proved (from 1/1000 to 1/8000; [pictures](mathlib/README.md)); in the gallery's 640 × 400 pixel pictures the bound is at most 0.072 of a pixel on the vertical axis (from 0.026 for the logarithm to 0.072 for the cosine), which `lake test` checks in floating point against a tenth of a pixel and which is not proved; the step from the exact numbers to pixels is floating point and tested, not proved |

## Kinds of combinatorial diagrams

Each kind has plain data, a pure layout, a builder of a `Diagram`, a decidable `Faithful`
predicate that reads the diagram back and compares it with the data, and a theorem that the
builder satisfies it. The package `pilean-mathlib` binds each to Mathlib's object.

| Kind | Data | Theorem (exact marks) | Mathlib object |
|---|---|---|---|
| Graph, digraph (`FinGraph`) | `adj : Fin n → Fin n → Bool` | drawn edges = related pairs | `SimpleGraph.Adj`, `Digraph.Adj` |
| Hasse diagram (`FinPoset`) | `le : Fin n → Fin n → Bool` | drawn edges = covers; their transitive closure = the strict order | `CovBy` (`⋖`) of a `PartialOrder` |
| Young diagram (`YoungShape`) | row lengths `λ` | cell `(i, j)` drawn iff `j < λᵢ` | `YoungDiagram.cells`, `Nat.Partition` |
| Tableau (`Tableau`) | rows of entries | cells and written entries = the filling | `SemistandardYoungTableau` |
| Permutation (`FinPerm`) | one-line notation | matrix cells `(i, σ i)`; cycle arrows `i → σ i`; wiring crossings = inversions | `Equiv.Perm (Fin n)` |
| Forest, binary tree (`Forest`, `BinTree`) | parent links, children | drawn edges = parent links | |
| Set system (`SetSystem`) | sets of `0, …, n - 1` | Venn: written inside circle `s` iff in set `s`; incidence edges = membership | `Finset (Fin n)` |
| Lattice path, Dyck path (`LatticePath`) | integer steps | step `k` drawn from point `k` to point `k + 1` | `DyckWord` |
| Polyomino, Ferrers board (`Polyomino`) | cells | drawn cells = the cells | |
| Commutative diagram (`CommDiagram`) | objects (labels, positions), arrows (ends, label, style, bend), 2-cells, claims of commuting paths | drawn arrow bodies = the arrows with their ends; texts = labels; every tip, hook, bar and label the builder's; `FinMaps.Commutes` and `FinMaps.StylesHold` decide commutation and the arrows' marks for maps between finite sets | `CommSq`, `f ≫ g = h`, `ShortComplex.ShortExact`, `Mono`, `Epi`, `IsIso` (`CommDiagram.Realisation`) |
| Cayley table, Cayley graph (`FinMagma`) | a table on `Fin n`, generators | cell `(a, b)` holds `a * b`, in the colour of `a * b`; arrows `g → g * s` in the colour of `s`; `isGroup` decided on the table | `Group` through `Fin n ≃ G`, `Subgroup.center` |
| Lattice of subgroups (`FinPoset` with `marked`) | a finite order, marked elements | edges = covers; a dot in accent exactly when marked | `Subgroup G`, `⋖`, `Subgroup.Normal` |
| Quiver (`FinQuiver`) | vertices, arrows (several between two vertices, loops), a dimension vector | drawn arrows = the arrows with their ends and names; vertex labels = the dimensions | |
| Plot of sequences (`SeqPlot`) | a range `lo, …, hi`, sequences `ℕ → ℚ` with names, comparison curves | drawn points = `(k, n, point n (f n))` for every sequence and index; curves = the polylines through their values; axes, ticks, labels and legend the builder's | `Nat.totient`, `σ 0`, `Nat.primeCounting`, `harmonic` |
| Grid of numbers (`CellPlot`) | cells (key, position, mark, text), headings; `ulamCells` | drawn cells and texts = the data's, in the colour of their mark | `Nat.Prime`, `IsSquare` in `ZMod p`, `legendreSym` |
| Lattice of the plane (`PlaneLattice`) | two rational periods, a window, a marking | drawn dots = the candidates `m ω₁ + n ω₂` in the window, in the colour of their mark; the fundamental parallelogram | `Submodule.span ℤ {ω₁, ω₂}`; `Prime` in `GaussianInt` |
| Zeros and poles (`RationalPlot`) | rational coefficients of a numerator and a denominator, zeros and poles as Gaussian rationals with multiplicities, a window | circles = the zeros, crosses = the poles, written multiplicities = those above 1; decided: each a root of exactly its multiplicity (`Verified`), the multiplicities adding up to the degrees (`Complete`) | `Polynomial.rootMultiplicity` over ℂ; every complex root marked (`Polynomial.roots`) |
| Domain colouring (`DomainColouring`) | a `Float` function, a window | none: an illustration, marked `@[figure illustration]`, raster (PNG and PDF) | |

## Formats

| Format | Written by | Holds | Source record |
|---|---|---|---|
| SVG | `toSvg` of every picture | the drawing, text as text or as outlines, accessible names, declaration links | `<metadata>` with a `pilean:source` element |
| PNG | `toPng` | the drawing rasterised by PILean (text as outlines) | `iTXt` chunks |
| APNG, GIF | `Animation.toApng`, `toGif` | every frame of an animation | `iTXt` chunks; a comment |
| PDF | `toPdf` of every picture, `Image.toPdf` | one vector page, `0.75` points per pixel, text as outlines (no fonts), gradients as shadings | the document information dictionary |

`pilean-build` writes a figure's SVG, PNG and PDF (and an animation's APNG, GIF and still frames),
each with its source record; `pilean-info` and `pilean-verify` read every format.

## Use

```lean
import PILean
open PILean PILean.Plot

def fig : Figure where
  title := "Trigonometric functions"
  panels := #[{
    x := { label := "x" }, y := { label := "y" },
    series := #[.function "sin x" Float.sin (-3.14) 3.14,
      .function "cos x" Float.cos (-3.14) 3.14] }]

#eval IO.FS.writeFile "sin.svg" fig.toSvg
#eval match fig.toPng with
  | some png => IO.FS.writeBinFile "sin.png" png
  | none => pure ()
#eval IO.FS.writeFile "sin-dark.svg" { fig with style := Style.dark }.toSvg
```

This picture has no theorem: `Series.function` samples a floating-point function (`Float.sin`
is the platform's) adaptively, which is tested, not proved. The plots with a theorem are those of
exact functions on the rationals and of exact data, `Series.ofExact` and `Series.ofIntPoints`
([`docs/PROOFS.md`](docs/PROOFS.md)).

A graph is a value too, laid out in layers (or on a circle, or as a tree) and written as SVG or
PNG (this block and the next continue a file that starts with `import PILean`):

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

## Manual

The manual is a Lean program: a Verso site in the package [`manual/`](manual/), which depends on
the core and on `pilean-verso-manual` by path. Its examples are elaborated and their printed
results produced when it is built, its figures are drawn by PILean (light and dark), and its API
reference has one page per module, read from the library's docstrings. To build it:

```
cd manual
lake exe pilean-manual --output _out
```

and open `_out/html-multi/index.html` through a local web server (the pages use paths from the
site's root), for instance `python3 -m http.server --directory _out/html-multi`. `lake test` in
`manual/` checks that every module has its page (`lake exe pilean-manual-pages` writes the page
files), that every public declaration of the core is documented or on the manual's allow-list,
and a generated site. The workflow `.github/workflows/manual.yml` builds the manual and uploads
the site as a GitHub Pages artifact when it is started by hand.

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
lake exe pilean-test --pdf-out /tmp/pilean-pdf && python3 -I tools/pdf-compare.py /tmp/pilean-pdf --qpdf
lake exe pilean-test --anim-out /tmp/pilean-anim && python3 -I tools/anim-check.py /tmp/pilean-anim
lake exe pilean-test --bench
lake exe pilean-test --graph-bench
lake exe pilean-test --graph-quality /tmp/pilean-graphs && python3 -I tools/graph-compare.py /tmp/pilean-graphs
lake exe pilean-test --graph-quality-files PILeanTest/graphs /tmp/pilean-graph-files && python3 -I tools/graph-compare.py /tmp/pilean-graph-files
```

The first decodes PILean's zlib streams and PNGs with Python's `zlib`; the second renders the
gallery's SVGs with `sips` and compares their pixels with PILean's PNGs; the next renders the
gallery's PDFs with Ghostscript (`gs`) and Quick Look (`qlmanage`) and compares them with PILean's
PNGs, and checks each with `qpdf --check` when that is installed; the next composes the
sample APNG and GIF files with a decoder written in Python and checks that both formats show the
same frames. The last compares the layered graph layout with Graphviz's `dot` (when it is on the
path) by crossings, edge length and area. `python3 tools/anim-browser-check.py` loads the
animated SVGs of the gallery in a headless Chromium through Playwright, when that is installed, and
checks that the picture changes with time and that reduced motion shows the poster frame.

## Trust model (outline)

PILean treats what it is given as untrusted: text in a figure (titles, labels) is escaped before it
reaches SVG, characters XML cannot carry are dropped, element and attribute names are checked, and
every loop is bounded by its input (curve flattening has a cap per curve). The traceability layer
records in each image the Lean file and declaration that produced it and a fingerprint of the
drawing and the declaration, with a manifest and two checkers (`pilean-build --check`,
`pilean-verify`); theorems tie a figure to the Lean object it shows
([`docs/PROOFS.md`](docs/PROOFS.md)). PNG and DEFLATE data read from files are untrusted: every
length is checked, the output size is capped, and mutated files end in clean errors. With the
default limits, reading a PNG of `n` bytes holds at most the input, its image data (at most `n`
bytes), the data of one other chunk at a time with the strings decoded from it, the text entries
(their strings with 128 bytes for each entry at most `Limits.maxTextBytes`, 4 MiB; an entry over the
budget, or a malformed one, is dropped and counted), and two buffers whose sizes together are at
most `Limits.maxBytes` (512 MiB), allocated only after the header has been checked against the caps;
its work is linear in those sizes. The buffer of the image data is sized from the header (after a
check that the compressed data is long enough for it) and inflating stops at its end; a zlib stream
decoded without an expected size is measured before its output is allocated, so a bomb is refused
without its output. GIF and APNG hold the composed frames (at most `Limits.maxBytes`, checked before
each frame is decoded) and a constant number of frame-sized buffers. These bound the buffers the
readers allocate, not the memory of the whole process. The graph layout's work is bounded by the
numbers of nodes and edges and two work budgets (`LayeredOptions.layerWork`, `coordinateWork`), with
a cap on dummy nodes (`maxLayoutNodes`: past it no edge gets dummy nodes; the real nodes are not
capped); `docs/DESIGN.md` gives the cost of each phase, some of them quadratic in the size of one
layer or gap. The command-line tools read only regular files, follow no symbolic link below the
folder they are given, and print what they read escaped. `lake test` runs the readers, the layout
and the tools on hostile inputs in child processes and checks their memory and CPU time
(`PILeanTest/Bounds.lean`, `PILeanTest/Tools.lean`). The rasteriser computes coverage in integers
from outlines on a grid of 1/256 pixel, so the same outlines give the same coverage on every
machine; the colour of a pixel also depends on its paint, the clips and the compositing ("Exact and
floating point" in `docs/DESIGN.md`), and the outlines themselves are computed in floating point.
The rasteriser is tested, not proved. `docs/DESIGN.md` has the details and the open choices.

## Licence

Apache License 2.0 (`LICENSE`). PILean follows the shape of Pillow's API in places; no Pillow code
is used (`THIRD-PARTY.md`).
