# PILean design

PILean is a pure-Lean image library: what Pillow is to Python, with plots, a vector canvas and
graphs of nodes and edges on top, SVG and PNG output, and a traceability layer that ties every
image to the Lean that produced it. This note gives the planned module layout, the public API in
outline, what is exact and what is floating point, and the open choices.

## Principles

1. **Pure Lean, `Init` and `Std` only.** No FFI, no Mathlib, no large dependencies. Text in
   images goes through an interface (`TextEngine`) with a built-in lettering; LeAnTeX implements
   it in a separate package of this repository (`leantex/`, "Text in images").
2. **Values first.** An image, a figure, a drawing or a graph is a Lean value; output is a
   function of it. The same value gives the same bytes on every machine (deterministic number
   formatting, stable ordering, no clocks or randomness).
3. **Untrusted input everywhere.** Labels, data, fonts and images read from files are treated as
   hostile: escaped, bounded, checked; no panics, every loop bounded by its input.
4. **Craft.** Defaults that look deliberate without tuning: whole-pixel plot areas, hairlines on
   pixel centres, a restrained colour-blind-safe palette, typographic minus signs, consistent
   margins; visual variants are compared side by side before a default is fixed.

## Module layout

| Module | Contents | State |
|---|---|---|
| `PILean.Color` | `Rgba` (8-bit sRGB, straight alpha), `LinearRgba`, OKLab / OKLCH, gamut mapping, WCAG contrast, hex, `over`, `mixOk` | done |
| `PILean.Geometry` | `Point`, `Affine`, `Box` | done |
| `PILean.Path` | `PathCmd`, `Path`, shapes, `transform`, `flatten`, `bounds` | done |
| `PILean.Svg` | the SVG document model and writer | done |
| `PILean.Plot.Ticks`, `Scale`, `Sample`, `Figure`, `Proofs` | nice ticks (multipliers proved ascending and inside their interval), linear and logarithmic scales with minor ticks, adaptive sampling of functions, the `Figure` model (panels, axes, series, legends, annotations) drawn on the canvas | done |
| `PILean.Raster` | anti-aliased scanline fill by area coverage in integers (non-zero and even-odd), clipping to rectangles and paths, the stroker (joins, caps, miter limit, dashes), gradients, compositing in linear light, group opacity, `Draw` (in the spirit of `ImageDraw`), Gaussian blur and drop shadows, SVG nodes drawn | done |
| `PILean.Image` | `Image` (mode, size, pixels in a `ByteArray`), `getpixel`, `putpixel`, crop, paste with a mask, alpha compositing, convert, flips and quarter turns, resize (nearest, bilinear, box, Lanczos) | done |
| `PILean.Png` | PNG writer and reader: CRC-32, Adler-32, DEFLATE (stored, fixed and dynamic Huffman; inflate with every bound checked), filters, `tEXt`/`iTXt`/`zTXt`, `sRGB`, `gAMA`, `pHYs` (written); the reader takes every colour type and depth and Adam7 (the writer does not interlace) | done |
| `PILean.Anim` | a `FrameSeq` (equally sized RGBA frames, a rational delay each, a loop count) and its codecs. APNG: writer (frame differencing to the changed rectangle, equal frames merged, delays as reduced fractions) and reader (composes `dispose_op` and `blend_op`, any PNG colour type, caps on size, frames and bytes). GIF89a: writer (LZW, one global palette by median cut or the exact colours, optional Floyd–Steinberg dithering, differencing with a transparent index, delays in centiseconds with exact cumulative time, loop extension) and reader (global and local tables, interlacing, disposal 0–3, transparency, caps) | done |
| `PILean.Canvas`, `PILean.Style` | the vector canvas (`Shape`: paths with fills and strokes, text, groups with transforms, opacity and clips; gradients), written as SVG or drawn as PNG from the same SVG nodes; the `Style` record of every visual constant, `Style.light` and `Style.dark` | done |
| `PILean.Text` | `TextEngine` (measure, ascent, descent, shapes, identity, whether its strings are plain text) and the built-in single-stroke lettering that draws text into images; LeAnTeX implements it in the package `pilean-leantex` (`leantex/`) | done |
| `PILean.Anim.Animation` | an animation as a drawing over time, written as animated SVG (SMIL), APNG and GIF, with a poster frame | done |
| `PILean.Graph` | `Graph` (nodes, edges, clusters), the layered (Sugiyama) layout with spline or orthogonal edges, arrowheads, edge labels and clusters, circular and tree layouts, drawing on the canvas as SVG and PNG | done; layering proved, see below |
| `PILean.Trust` | done: SHA-256 (`Sha256`, padding and digest size proved, FIPS and NIST vectors tested); source information (module, declaration, file, line, repository, commit, version, fingerprint) written into SVG, PNG, APNG and GIF and read back by a bounded reader, `lake exe pilean-info`, see [`TRUST.md`](TRUST.md). `@[figure]` and `figures%` (declaration, file, line, source hash), fingerprints of figure specifications (SHA-256), `lake exe pilean-build` (deterministic build with `manifest.json`, `--check`) and `lake exe pilean-verify`. Later: the theorems that tie a figure to its Lean object | partly done |

## Public API in Pillow's spirit

Pillow's module split and verbs are familiar, so PILean keeps them where they fit, in Lean
idiom (values instead of mutation; `IO` only at the edges):

```lean
-- Image (Pillow: Image.new, Image.open, im.save, im.crop, im.resize, im.paste)
def Image.new (mode : Mode) (w h : Nat) (fill : Rgba) : Image
def Image.readPng (bytes : ByteArray) : Except PngError Image
def Image.writePng (im : Image) (meta : Metadata := {}) : ByteArray
def Image.crop (im : Image) (box : IntBox) : Image
def Image.resize (im : Image) (w h : Nat) (filter : Filter := .lanczos) : Image
def Image.paste (dst src : Image) (at : Nat × Nat) (mask : Option Image := none) : Image

-- ImageDraw (Pillow: draw.line, draw.rectangle, draw.ellipse, draw.polygon, draw.text)
def Draw.line (pts : Array Point) (stroke : Stroke) : Draw → Draw
def Draw.path (p : Path) (fill : Option Paint) (stroke : Option Stroke) : Draw → Draw
def Draw.text (at : Point) (s : String) (font : Font) (fill : Rgba) : Draw → Draw
def Draw.toImage (d : Draw) (w h : Nat) : Image        -- through Raster
def Draw.toSvg (d : Draw) (w h : Float) : String

-- ImageColor (Pillow: ImageColor.getrgb)
def Rgba.ofHex? (s : String) : Option Rgba             -- done
```

What PILean takes from Pillow is the shape of the API and its documented behaviour (modes such as
`L`, `RGB`, `RGBA`; box coordinates; filter names); no Pillow code (`THIRD-PARTY.md`).

## Exact and floating point

- **Exact (integers, rationals):** pixel dimensions, image buffers and their indexing, PNG and
  DEFLATE (bit-exact by construction and by round-trip tests), CRC and Adler checksums,
  fingerprints, tick values (integer multiples of a step), the manifest. Data values that come
  from Lean (`Nat`, `Int`, `Rat`) stay exact until they are mapped to the page.
- **Integers in the rasteriser:** coordinates are rounded to 1/256 pixel and everything after
  that is integer arithmetic: the cells and their areas, the coverage, compositing (16 bits a
  channel, premultiplied, in linear light) and the sRGB conversions (two tables of integers,
  `PILean/Raster/SrgbTables.lean`, written by `tools/gen-srgb.py`). The coverage is exact area
  coverage for edges on that grid, except where two edges cross inside one pixel (the usual
  approximation of both fill rules).
- **Floating point (`Float`, IEEE double):** geometry, transforms, path flattening, the
  conversion of coordinates to the 1/256 grid, a gradient's parameter at a pixel, stroke
  offsets, the weights of the bilinear and Lanczos filters, scales. The basic operations
  (`+ − × ÷ √`) are correctly rounded by IEEE 754 and so the same everywhere; the trigonometric
  functions (round caps and joins, arcs, Lanczos) come from the platform's library and may differ
  in the last bit between platforms, which moves a point by far less than the 1/256 pixel it is
  rounded to. These parts are tested against published values and goldens, not proved; the
  stated limit of the trust layer is that a figure's *content* (which function, which data
  points, which edges) is proved, its *rendering* tested.
- **Output formatting:** every number written to SVG goes through one formatter with a fixed
  number of decimals and no exponent, so output is byte-stable.

## The rasteriser

`PILean.Raster` draws paths by area coverage (`Raster/Coverage.lean` has the method): every edge
is cut at the pixel grid into pieces that add their winding (*cover*) and the area left of them
to their cell; a sweep along each row gives each pixel's winding area, which the non-zero rule
clamps to one pixel and the even-odd rule folds. Work is bounded by the image and the edges
(rows outside the image are not visited, edges left of it become vertical, right of it are
dropped), and inputs with more than four million points are refused. Strokes are the union of
one rectangle per segment, joins (miter within the limit, else bevel; round as a sector) and caps
(round as half discs), all wound the same way so that their non-zero fill has no seams; dashes
cut the flattened path first. The canvas keeps premultiplied linear light at 16 bits a channel,
composites source over destination there, and converts to 8-bit sRGB with straight alpha at
the end (the pixel model: straight alpha in `Image`, premultiplied inside). A group is drawn on
a layer of its own and composited at its opacity.

`Svg.rasterize` draws PILean's SVG nodes with it, so one description of a picture gives both
files: a figure's PNG is drawn from the nodes its SVG is written from. Measured against macOS's
SVG renderer (`tools/compare-render.py`, `sips`), the gallery's PNGs differ by 0.01 to 0.05
levels on average when PILean mixes colours as that renderer does (in sRGB); in linear light,
PILean's default, anti-aliased edges and overlaps come out lighter or darker by design.

Gradients interpolate in linear light. SVG interpolates in sRGB (its `color-interpolation`
attribute is not implemented for gradients by browsers), so PILean writes a gradient to SVG with
sixteen stops per segment sampled from its own interpolation (`gradientNode`), and both outputs
show the same colours (0.3 levels on average in the comparison).

**Blur and shadows** (`Raster/Blur.lean`). `Mask.blur` blurs a coverage mask by a Gaussian in two
separable passes over one kernel of integer weights that add up to exactly `2 ^ 16`; the weights
come from `exp (-i² / 2σ²)` evaluated with the basic operations only (`expNeg`, a series and
repeated squaring), so they are the same on every machine, and the passes are integer sums with
one rounding each. The kernel reaches `⌈3σ⌉` pixels each way; outside the mask counts as
transparent. Caps: `σ ≤ 256` and at most `4096 × 4096` pixels, and only the rows and columns the
kernel reaches from a covered pixel are visited. `Draw.dropShadow` moves a shape's coverage, blurs
it and paints it in a colour; the shape is drawn over it next. The tests compare the blur of a
straight edge with the Gaussian's cumulative distribution (within one level), keep a constant
layer exactly constant, and record the SHA-256 of a blurred disc. Pillow's `GaussianBlur`
approximates a Gaussian by three box blurs; PILean's is the sampled Gaussian itself.

The figure of a 2000 × 1200 function plot: drawing 244 ms, conversion to an 8-bit image 87 ms,
PNG encoding 689 ms (one core of an Apple M2 Ultra, under load; `lake exe pilean-test --bench`).
PNG encoding dominates (LZ77 matching and Huffman coding at level 6); drawing is dominated by the
full-image background and the canvas's 16-bit stores.

## Trust

Four parts:

1. **Source.** Every image records the Lean file and declaration that built it: SVG `<title>`,
   `<desc>` and `<metadata>` elements, a PNG `iTXt` chunk, a GIF comment (there is no `data-source`
   attribute); a site can show a "Source" link beside each image from the record or the manifest.
2. **Built by the build.** Images in a published site are produced only by the site build
   (`pilean-build`), never committed by hand; `manifest.json` and `pilean-verify` make a hand edit
   detectable, and `pilean-build --check` shows that committed files are what the build produces.
3. **Fingerprint.** A SHA-256 (pure Lean) of the figure specification's canonical encoding, of the
   source declaration's text and of where it is, written into the file and into the manifest; a
   checker re-renders and compares (`pilean-build --check`).
4. **Theorems** (done for four kinds; see `docs/PROOFS.md`). A `Figure` holds the Lean objects it shows (the function, the data term, the
   relation of a graph), and the renderer's sampling and drawing functions are stated over them:
   the plotted function is the definition; each data point is the evaluated term; each drawn edge
   is in the declared relation and every related pair is drawn. Statements first, proofs second,
   about the functions the code calls.

## Graph layout

`PILean.Graph` draws a `Graph` (labelled nodes, edges with optional labels, clusters) in layers
(`Graph.layout`, files `Graph/Layering`, `Simplex`, `Ordering`, `Coordinates`, `Layered`), or on a circle
(`circularLayout`) or as a tree (`treeLayout`), and draws the `Layout` on the vector canvas
(`Graph/Draw`), so that the SVG and the PNG show the same picture. Nothing in it depends on
Mathlib or on any other library; it follows the published algorithms, listed in the module
docstrings.

**Phases and their bounds** (`V` nodes, `E` edges, `L` layers, `D` dummy nodes, the sum of the
spans of the edges, at most `E (L - 1)`; `C` clusters):

1. *Cycle removal*: the greedy feedback arc set heuristic of Eades, Lin and Smyth; edges against
   the resulting order are reversed for the layout and drawn in their own direction. At most
   `3V + 2` steps, `O(V + E)` plus a scan of the nodes each time no source or sink is left.
   Self-loops are set aside and drawn as small loops.
2. *Layers*: the layers of least total edge span by network simplex (Gansner, Koutsofios, North
   and Vo, 1993; `Graph/Simplex`) from the longest-path layering; two balancing passes; then the
   nodes of each cluster pulled towards their cluster's median layer within the layers their
   edges leave free (`compactGroups`, so a cluster spans few layers, as dot ranks a cluster's
   nodes together); then `fixLayers`, which relaxes the edges sorted by the order of their source
   and so makes every edge point down whatever came before (proved). `O(E log V)` for the start,
   `O(V + E)` per exchange at worst. When an edge has a label the layers are doubled so that the
   label has a layer half-way along its edge.
3. *Crossing reduction*: long edges become chains of `D` dummy nodes; from a depth-first start
   order (and, up to 6000 nodes, a breadth-first and a bottom-up one, keeping the best) at most
   `sweeps` (24) rounds of weighted-median sweeps down and up (Gansner et al.) each followed by
   transposition (adjacent swaps, at most eight passes; the first pass of an up round also swaps
   pairs of equal crossings, which moves the search off a plateau; pairs whose degrees multiply to
   more than 2500 are skipped), the order with the fewest crossings kept and the rounds stopped
   after four without improvement. Crossings are counted per round in `O(E log V)` with a Fenwick
   tree (the accumulator tree of Barth, Jünger and Mutzel).
4. *Clusters* (`Graph/Compound`, after Sander's layout of compound graphs): a dummy node belongs
   to the innermost cluster holding both ends of its edge; every cluster gets a left and a right
   border node in each layer of its span, joined from layer to layer by edges that count in the
   crossing count (so an edge crossing a cluster's side is a crossing like any other); in every
   layer a cluster's nodes stand together between its borders, nested clusters inside their
   parent's block, sibling blocks in one order in every layer (the mean relative position of
   their nodes); the sweeps and transposition run under these rules from three start orders.
   `O(C L)` border nodes.
5. *Coordinates*: Brandes and Köpf's four alignments with type 1 conflict marking, balanced; then
   `refine` (8) passes towards the median of the neighbours; then network simplex on the weighted
   horizontal length of the edges (Gansner et al., section 4.2: weight 1 for two real nodes, 2 for
   one dummy, 8 for two, and an edge of the least separation between neighbours in a layer),
   started from that result. All left borders of a cluster share one variable and all its right
   borders another, with an edge between them as long as the title and of weight 1: the sides of
   a cluster are straight, and so its box holds exactly its nodes. The leaving edge is found by
   partial pricing (the most negative of the next 32 candidates); the search has a bound on the
   work (`coordinateWork`, 90 million) and returns the best assignment so far when it is used up
   (a 3000-node graph finishes about 1800 exchanges).
6. *Edges*: an edge passes a dummy node straight along the layers through the band of that
   layer's boxes, and crosses a gap as a cubic leaving and entering perpendicular to the layers;
   a step that goes sideways more than eight times the gap is drawn instead as a horizontal run
   inside the gap with rounded corners, on a track of its own (runs going right lie below the
   overlapping runs going right that start further right, so their descents do not cross; runs
   going left likewise), and a gap with many runs grows, up to three times, to keep them three
   pixels apart; or horizontal and vertical segments with rounded corners on the same tracks
   (`Routing.orthogonal`). Ends are spread along the node's side in the order of the other ends;
   arrowheads aligned with the end of the curve; labels on plates of the page colour at the middle
   of the edge.

Node boxes are whole even pixels from the label measured with the style's text engine, and each
layer is as tall as its tallest box; outlines are one pixel on pixel centres. The result of every
layout is a `Layout` of boxes and paths; the drawing is deterministic (every tie is decided by
node and edge numbers). `direction := .leftToRight` lays the layers out from left to right.

**Validity.** Edges to nodes that do not exist are dropped (`Graph.validEdges`); self-loops and
parallel edges are kept. A node belongs to the deepest cluster that lists it; a cluster's
`parent` must be listed before it. Two conditions on the finished geometry are stated as checks
that list every violation (`Graph/Check`): `clusterProblems` (every cluster box contains exactly
the nodes the cluster holds and no part of any other node's box; boxes of clusters nest when one
holds the other and are apart otherwise) and `clearanceProblems` (no edge comes within two pixels
of the box of a node it does not end at; an edge between nodes that a cluster does not hold does
not enter that cluster's box). The tests hold every measured graph to no violation of the first
and of the node part of the second; edges entering foreign clusters are counted (they are avoided
where the order allows, not always).

**Proved** (`PILean.Graph.Proofs`, axioms `propext`, `Classical.choice`, `Quot.sound` only):
`fixLayers_lt` (relaxing edges in an order in which no later edge ends where an earlier one
starts puts every target below its source, from any starting layers), `assignLayers_lt` and
`assignLayers_lt_input` (for the function the layout calls, which runs the network simplex,
balances, compacts the clusters and relaxes the result, every acyclic edge, and so every input
edge turned to point from the node that comes first, has `layer src < layer dst`, whatever the
earlier steps returned), `compactGroups_size`, and `layout_edge_indices`, `layout_edges_nodup`,
`layout_edges_complete` (the routed edges are exactly the valid input edges, in order, each once,
by index). The cluster and clearance conditions are checked, not proved.

**DOT in and out** (`Graph/Dot`): `layoutDot` reads the DOT a program would hand to
`dot -Tdot` (graphs and digraphs, node, edge and graph defaults, chains of edges, nested `cluster`
subgraphs, quoted IDs, comments; labels, shapes, colours, `rankdir`), lays the graph out and
writes laid out DOT in Graphviz's conventions (points, origin at the bottom left; the graph's
`bb`; each node's `pos`, `width`, `height`; each edge's `pos` as Bézier control points after the
arrowhead's `e,x,y`, and `lp`; each cluster's `bb` and `lp`), keeping the attributes it read. The
input is untrusted and bounded (`Dot.Limits`: bytes, nodes and edges, nesting, attributes per
item, string length); ports, HTML strings and subgraphs as edge ends are refused with a message.
`lake exe pilean-test --layout-dot FILE` runs it on a file.

**Measured** (`lake exe pilean-test --graph-quality [DIR]`; the measures are computed from the
finished layout: pairs of edges that cross, edges sharing a node not counted, on the flattened
curves; total edge length; the area of the box around nodes, clusters and edges; violations of
the two checks; time). With `DIR`, the same graphs are written as DOT with PILean's node sizes and
gaps and their clusters, and `python3 -I tools/graph-compare.py DIR` compares with Graphviz's
`dot` when it is installed. The graphs: this library's import graph and that of a project of 89
modules (names replaced by ids), the dependency graphs of two blueprints (names removed, label
lengths kept) without clusters, by chapter and, for the first, by chapter and section, random
module graphs of 800 and 3000 nodes, random dense and sparse acyclic graphs, a binary tree and a
chain with shortcuts (`PILeanTest/GraphQuality.lean`). The quality checks of `lake test` hold
every graph but the largest to bounds about a tenth above these values.

Measured with the machine's load average about 8 (both programs under the same load). Ratios are
PILean over `dot`; `dot`'s area leaves out its cluster boxes (its plain output has none), PILean's
includes them.

| Graph | Nodes, edges | Time PILean / dot (ms) | Crossings | Edge length | Area | Cluster violations | Edges passing a node | Edges entering a foreign cluster |
|---|---|---|---|---|---|---|---|---|
| own imports | 92, 205 | 37 / 41 | 1.08 | 0.87 | 0.72 | – | 0 | – |
| project imports | 88, 173 | 22 / 33 | 1.11 | 0.91 | 0.61 | – | 0 | – |
| blueprint A | 58, 146 | 16 / 28 | 1.24 | 0.94 | 0.77 | – | 0 | – |
| blueprint A by chapter | 58, 146 | 26 / 258 | 1.35 | 1.58 | 0.91 | 0 | 0 | 17 |
| blueprint A by chapter and section | 58, 146 | 28 / 61 | 1.31 | 1.72 | 1.09 | 0 | 0 | 68 |
| blueprint B | 69, 111 | 10 / 21 | 1.26 | 1.10 | 0.76 | – | 0 | – |
| blueprint B by chapter | 69, 111 | 16 / 56 | 1.12 | 1.56 | 1.20 | 0 | 0 | 25 |
| module graph | 800, 1077 | 311 / 503 | 1.38 | 1.01 | 0.65 | – | 0 | – |
| module graph | 3000, 4019 | 2076 / 3587 | 1.08 | 1.03 | 1.78 | – | 0 | – |
| dense random | 120, 387 | 47 / 52 | 1.19 | 0.76 | 0.31 | – | 0 | – |
| sparse random | 300, 325 | 27 / 36 | 1.31 | 1.26 | 0.44 | – | 0 | – |
| tree | 127, 126 | 6 / 22 | – (0 / 0) | 1.31 | 1.00 | – | 0 | – |
| chain | 80, 99 | 6 / 18 | – (0 / 0) | 1.15 | 1.14 | – | 0 | – |

Against the aim of 1.1 times `dot`'s crossings and edge length and 1.25 times its area with
correct clusters: the clusters are correct on every graph (boxes disjoint or nested, holding
exactly their nodes), no edge passes a node, and the area is within the aim everywhere except
the 3000-node graph (1.78: PILean's layering of least total span gives fewer, wider layers than
`dot`'s); edge length is within it on the graphs without clusters except the sparse graph, the
tree and the chain (PILean's ends are spread along the node's side and enter perpendicular to it;
the curves are longer than `dot`'s diagonals), and not on the clustered ones (1.56 to 1.72:
`compactGroups` shortens the clusters' spans at the cost of longer edges, and long edges leave a
cluster through its side and run outside it). Crossings are within 1.1 only on the largest graph
and the import graphs; elsewhere 1.12 to 1.38. What would close the gaps: a layering that ranks
clusters recursively as `dot` does (its own cluster skeleton), which lets the crossing reduction
move whole clusters; sifting on the layers with the most crossings; and a cheaper network simplex
exchange (the low/lim numbering of Gansner et al. for the cut search) so that the coordinate
phase can finish within the bound on larger graphs. PILean is 1.1 to 10 times faster than `dot`
on these graphs (1.7 times at 3000 nodes, where the coordinate phase takes most of the time).

## Plots

A `Figure` is a value: a size, a title, a `Style`, and panels in a grid of `columns`; a panel has
two `Axis` values, `Series` and `Annotation`s. `Figure.draw` lays it out onto the canvas and both
outputs are written from that drawing.

* **Layout.** The title, then the legend (one row of swatches and labels, wrapped, when more than
  one series is labelled), then the grid. Gutters come from measured text: the widest tick label
  of any panel, the axis labels' line heights. Plot areas have whole-pixel edges; hairlines (grid,
  axes, ticks) sit on pixel centres. Shared axes give every panel one domain and keep tick labels
  on the outer panels; a row whose horizontal tick labels are hidden keeps no room for them, so
  the rows of plot areas are evenly spaced. The data keeps `Style.plotPadding` (8 px) from the
  frame at each end (not below a zero baseline of bars or areas), so curves and markers never
  touch it.
* **Scales.** Linear axes take 1-2-5 steps (`niceTicks`) with the target number of ticks scaled
  by the axis length, and minor ticks (five or four per step); logarithmic axes take decades,
  thinned when there are many, with 2–9 times each as minor ticks. A domain from data is widened
  to whole ticks; a given domain (or the interval of function series alone) is kept. Tick labels
  have one style per axis: plain numbers, or, when a tick needs a power of ten (10⁶ and above,
  below 10⁻⁴), every tick as a multiple of the largest tick's power (`0.5×10¹⁰`, `10¹⁰`); a
  logarithmic axis labels its decades as numbers between 10⁻³ and 10⁴ and otherwise every one as
  `10ⁿ`, the exponents in superscript digits.
* **Functions** are sampled for the picture (`sampleFunction`): 64 pieces halved while the
  midpoint is more than a quarter pixel off the chord or the piece is wider than 8 pixels, down to
  14 halvings, within 6000 evaluations; values far outside the visible range are clamped first,
  so poles do not draw refinement out of sight; a piece at full depth whose ends are more than two
  pixels apart is a jump and breaks the curve.
* **Awkward data.** Non-finite values break lines and are left out of extents; non-positive values
  have no position on a logarithmic axis; a panel without data shows its axes on `[0, 1]` and a
  note; constants get an interval around them; huge values are clamped in the output (and
  labelled with powers of ten); a function's automatic range leaves out extreme tails (2 % each side)
  when they are more than twelve times the central spread away.
* **Style.** `Style` holds every visual constant; `Style.light` and `Style.dark`. The palette is
  Okabe and Ito's, ordered so that adjacent colours stay apart under colour-vision deficiencies;
  both palettes pass a palette validator's checks of lightness band, chroma, CVD and
  normal-vision separation of neighbours, on their surfaces. Text never takes a series colour.

The 2000 × 1200 function plot (`lake exe pilean-test --bench`, one core of an Apple M2 Ultra,
load average about 14): layout 3 ms, drawing 320 ms, conversion to an 8-bit image 98 ms, PNG
encoding 732 ms (159,548 bytes). PNG encoding dominates (LZ77 and Huffman at level 6), then the
rasteriser's full-image background and curve strokes.

## Text in images

Text reaches images through an interface, `TextEngine` (measure, ascent, descent, and shapes:
outlines to fill and centre lines to stroke; an identity; whether its strings are plain text),
with one implementation built in: a single-stroke lettering drawn for PILean (430 characters:
ASCII, Latin-1, Greek, scripts, math signs, arrows; tabular digits; stroke 78/1000 of the size,
drawn at least a pixel wide). With the lettering, SVG output keeps real `<text>` elements in the
style's font family (selectable, small); the layout measures text with the engine, so an SVG font
may run a little wider or narrower than the measurement. `Figure.toSvg (outlines := true)` writes
the lettering's shapes into SVG instead.

**LaTeX labels through LeAnTeX.** The package `pilean-leantex` in the folder `leantex/`
(`leantex/README.md`) implements the interface with [LeAnTeX](https://github.com/eric-vergo/LeAnTeX):
every title, axis label, tick label, legend entry and node label is LaTeX, set on one line by
LeAnTeX's text layer with formulas in `$…$` by its KaTeX-compatible math layout, and drawn as
New Computer Modern's glyph outlines. Such an engine is not `native`, so SVG writes its text as
paths (no font needed, and the document stays inert: no `text`, `use` or font reference), and
PNG goes through PILean's rasteriser. A string LeAnTeX rejects, or one longer than 1,000
characters, is drawn by the lettering instead; each string is typeset under tight caps on
tokens, expansions, nesting and line-breaking work, and the tests run hostile labels in child
processes under CPU and memory bounds. The engine's identity names the LeAnTeX commit and the
SHA-256 of every font file it reads; the fingerprint of a figure drawn with it covers that
identity (`Trust.rendererWith`), so a new LeAnTeX revision or a changed font changes the
fingerprint. Reading the fonts and hashing them takes a few seconds once per program run.

*Why a separate package and not a dependency of PILean itself:* PILean's first principle is
`Init` and `Std` only, so that any Lean program can use it without a large dependency. LeAnTeX
is a large library with about 20 MB of fonts that a program reads at run time; making it a
dependency of the core would put that weight on every user, including those who need no LaTeX.
The interface was designed for this split: the core knows only `TextEngine`, and the package in
`leantex/` (as `verso/` does for Verso) adds the dependency for those who ask for it. The
built-in lettering stays the default and needs nothing.

## Animations

An `Animation` is a drawing as a function of time, with a size, frame rate, duration and loop
count; frame `i` is the drawing at `i / fps`. Animated PNG and GIF draw every frame (the codecs
store the changed rectangle of each). The animated SVG is declarative only (SMIL `animate`, no
script): when every frame has the same elements and attribute names, it is one picture whose
changing attributes are animated between at most 30 keyframes, linearly where the values have the
same text between their numbers (path data with the same commands, coordinates, opacities) and in
steps otherwise (then every frame is a keyframe); when the frames' structure differs, each frame is
its own group shown in turn. Every animation has a poster frame (the last frame by default),
written as still SVG and PNG, and contained in the animated SVG, where a style rule shows it
instead of the motion under `prefers-reduced-motion: reduce`. `tools/anim-browser-check.py` loads
the wave and the graph-build animations in headless Chromium (through Playwright): the pictures at
0 s and 1.3 s differ, and with `prefers-reduced-motion: reduce` the motion is hidden, the picture
does not change with time and it matches the poster PNG.

A 120-frame animation of 640 × 360 pixels (the travelling wave, `lake exe pilean-test
--anim-bench`, load average about 14.5): drawing the frames 5.6 s; animated SVG 0.1 s (134,789
bytes); APNG encoding 5.9 s (1,876,963 bytes); GIF encoding 5.3 s (785,813 bytes). Drawing and
encoding share the time; the wave changes most pixels of every frame, so frame differencing
saves little here (the growing-bars animation is 63 KB as APNG).

## Open design questions

Each question has a current default, which the code follows until the question is settled.

1. **Text in SVG: outlines or `<text>`.** Outlines look the same everywhere and need no installed
   font, but are larger and not selectable; `<text>` is smaller and selectable. *Default:*
   `<text>` in SVG, outlines in PNG (and in SVG on request, `outlines := true`).
2. **Default text family.** *Default:* the built-in lettering in images, a system sans-serif stack
   in SVG; LaTeX labels in New Computer Modern with the `pilean-leantex` engine, drawn as
   outlines in both.
3. **Pixel model.** Straight or premultiplied alpha in `Image`. *Default:* straight alpha in the
   public `Image` (as Pillow's `RGBA`), premultiplied inside the rasteriser.
4. **Anti-aliasing.** Analytic area coverage or sub-row sampling. *Default:* analytic coverage
   (exact for polygons, as in font rasterisers).
5. **Default figure size and style.** *Default:* 640 × 400 px, pixels as the unit; one style,
   `Style.light` (with `Style.dark`), every constant a field of `Style`.
6. **Where figures live in a blueprint.** A Lean attribute (`@[figure]`) on a definition of type
   `Figure` that the site build renders, or explicit calls in the blueprint source. *Default:* the
   attribute, which also gives the trust layer its source declaration.
7. **Graph layout depth.** *Default:* the layered layout, with circular and tree layouts for
   small graphs; no force-directed layout.

