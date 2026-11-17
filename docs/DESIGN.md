# PILean design

PILean is a pure-Lean image library: what Pillow is to Python, with plots, a vector canvas and
graphs of nodes and edges on top, SVG and PNG output, and a traceability layer that ties every
image to the Lean that produced it. This note gives the module layout, the public API in
outline, what is exact and what is floating point, and the open choices.

## Principles

1. **Pure Lean, `Init` and `Std` only.** No FFI, no Mathlib, no large dependencies. Text in
   images goes through an interface (`TextEngine`) with a built-in lettering; LeAnTeX implements
   it in a separate package of this repository (`leantex/`, "Text in images").
2. **Values first.** An image, a figure, a drawing or a graph is a Lean value; output is a
   function of it. The same value gives the same bytes on every run (deterministic number
   formatting, stable ordering, no clocks or randomness), and on every machine as far as the
   floating-point steps agree ("Exact and floating point" says where the platform's library can
   differ in a last bit).
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
| `PILean.Graph` | `Graph` (nodes, edges, clusters), the layered (Sugiyama) layout with spline or orthogonal edges, arrowheads, edge labels and clusters, circular and tree layouts, components laid out apart and packed, mirrored layouts, drawing on the canvas as SVG and PNG, and as SVG for a web page | done; layering proved, see below |
| `PILean.Trust` | done: SHA-256 (`Sha256`, padding and digest size proved, FIPS and NIST vectors tested); source information (module, declaration, file, line, repository, commit, version, fingerprint) written into SVG, PNG, APNG and GIF and read back by a bounded reader, `lake exe pilean-info`, see [`TRUST.md`](TRUST.md). `@[figure]` and `figures%` (declaration, file, line, source hash), fingerprints of figure specifications (SHA-256), `lake exe pilean-build` (deterministic build with `manifest.json`, `--check`) and `lake exe pilean-verify`; `figure_proves` links a figure to a theorem about it ([`PROOFS.md`](PROOFS.md)) | done |

## Public API in Pillow's spirit

Pillow's module split and verbs are familiar, so PILean keeps them where they fit, in Lean
idiom (values instead of mutation; `IO` only at the edges):

```lean
-- Image (Pillow: Image.new, Image.open, im.save, im.crop, im.resize, im.paste)
def Image.new (mode : Mode) (width height : Nat) (fill : Rgba := ⟨0, 0, 0, 255⟩) : Image
def Image.readPng (bytes : ByteArray) (lim : Png.Limits := {}) : Except Png.PngError Image
def Image.writePng (im : Image) (md : Png.Metadata := {}) : Except Png.PngError ByteArray
def Image.crop (im : Image) (x0 y0 x1 y1 : Int) : Image
def Image.resize (im : Image) (w h : Nat) (filter : Filter := .box) : Image
def Image.paste (dst src : Image) (x y : Int) (mask : Option Image := none) : Image

-- ImageDraw (Pillow: draw.line, draw.rectangle); in the namespace PILean.Raster
def Draw.new (w h : Nat) (bg : Rgba := ⟨255, 255, 255, 255⟩) (space : Space := .linear) : Draw
def Draw.line (d : Draw) (pts : Array Point) (paint : Paint) (width : Float := 1)
    (cap : Cap := .butt) (join : Join := .miter) : Draw
def Draw.rectangle (d : Draw) (x0 y0 x1 y1 : Float) (fill : Option Paint := none)
    (outline : Option Paint := none) (width : Float := 1) : Draw
def Draw.toImage (d : Draw) (mode : Mode := .rgba) : Image

-- ImageColor (Pillow: ImageColor.getrgb)
def Rgba.ofHex? (s : String) : Option Rgba
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
4. **Theorems** (for four kinds of picture; see `docs/PROOFS.md`). A series built with
   `Series.ofExact` or `Series.ofIntPoints`, a graph built with `Graph.ofRelation` and an
   `Animation` have theorems about the exact objects they are built from: the plotted points are
   the exact samples of the function on a stated grid, or the data list, converted one by one;
   the layout has one route for each related pair; frame `i` is the drawing at `i / fps`. The
   statements are about exact numbers and lists and about the functions the code calls. The
   steps from there to pixels (the conversion to floating point, the scales, the rasteriser) are
   tested, not proved, and nothing is proved about a curve between two samples.

## Graph layout

`PILean.Graph` draws a `Graph` (labelled nodes, edges with optional labels, clusters) in layers
(`Graph.layout`, files `Graph/Layering`, `Simplex`, `Ordering`, `Coordinates`, `Layered`; with the components laid out apart and packed, `Graph.layoutPacked`, `Graph/Pack`), or on a circle
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
   order (and, up to 6000 nodes, a breadth-first and a bottom-up one, and more depth-first
   orders from a fixed pseudo-random sequence, `initialLayersSeeded`, keeping the best) at most
   `sweeps` (24) rounds of weighted-median sweeps down and up (Gansner et al.) each followed by
   transposition (adjacent swaps, at most eight passes; the first pass of an up round also swaps
   pairs of equal crossings, which moves the search off a plateau; pairs whose degrees multiply to
   more than 2500 are skipped), the order with the fewest crossings kept and the rounds stopped
   after four without improvement. Every such search ends with *sifting* (`siftFrom`, after
   Matuszewski, Schönfeld and Molitor, *Using sifting for k-layer straightline crossing
   minimization*, Graph Drawing 1999, LNCS 1731): in rounds over all layers, alternately down and
   up, each node of a layer, the nodes of most edges first, is taken out and put at the place
   among the others where its edges cross the fewest of theirs (one merge of two sorted position
   lists, `crossBothWays`, per pair of nodes, so `O(k² d)` for a layer of `k` nodes of mean degree
   `d`; on a tie the node stays as near as it can to where it stood), each round followed by
   transposition; at most 12 rounds, stopped after two without improvement, and skipped when the
   layers hold more than `siftPairLimit` (6 million) pairs of nodes in all. The extra starts have
   a bound on the work too: `extraStarts` makes as many (at most 24) as `extraStartWork` (600,000
   pairs of nodes of one layer, summed over the layers, per start) allows for the size of the
   layered graph, so a large graph gets none. Crossings are counted per round in `O(E log V)`
   with a Fenwick tree (the accumulator tree of Barth, Jünger and Mutzel). The seeded starts
   and the sifting are tested for what they promise (a permutation of every layer, never more
   crossings, the same result on every run), not proved.
4. *Clusters* (`Graph/Compound`, after Sander's layout of compound graphs): a dummy node belongs
   to the innermost cluster holding both ends of its edge; every cluster gets a left and a right
   border node in each layer of its span, joined from layer to layer by edges that count in the
   crossing count (so an edge crossing a cluster's side is a crossing like any other); in every
   layer a cluster's nodes stand together between its borders, nested clusters inside their
   parent's block, sibling blocks in one order in every layer (the mean relative position of
   their nodes); the sweeps and transposition run under these rules from three start orders (the unconstrained order of phase 3 is one of them; the seeded starts and sifting of phase 3 do not run under the cluster rules).
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
   a step that goes sideways more than eight times the gap is one cubic too, whose long sideways
   stretch runs at the height of a track of its own (the tracks of steps going right lie below
   those of the overlapping steps going right that start further right, so that their descents
   do not cross; steps going left likewise), and a gap with many such steps grows, up to three
   times, to keep them three pixels apart; or horizontal and vertical segments with rounded corners on the same tracks
   (`Routing.orthogonal`). Ends are spread along the node's side in the order of the other ends;
   arrowheads aligned with the end of the curve; labels on plates of the page colour at the middle
   of the edge.

Node boxes are whole even pixels from the label measured with the style's text engine (or, for a node with a `size`, that size made whole and even, for a caller that measures its labels itself), and each
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

**Components packed** (`Graph/Pack`). `Graph.layoutPacked` lays every connected component out on
its own (`Graph.layout`'s phases) and packs the drawings into rows instead of one wide row of
layers. Two nodes are in one component when a valid edge joins them or when one top cluster holds
both (a cluster's box must stay whole, so its members and the clusters inside it form one
component; a graph whose one cluster holds every node is therefore one component). The drawings
are sorted by height, the tallest first (the first node first among equals), and put on shelves
from left to right, a new shelf starting when the next drawing would pass the width
`sqrt (aspect × area)` (the shelf algorithm *next fit decreasing height* of Coffman, Garey,
Johnson and Tarjan, *Performance bounds for level-oriented two-dimensional packing algorithms*,
SIAM Journal on Computing 9, 1980), `gap` apart; the work besides the layouts is `O(k log k)` for
`k` components. A graph of one component gets `Graph.layout`'s layout. Packing cannot make a
drawing narrower than its widest component: a node with 400 neighbours stands with them in one
layer. `Layout.mirror` turns a layout upside down or left to right (boxes, routes, arrowheads and
label plates keep their sizes), which is how layers that run from the bottom up or from right to
left are drawn: the layout of the opposite direction, mirrored.

**Output for a web page** (`Graph/Web`). `Layout.toWebSvg` writes a layout as one SVG element to be
put into a page and styled there: a `g` with class `node` for every node (with its `id`, classes,
a `title`, an optional `desc`, the outline as a `path` or an `ellipse`, and one `text` per line
of the label), a `g` with class `edge` for every edge (the curve and, for a directed edge, a
`path` with class `head`), a `g` with class `cluster` for every cluster, and the colours as plain
presentation attributes that a stylesheet overrides by class. The text is SVG text in the page's
font, so the caller sizes the nodes for it: `Graph.Node.size`, with `sansWidth` (the width of a
line in a sans-serif face of Helvetica's metrics) as the measure. The output carries no script,
link, style attribute or event handler and `Svg.isInert` accepts it; what the caller passes
(ids, classes, names, tooltips, lines, colours, attributes) is escaped as text or as an attribute
value. `isInert` refuses `javascript:` and `data:` inside an attribute value, so an `id` that
contains one makes the check fail, although the escaped text would do no harm; in text positions
(name, tooltip, lines) they are accepted. These functions are tested (`PILeanTest/GraphOrder.lean`),
not proved.

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

**Measured** (`lake exe pilean-test --graph-quality [DIR]` for the built-in graphs and
`--graph-quality-files PILeanTest/graphs [DIR [packed]]` for the graph files; the measures are
computed from the finished layout: pairs of edges that cross, edges sharing a node not counted,
on the flattened curves; total edge length; the area of the box around nodes, clusters and edges;
violations of the two checks; time). With `DIR`, the same graphs are written as DOT with PILean's
node sizes and gaps and their clusters, and `python3 -I tools/graph-compare.py DIR` compares with
Graphviz's `dot` when it is installed. The built-in graphs: this library's import graph and that
of a project of 89 modules (names replaced by ids), the dependency graphs of two blueprints
(names removed, label lengths kept) without clusters, by chapter and, for the first, by chapter and
section, random module graphs of 800 and 3000 nodes, random dense and sparse acyclic graphs, a
binary tree and a chain with shortcuts (`PILeanTest/GraphQuality.lean`). The graph files
(`PILeanTest/graphs/`, described in its `README.md`; names removed, label lengths kept) are a code
site of about 2,900 declarations in 85 modules (code site C), its modules and its largest module,
and views of the neighbourhood of one declaration of 34 to 401 nodes. Graphviz's numbers are the
recorded ones in `PILeanTest/graphs/dot-recorded.tsv` (Graphviz 16.1.0), so that `lake test` needs
no `dot`: it holds every graph but the two largest (the 3000-node module graph and code site C)
to no cluster violation, no edge passing a node, crossings and edge length within a ratio of the
recorded ones (a constant per graph, about 0.1 above the measured ratio), and, for the older
graphs, to bounds about a tenth above the values measured.

Measured with the machine's load average about 8 to 11 (both programs under the same load).
Ratios are PILean over `dot`; `dot`'s area leaves out its cluster boxes (its plain output has
none), PILean's includes them. Times are one run each: PILean's layout alone, and `dot` on the
file (including its start).

| Graph | Nodes, edges | Time PILean / dot (ms) | Crossings | Edge length | Area | Cluster violations | Edges passing a node | Edges entering a foreign cluster |
|---|---|---|---|---|---|---|---|---|
| own imports | 92, 205 | 273 / 40 | 1.04 | 0.90 | 0.75 | – | 0 | – |
| project imports | 88, 173 | 132 / 35 | 0.75 | 0.93 | 0.77 | – | 0 | – |
| blueprint A | 58, 146 | 159 / 27 | 1.01 | 0.85 | 0.70 | – | 0 | – |
| blueprint A by chapter | 58, 146 | 88 / 63 | 1.29 | 1.04 | 0.85 | 0 | 0 | 8 |
| blueprint A by chapter and section | 58, 146 | 90 / 59 | 1.19 | 1.64 | 1.09 | 0 | 0 | 69 |
| blueprint B | 69, 111 | 52 / 20 | 1.07 | 1.16 | 0.77 | – | 0 | – |
| blueprint B by chapter | 69, 111 | 43 / 55 | 1.10 | 1.54 | 1.20 | 0 | 0 | 26 |
| module graph | 800, 1077 | 1432 / 513 | 1.23 | 0.96 | 0.64 | – | 0 | – |
| module graph | 3000, 4019 | 6070 / 3545 | 0.86 | 0.82 | 1.29 | – | 0 | – |
| dense random | 120, 387 | 304 / 48 | 1.05 | 0.75 | 0.34 | – | 0 | – |
| sparse random | 300, 325 | 193 / 34 | 0.92 | 1.11 | 0.50 | – | 0 | – |
| tree | 127, 126 | 6 / 22 | – (0 / 0) | 1.30 | 1.00 | – | 0 | – |
| chain | 80, 99 | 7 / 18 | – (0 / 0) | 1.15 | 1.14 | – | 0 | – |
| code site C | 2866, 5516 | 775 / 1654 | 1.26 | 3.35 | 1.63 | 0 | 0 | 5682 |
| code site C, its modules | 85, 159 | 175 / 34 | 1.13 | 1.02 | 0.75 | – | 0 | – |
| code site C, its largest module | 561, 422 | 148 / 81 | 0.02 | 0.98 | 2.24 | 0 | 0 | 0 |
| neighbourhood, a node with 400 neighbours | 401, 400 | 13 / 33 | – (0 / 0) | 1.01 | 1.73 | – | 0 | – |
| neighbourhood of 290 nodes | 290, 793 | 1564 / 165 | 0.86 | 0.82 | 1.20 | – | 0 | – |
| neighbourhood of 150 nodes | 150, 468 | 931 / 156 | 0.77 | 0.69 | 0.71 | – | 0 | – |
| neighbourhood of 50 nodes | 50, 152 | 154 / 30 | 0.96 | 0.89 | 0.76 | – | 0 | – |
| neighbourhood of 46 nodes (1) | 46, 119 | 120 / 26 | 1.09 | 0.88 | 0.76 | – | 0 | – |
| neighbourhood of 46 nodes (2) | 46, 72 | 23 / 21 | 0.95 | 1.19 | 0.94 | – | 0 | – |
| neighbourhood of 34 nodes | 34, 93 | 74 / 23 | 0.92 | 0.96 | 0.68 | – | 0 | – |

Packed (`layoutPacked` against `dot` with `pack=true`; measured for code site C and its largest
module): code site C has 1.15 times `dot`'s crossings, 1.66 times its edge length and 0.41 times
its area (unpacked: 1.29, 3.36 and 1.63); its largest module is one component (its one cluster
holds every node), so packing changes nothing there.

Against the aim of 1.1 times `dot`'s crossings and edge length and 1.25 times its area with
correct clusters. The clusters are correct on every graph (boxes disjoint or nested, holding
exactly their nodes) and no edge passes a node. The area is within the aim on every graph but four:
the 3000-node module graph (1.29: PILean's layering of least total span gives fewer, wider layers
than `dot`'s), code site C (1.63) and the two graphs that are one very wide layer of leaves, the
node with 400 neighbours (1.73) and the largest module of code site C (2.24), whose drawings are
about 107,000 and 142,000 pixels wide. Crossings are within the aim on every graph without
clusters but the 800-node module graph (1.25), and on all the neighbourhoods (0.78 to 1.10); on the
graphs with clusters they are not: 1.50, 1.55 and 1.31 on the three blueprint graphs and 1.29 on
code site C (0.02 on its largest module, where `dot` draws 1,003 crossings against PILean's 16).
Edge length is within the aim on every graph without clusters but the sparse graph (1.12), the
tree (1.31), the chain (1.15) and one neighbourhood (1.19) (PILean's ends are spread along the
node's side and enter perpendicular to it; the curves are longer than `dot`'s diagonals), and not
on the graphs with clusters: 1.04, 1.64 and 1.54 on the blueprint graphs and 3.36 on code site C
(1.66 packed), where 85 clusters and 5,455 edges that enter a cluster holding neither of their ends
are what PILean handles worst (`compactGroups` shortens the clusters' spans at the cost of longer
edges, and long edges leave a cluster through its side and run outside it).

Crossings on the blueprint graphs with clusters are 1.29, 1.19 and 1.10 times `dot`'s: under the
cluster rules the reduction runs the sweeps and transposition from the same starts (the seeded
ones included) but does not sift. What would close the gaps: a layering that ranks clusters
recursively as `dot` does (its own cluster skeleton), which lets the crossing reduction move whole
clusters; sifting under the cluster rules; and a cheaper network simplex exchange (the low/lim
numbering of Gansner et al. for the cut search) so that the coordinate phase can finish within
the bound on larger graphs.

PILean is slower than `dot` on most of these graphs: the seeded starts and the sifting take most
of the time (the blueprint graphs without clusters 50 to 160 ms, the 800-node module graph about
1.5 s and the 3000-node one about 6 s, against `dot`'s 20 to 63 ms, 0.5 s and 3.5 s).
`LayeredOptions.starts` sets the number of extra starts; with none the layouts take a tenth to a
fifth of these times and have more crossings.

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

