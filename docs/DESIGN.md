# PILean design

PILean is a pure-Lean image library: what Pillow is to Python, with plots, a vector canvas and
graphs of nodes and edges on top, SVG and PNG output, and a traceability layer that ties every
image to the Lean that produced it. This note gives the module layout, the public API in
outline, what is exact and what is floating point, and the open choices.

## Principles

1. **Pure Lean, `Init` and `Std` only.** The drawing library (`import PILean`) imports nothing
   else; the module of the attribute `@[figure]` and the build-time checks, `PILean.Trust.Attr`,
   imports `Lean` and is imported only by code that uses them. No FFI, no Mathlib, no large
   dependencies. Text in images goes through an interface (`TextEngine`) with a built-in
   lettering; LeAnTeX implements it in a separate package of this repository (`leantex/`, "Text
   in images").
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
| `PILean.Path` | `PathCmd`, `Path`, shapes, circular arcs (`arc`, `arcTo`, `arcError`), `transform`, `flatten`, `bounds` | done |
| `PILean.Svg` | the SVG document model and writer | done |
| `PILean.Plot.Ticks`, `Scale`, `Sample`, `Figure`, `Check`, `Proofs` | nice ticks (multipliers proved ascending and inside their interval), linear and logarithmic scales with minor ticks, adaptive sampling of functions, the `Figure` model (panels, axes, series, legends, annotations) drawn on the canvas | done |
| `PILean.Raster` | anti-aliased scanline fill by area coverage in integers (non-zero and even-odd), clipping to rectangles and paths, the stroker (joins, caps, miter limit, dashes), gradients, compositing in linear light, group opacity, `Draw` (in the spirit of `ImageDraw`), Gaussian blur and drop shadows, SVG nodes drawn | done |
| `PILean.Image` | `Image` (mode, size, pixels in a `ByteArray`), `getpixel`, `putpixel`, crop, paste with a mask, alpha compositing, convert, flips and quarter turns, resize (nearest, bilinear, box, Lanczos) | done |
| `PILean.Png` | PNG writer and reader: CRC-32, Adler-32, DEFLATE (stored, fixed and dynamic Huffman; inflate with every bound checked), filters, `tEXt`/`iTXt`/`zTXt`, `sRGB`, `gAMA`, `pHYs` (written); the reader takes every colour type and depth and Adam7 (the writer does not interlace) | done |
| `PILean.Anim` | a `FrameSeq` (equally sized RGBA frames, a rational delay each, a loop count) and its codecs. APNG: writer (frame differencing to the changed rectangle, equal frames merged, delays as reduced fractions) and reader (composes `dispose_op` and `blend_op`, any PNG colour type, caps on size, frames and bytes). GIF89a: writer (LZW, one global palette by median cut or the exact colours, optional Floyd–Steinberg dithering, differencing with a transparent index, delays in centiseconds with exact cumulative time, loop extension) and reader (global and local tables, interlacing, disposal 0–3, transparency, caps) | done |
| `PILean.Canvas`, `PILean.Style` | the vector canvas (`Shape`: paths with fills and strokes, text, groups with transforms, opacity and clips, metadata through `Shape.tagged` and `ShapeInfo`; gradients), written as SVG or drawn as PNG from the same SVG nodes; the `Style` record of every visual constant, `Style.light` and `Style.dark`, with the plane colours and sizes `PlaneStyle` | done |
| `PILean.Plane` (`Basic`, `Frame`, `Draw`, `Check`, `Render`, `Graph`) | plane figures: elements in world coordinates (`Geom`: points, lines, arcs, regions of disks, ticks, labels, …), looks by role (`Look`, `Tone`, named roles), items with metadata (`Item`), builders and modifiers; the frame (`Frame`, one scale, `y` up) fitted to the items' reaches (`Frame.fit`), clipping (`clipLine`); the figure (`Figure`) drawn on the canvas; layout checks and automatic label placement; outputs (sRGB images, outlined text, narrow renditions); graphs inside plane figures, step animations | done |
| `PILean.CheckLevel` | how strictly a figure's checks apply (`ignore`, `warn`, `fail`), shared by plots and plane figures | done |
| `PILean.Explorer` | families of frames (a parameter axis, a step sequence, or both) for web pages, their poster files and animations | done |
| `PILean.Exact.Plane`, `PILean.Exact.Algebraic`, `PILean.Exact.Spec` | exact points: rational balls (`RatBall`, `sqrtBall`), the classes `RealValue` and `PlanePoint` with their laws, instances for `Rat`, `Int` and their pairs, builders from exact points, theorems on where they are drawn; exact incidence with a disk; ℚ(√d), ℤ[ζ₅], exact square roots, constructions with certified enclosures; what an item of a figure is in exact terms (`IsPoint`, `IsDisk`, `IsSegment`, `IsRegion`), for specifications | done |
| `PILean.Diagram` (`Basic`, `Graph`, `Hasse`, `Young`, `Perm`, `Tree`, `SetSystem`, `Path`) | diagrams of finite combinatorial objects and orders drawn from their data: exact marks tagged with the part they depict, read back by `Faithful` predicates with theorems for every kind, drawn as plane figures | done; faithfulness proved for every kind, see [`PROOFS.md`](PROOFS.md) |
| `PILean.Graph.Fixed` | graphs at given positions (page, world or exact), edges straight or bent around nodes | done |
| `PILean.Text` | `TextEngine` (measure, ascent, descent, shapes, identity, whether its strings are plain text) and the built-in single-stroke lettering that draws text into images; LeAnTeX implements it in the package `pilean-leantex` (`leantex/`) | done |
| `PILean.Anim.Animation` | an animation as a drawing over time, written as animated SVG (SMIL), APNG and GIF, with a poster frame | done |
| `PILean.Graph` | `Graph` (nodes, edges, clusters), the layered (Sugiyama) layout with spline, orthogonal or bundled edges (one entry and one exit port per node, tracks in channels, concentric corners), arrowheads, edge labels and clusters, circular and tree layouts, components laid out apart and packed, mirrored layouts, drawing on the canvas as SVG and PNG, and as SVG for a web page | done; layering proved, see below |
| `PILean.Trust` | done: a figure's standing (`proved` or `illustration`, recorded in its files and the manifest, `--require-standing`); SHA-256 (`Sha256`, padding and digest size proved, FIPS and NIST vectors tested); source information (module, declaration, file, line, repository, commit, version, fingerprint) written into SVG, PNG, APNG and GIF and read back by a bounded reader, `lake exe pilean-info`, see [`TRUST.md`](TRUST.md). `@[figure]` and `figures%` (declaration, file, line, source hash), fingerprints of figure specifications (SHA-256), `lake exe pilean-build` (deterministic build with `manifest.json`, `--check`) and `lake exe pilean-verify`; `figure_proves` links a figure to a theorem about it ([`PROOFS.md`](PROOFS.md)) | done |

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
(`Graph.layout`, files `Graph/Layering`, `Nested`, `Simplex`, `Ordering`, `Compound`, `Coordinates`,
`Route`, `Layered`; with the components laid out apart and packed, `Graph.layoutPacked`,
`Graph/Pack`), or on a circle (`circularLayout`) or as a tree (`treeLayout`), and draws the
`Layout` on the vector canvas (`Graph/Draw`), so that the SVG and the PNG show the same picture.
Nothing in it depends on Mathlib or on any other library; it follows the published algorithms,
listed in the module docstrings.

**Phases and their bounds** (`V` nodes, `E` edges, `L` layers, `D` dummy nodes, the sum of the
spans of the edges, at most `E (L - 1)`; `C` clusters):

1. *Cycle removal*: the greedy feedback arc set heuristic of Eades, Lin and Smyth; edges against
   the resulting order are reversed for the layout and drawn in their own direction. At most
   `3V + 2` steps, `O(V + E)` plus a scan of the nodes each time no source or sink is left.
   Self-loops are set aside and drawn as small loops.
2. *Layers*: network simplex (Gansner, Koutsofios, North and Vo, 1993; `Graph/Simplex`) from the
   longest-path layering, towards the layers of least total edge span (the objective; it is
   reached when the search finishes within `layerWork`); two balancing passes; then
   `fixLayers`, which relaxes the edges sorted by the order of their source and so makes every
   edge point down whatever came before (proved). `O(E log V)` for the start, `O(V + E)` per
   exchange at worst. When an edge has a label the layers are doubled so that the label has a
   layer half-way along its edge. With `maxLayerWidth`, the nodes of a layer wider than that are
   split over rows put in between (`wrapLayers`: a row is filled until the next node would pass
   the limit, the nodes with more edges from above first); edges keep pointing down, the drawing
   gets narrower and taller, and the edges to the lower rows pass between the nodes of the upper
   ones.
   *With clusters* (`Graph/Nested`, the default; Gansner et al. rank clusters recursively, and
   Sander's compound graphs are layered the same way): the graph is layered from the inside out.
   At one level (the whole graph, or the inside of one cluster) the items are the nodes standing
   there directly and the clusters directly inside, each already layered and so many layers high;
   an edge between two items makes its target item begin below the whole of its source item
   (network simplex with the heights as the least lengths of the edges, cycles between items
   removed first). So every cluster keeps a block of layers to itself, two clusters that an edge
   joins lie one wholly above the other, and an edge between them leaves the one through its
   lower side and enters the other through its upper side.
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
   crossings, the same result on every run), not proved. The starts are searched at the same
   time (tasks), and the first of the best results is kept, as if they had been searched one
   after the other: the result does not depend on the number of processors.
4. *Clusters* (`Graph/Compound`, after Sander's layout of compound graphs): a dummy node belongs
   to the innermost cluster around one of its edge's ends whose layers reach the dummy node's
   layer, else to the innermost cluster holding both ends; every cluster gets a left and a right
   border node in each layer of its span, joined from layer to layer by edges that count in the
   crossing count eight times (an edge crossing a cluster's side passes through the cluster); in
   every layer a cluster's nodes stand together between its borders, nested clusters inside
   their parent's block, sibling blocks in one order in every layer. In a sweep a free node keeps
   the side of every nested cluster that its middle neighbour in the layer before has there
   (`arrangeBlock`), and a cluster that begins in a layer is seated between the siblings that its
   edges from the layer before come between (`seatClusters`); the sweeps and transposition run
   under these rules from the same starts as phase 3 (without sifting). Where an edge would still
   pass through a cluster that holds neither of its ends (`strays`), the first three phases are
   run again with that cluster and the item the edge leads to kept one above the other, up to
   `clusterRounds` (12) times, and the attempt with the fewest such edges is kept: the edge then
   passes the cluster's lower or upper side instead. `O(C L)` border nodes.
5. *Coordinates*: Brandes and Köpf's four alignments with type 1 conflict marking, balanced; then
   `refine` (8) passes towards the median of the neighbours; then network simplex on the weighted
   horizontal length of the edges (Gansner et al., section 4.2: weight 1 for two real nodes, 2 for
   one dummy, 8 for two, and an edge of the least separation between neighbours in a layer),
   started from that result. All left borders of a cluster share one variable and all its right
   borders another, with an edge between them as long as the title and of weight 1: the sides of
   a cluster are straight, and so its box holds exactly its nodes. The leaving edge is found by
   partial pricing (the most negative of the next 32 candidates); the search has a bound on the
   work (`coordinateWork`, 90 million) and returns the best assignment so far when it is used up
   (a 3000-node graph finishes about 1800 exchanges). With `compact`, the width of every layer
   counts in the total too (an edge of that weight from the first to the last node of each
   layer): the drawing gets narrower and its edges more slanted.
6. *Edges* (`Graph/Route`, after section 5 of Gansner et al.): the room of an edge is a sequence
   of *gates*: at the lower edge of the layer it leaves, at the upper and lower edge of every
   layer it crosses and at the upper edge of the layer it enters, the stretch across the layer
   between its neighbours there (half of the free space towards a neighbouring dummy node, so
   that the edges of a bundle stay apart; up to a few pixels from a neighbouring box or cluster
   side); between two layers the room is free. The route is the shortest polyline through the
   gates (`tautRoute`, the funnel of Lee and Preparata; an edge with nothing in its way is one
   straight line), and the curve is the quadratic B-spline of that polyline (`roundedPieces`):
   a parabola around every bend from the middle of the part before it to the middle of the part
   after, so that the curve turns no more than the polyline and never the other way. Where a
   parabola would leave the room of its edge (the boxes and cluster sides beside it in a layer,
   the sides of the clusters that reach on between two layers) it is drawn closer to its bend,
   by halves, down to the corner itself (`fitPieces`). An edge never turns back across the
   layers. A gap grows, up to `sidewaysGap` (2.5) times, until its widest step is no flatter
   than `flattest` (12) to one; orthogonal routes (`Routing.orthogonal`) are horizontal and
   vertical segments with rounded corners on tracks of their own: in each gap between two
   layers, the horizontal runs going one way are taken in order and each gets the track after the
   highest one among the runs placed before it in that gap that it overlaps (within 6 pixels), so
   `k` runs in one gap and direction cost
   `k (k − 1) / 2` comparisons, a term that neither `layerWork` nor `coordinateWork` bounds
   (`lake test` lays out 5000 runs in one gap under its CPU bound). Ends are spread along the
   node's side in the order of the other ends; an arrowhead lies along the end of its curve, with
   Graphviz's proportion to the node; labels on plates of the page colour at the middle of the
   edge. Bundled routes (`Routing.bundled`) are the next section.

**Bundled routes** (`Routing.bundled`, `Graph/Channel`, `Graph/Bundle`; the look is
`LayeredOptions.bundle`, a `BundleStyle`; the spline routes stay the default). Edges drawn as
horizontal and vertical segments in bundles of parallel lanes, as cables are laid in a tray:

* *Ports.* Every node has one exit port, the middle of its lower side, and one entry port, the
  middle of its upper side (in the layers' frame; left to right and the mirrored directions
  follow). The edges that leave a node share one vertical stem from the exit port and leave it,
  each on its own track; the edges that enter a node join one stem, which ends in one arrowhead.
  An edge against the layers (cycle removal) and a self-loop keep to the ports: they leave
  downwards, turn up a *corridor* beside the source (room the layout keeps on the node's right,
  `laneGap` for each), run up the lanes of their dummy nodes, pass up a corridor beside the
  target and come down into its entry port.
* *Channels and tracks* (`placeRuns`, the channel routing of circuit layout with two-terminal
  nets). The band between two layers is a channel (one more above the first layer and below the
  last, used by the corridors). An edge that changes its position across the layers there does so
  on a horizontal run with a track of its own height. The *vertical constraints* of Hashimoto and
  Stevens: where an end whose vertical piece comes from above and one whose piece goes on below
  stand at one column (closer than `laneGap`), the first run lies above the second; they are kept
  through one hub per pair of such columns, linear in the runs. The *nesting* of the runs that turn
  the same way: of two overlapping runs going right (from `a` above to `b > a` below) the one with
  the larger `a`, then the larger `b`, lies above, and mirrored for runs going left; then they do
  not cross, where the other order crosses them twice, and two runs whose order changes across
  the channel cross once either way. *Doglegs* (Deutsch): when the constraints form a cycle (two
  runs that swap two columns), the first run in the nesting order that nothing above it waits for
  is split at a free column (at least `max laneGap trackGap` from every vertical piece of the
  channel, the nearest such to the middle of its run) into two parts on two tracks joined by a
  vertical jog; an edge that repeats a straight one is split so at once. The order: Kahn's
  algorithm, the next run being a ready one of the lowest rank in its direction's nesting order,
  the two directions in step. The tracks (`tracksInOrder`, the left-edge rule): each run in that
  order gets the track below the lowest earlier run it is in conflict with: the runs overlap (or
  come within `trackGap`) and do not *fork* from one stem (a run leaving a stem to the left and one
  leaving it to the right share a track, so the stem forks there), or one must lie above the
  other at a column.
* *Room.* The layout reserves the room the routes need: the dummy nodes of a bundled layout stand
  `laneGap` apart (in place of `edgeGap`), so the lanes of long edges beside each other are evenly
  spaced; a channel is `stemLength + radius` (at least `laneGap`) above its first track,
  `laneGap` per track, and as much and an arrowhead below its last; nothing is squeezed. Before the routes, a
  pass moves a run of a chain's dummy nodes onto the line of its neighbour in the chain when that
  closes a jog narrower than a lane without opening another and every layer of the run has room
  (`straightenLanes`, at most three passes linear in the dummy nodes).
* *Corners.* Corners of one turn whose centres can coincide (lanes `laneGap` apart turning onto
  tracks `laneGap` apart lie on one diagonal) form a bundle and are concentric quarter circles: the
  innermost of radius `radius`, the lane `k` places further out `radius + k × laneGap`. The rule
  that fits them: of a segment between two corners each takes at most its share in proportion to
  the radii they want, of a segment at a port at most its length less the stem (and the
  arrowhead); a bundle that does not fit keeps its corners concentric with a smaller innermost
  radius when one of at least zero is enough, and is scaled as a whole otherwise.

Work: the legs of the routes are the sum of the spans of the edges; a channel of `k` runs costs
`O(k²)` (the nesting order and the tracks compare runs pairwise; at most `k` doglegs, each `O(k)`
to find its column), up to `BundleStyle.maxRuns` (4000) runs; a channel with more gives each run
a track of its own in `O(k log k)`, without the constraints between them: the promises tested
below (no shared segment, lanes apart) do not hold for such a channel. `lake test` lays out
5000 bundled routes leaving one node, 20000 parallel edges and 10000 nodes with ten self-loops each
under CPU and memory bounds.

*Proved* (`Graph/Channel`, `Graph/Bundle`): two runs in conflict never share a track
(`tracksInOrder_ne`, for any symmetric conflict, and the conflict of `placeRuns` is symmetric:
`RunPart.conflicts_comm`; that this conflict covers every pair that must not share a track is
tested); every route, before its corners are rounded and its ends cut for stems and arrowheads,
is a walk of horizontal and vertical moves that starts at
its source's exit port and ends at its target's entry port (`routeWalk_head`, `routeWalk_last`,
`routeWalk_axis`). *Tested* (`PILeanTest/GraphBundles.lean`, on every measured graph and graph
file but the two largest, on hostile graphs: multi-edges, self-loops, cycles, a node with 200
edges in or out, a chain with shortcuts, complete bipartite graphs, nested clusters, labels, an
undirected graph; from the top down, left to right, both mirrored and packed; each checker with a
planted fault): every route leaves at the exit port and enters at the entry port of the finished
picture, its segments and the straight pieces of its path are horizontal or vertical, no two edges
share a piece of a segment except the trunk of a port both use, no route passes within two pixels
of a node it does not end at, parallel segments of two edges are at least `laneGap` apart, one
arrowhead per entry port and none on an edge; crossings at most a fiftieth above the spline
routes'; no more edges through a foreign cluster than the spline routes; in random channels two
runs cross at most once, and not when their ends agree. The style space is tested at its
defaults on the corpus and, by an independent check, from lanes 3 to 12 apart, radii 0 to 20,
stems 0 to 30 and track gaps 4 to 24 on hostile and 500 random graphs. Two edges can still cross more than once
in all when the layers' order swaps them in one channel and back in another (the measures count
such pairs: up to 7 of 146 edges on blueprint A by chapter).

*Measured* (`lake exe pilean-test --bundle-measures`, the default `BundleStyle`: lanes 6 pixels
apart, innermost radius 6, stems 10, runs on one track 12 apart; the routes measured as
polylines from port to port, the spline routes as flattened curves; `dot`'s numbers are the
recorded ones of `PILeanTest/graphs/dot-recorded.tsv`, its area without cluster boxes, PILean's
with them). The bundled routes follow the spline routes' orders, so their crossings are within a
few of the spline routes' (and fewer than `dot`'s on the graphs with clusters); they are about 1.3
to 1.7 times as long (a rectilinear route against a straight or curved one), and the drawings take
up to about a tenth more area, as the channels grow with their tracks, except where one node has
hundreds of edges: every edge has its own lane, so a node with 400 neighbours in the layer below
needs 200 tracks on each side of its stem (seven times the spline drawing's area).

| Graph | Crossings (spline / bundled / `dot`) | Edge length (spline / bundled / `dot`) | Area, Mpx² (spline / bundled; `dot` without clusters) | Bends per edge | Jogs narrower than a lane | Pairs crossing twice |
|---|---|---|---|---|---|---|
| blueprint-a | 254 / 254 / 252 | 59712 / 86109 / 71977 | 2.93 / 3.28; 3.29 | 2.99 | 3 | 0 |
| blueprint-a-chapters | 264 / 261 / 310 | 76561 / 111013 / 84947 | 4.31 / 4.72; 3.77 | 3.62 | 5 | 7 |
| blueprint-67 | 296 / 296 / 279 | 99094 / 130602 / 108473 | 5.08 / 5.14; 5.39 | 3.2 | 3 | 0 |
| blueprint-67-chapters | 437 / 434 / 529 | 135787 / 178390 / 127946 | 7.97 / 8.09; 4.96 | 3.86 | 1 | 0 |
| blueprint-b | 85 / 85 / 80 | 35348 / 47438 / 31074 | 2.9 / 2.76; 2.76 | 2.18 | 4 | 0 |
| own-imports | 221 / 221 / 213 | 96236 / 125008 / 108109 | 4.38 / 4.47; 5.48 | 3.07 | 8 | 0 |
| project-imports | 105 / 105 / 140 | 39959 / 57614 / 46426 | 2.77 / 2.94; 3.49 | 2.44 | 1 | 0 |
| code-site-c-modules | 185 / 184 / 163 | 66847 / 91944 / 66155 | 6.74 / 6.99; 6.96 | 2.82 | 0 | 0 |
| module-800 | 7594 / 7603 / 6190 | 966400 / 1317517 / 988805 | 40.73 / 46.91; 41.92 | 2.72 | 26 | 0 |
| dense-dag | 751 / 753 / 713 | 74916 / 126237 / 109216 | 2.4 / 2.63; 7.18 | 3.16 | 6 | 2 |
| sparse-dag | 249 / 249 / 270 | 54793 / 81071 / 50956 | 5.26 / 5.84; 8.93 | 1.66 | 1 | 0 |
| neighbourhood-34 | 146 / 146 / 159 | 40869 / 56799 / 44034 | 1.78 / 1.96; 2.26 | 3.03 | 2 | 0 |
| neighbourhood-150 | 2892 / 2889 / 3776 | 748520 / 1021786 / 1064583 | 26.89 / 27.83; 27.08 | 3.99 | 11 | 1 |
| neighbourhood-290 | 6198 / 6192 / 7229 | 1197885 / 1702771 / 1534595 | 32.68 / 67.03; 26.80 | 3.39 | 3 | 6 |
| tree | 0 / 0 / 0 | 11418 / 15333 / 9468 | 2.55 / 2.12; 2.12 | 1 | 0 | 0 |
| neighbourhood-star-401 | 0 / 0 / 0 | 10670338 / 11194781 / 10594068 | 19.9 / 140.17; 12.84 | 2 | 0 | 0 |
| code-site-c-largest-module | 16 / 16 / 1003 | 10766097 / 11317539 / 10901646 | 33.21 / 191.93; 13.22 | 1.97 | 0 | 0 |


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
and of the node part of the second, and the blueprint graphs with clusters to no edge entering a
cluster that holds neither of its ends; on the largest graph such edges are counted.

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
earlier steps returned), `assignNested_lt` and `assignWide_lt` (the same for the layers of a graph
with clusters, layered from the inside out, and for the layers with their wide ones split into
rows), `compactGroups_size`, and `layout_edge_indices`, `layout_edges_nodup`,
`layout_edges_complete` (the routed edges are exactly the valid input edges, in order, each once,
by index). The cluster and clearance conditions and the properties of the routes (inside their
gates, shortest, the curve inside its zones, never back across the layers) are checked on every
measured graph and on random cases, each check with a planted fault that it must report
(`PILeanTest/GraphRoutes.lean`), not proved.

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
violations of the two checks; time; and what the eye objects to: the mean turning of an edge (the
sum of the angles by which it changes direction, in degrees), its mean number of inflections
(changes from bending one way to bending the other, a bend counting from five degrees), the
length of the edges outside the box around the nodes, the least distance between an edge and a
node it does not end at, and the edges that turn back across the layers). With `DIR`, the same
graphs are written as DOT with PILean's node sizes and gaps and their clusters, and
`python3 -I tools/graph-compare.py DIR` compares with Graphviz's `dot` when it is installed. The
built-in graphs: this library's import graph and that of a project of 89 modules (names replaced
by ids), the dependency graphs of two blueprints (names removed, label lengths kept) without
clusters, by chapter and, for the first, by chapter and section, random module graphs of 800 and
3000 nodes, random dense and sparse acyclic graphs, a binary tree and a chain with shortcuts
(`PILeanTest/GraphQuality.lean`). The graph files (`PILeanTest/graphs/`, described in its
`README.md`; names removed, label lengths kept) are a code site of about 2,900 declarations in 85
modules (code site C), its modules and its largest module, and views of the neighbourhood of one
declaration of 34 to 401 nodes. Graphviz's numbers are the recorded ones in
`PILeanTest/graphs/dot-recorded.tsv` (Graphviz 16.1.0), so that `lake test` needs no `dot`: it
holds every graph but the two largest (the 3000-node module graph and code site C) to no cluster
violation, no edge passing a node or nearer than three pixels to one, no edge turning back across
the layers, crossings, edge length, turning and inflections within a ratio of the recorded ones (a
constant per graph, about 0.1 above the measured ratio), and, for the older graphs, to bounds
about a tenth above the values measured.

Measured with the machine's load average about 3 to 12 (PILean's runs under the higher load).
Ratios are PILean over `dot`; where two numbers stand in a cell they are PILean's and `dot`'s.
The area in the table is computed by `tools/graph-compare.py` for both programs in the same way,
as the box around the nodes and the edges' points: neither includes cluster boxes (`dot`'s plain
output has none, and the comparator reads only the nodes and edges of PILean's file). The area
that `lake test` holds PILean's drawings to (`PILeanTest/GraphQuality.lean`) includes them.
Times are one run each: PILean's layout alone (the starts of the crossing reduction on several
processors), and `dot` on the file (including its start).

| Graph | Nodes, edges | Time (ms) | Crossings | Edge length | Area | Turning of an edge (degrees) | Inflections of an edge | Nearest node to an edge (px) | Edges entering a foreign cluster |
|---|---|---|---|---|---|---|---|---|---|
| own imports | 92, 205 | 68 / 37 | 1.04 | 0.89 | 0.80 | 46 / 44.8 | 0.26 / 0.29 | 5 / 0.6 | – |
| project imports | 88, 173 | 40 / 30 | 0.75 | 0.86 | 0.79 | 23.5 / 25 | 0.12 / 0.2 | 4.1 / 0.9 | – |
| blueprint A | 58, 146 | 45 / 27 | 1.01 | 0.83 | 0.89 | 48.4 / 43.6 | 0.25 / 0.29 | 4.9 / 0.3 | – |
| blueprint A by chapter | 58, 146 | 196 / 63 | 0.85 | 0.90 | 1.11 | 75 / 52 | 0.59 / 0.53 | 5 / 0.2 | 0 |
| blueprint A by chapter and section | 58, 146 | 258 / 61 | 0.98 | 0.90 | 1.13 | 99.5 / 66.1 | 0.77 / 0.69 | 5 / 0.1 | 0 |
| blueprint B | 69, 111 | 18 / 20 | 1.06 | 1.14 | 1.05 | 15 / 18 | 0.07 / 0.03 | 5.7 / 1.2 | – |
| blueprint B by chapter | 69, 111 | 81 / 60 | 0.60 | 0.88 | 0.96 | 42.1 / 39.4 | 0.35 / 0.38 | 4.5 / 0.1 | 0 |
| module graph | 800, 1077 | 794 / 434 | 1.23 | 0.98 | 0.97 | 34.2 / 39.4 | 0.5 / 0.6 | 4.2 / 0.1 | – |
| module graph | 3000, 4019 | 6466 / 3193 | 0.85 | 0.80 | 1.48 | 67.3 / 59.2 | 0.99 / 1.05 | 3.5 / 0 | – |
| dense random | 120, 387 | 93 / 52 | 1.05 | 0.69 | 0.33 | 32.1 / 29.4 | 0.21 / 0.12 | 5 / 1.7 | – |
| sparse random | 300, 325 | 55 / 32 | 0.92 | 1.08 | 0.59 | 6 / 9.1 | 0.05 / 0.1 | 5.8 / 0.8 | – |
| tree | 127, 126 | 8 / 19 | – (0 / 0) | 1.21 | 1.20 | 0 / 0.1 | 0 / 0 | 27.2 / 24.6 | – |
| chain | 80, 99 | 8 / 19 | – (0 / 0) | 1.09 | 1.14 | 0 / 1.4 | 0 / 0 | 22 / 14 | – |
| code site C | 2866, 5516 | 25181 / 1590 | 0.48 | 1.04 | 5.53 | 111.5 / 108.7 | 1.06 / 1.37 | 3.5 / 0 | 13 |
| code site C, its modules | 85, 159 | 114 / 33 | 1.13 | 1.01 | 0.97 | 44.8 / 40.1 | 0.36 / 0.31 | 5.7 / 0.9 | – |
| code site C, its largest module | 561, 422 | 160 / 75 | 0.02 | 0.99 | 1.99 | 6 / 34.8 | 0 / 0.1 | 5.9 / 0 | 0 |
| neighbourhood, a node with 400 neighbours | 401, 400 | 26 / 32 | – (0 / 0) | 1.01 | 1.55 | 2.1 / 32.4 | 0 / 0.07 | 5.9 / 0.1 | – |
| neighbourhood of 290 nodes | 290, 793 | 1115 / 155 | 0.86 | 0.78 | 1.22 | 69 / 61.7 | 0.63 / 0.66 | 4.6 / 0 | – |
| neighbourhood of 150 nodes | 150, 468 | 651 / 145 | 0.77 | 0.70 | 0.99 | 87.4 / 83.5 | 0.75 / 0.98 | 4.5 / 0 | – |
| neighbourhood of 50 nodes | 50, 152 | 106 / 27 | 0.95 | 0.85 | 0.88 | 61.7 / 57 | 0.36 / 0.49 | 5.4 / 1.1 | – |
| neighbourhood of 46 nodes (1) | 46, 119 | 84 / 24 | 1.09 | 0.88 | 1.02 | 50.1 / 49.7 | 0.26 / 0.42 | 5.3 / 0.8 | – |
| neighbourhood of 46 nodes (2) | 46, 72 | 22 / 18 | 0.95 | 1.10 | 1.03 | 14.6 / 14 | 0.08 / 0.1 | 6 / 1.8 | – |
| neighbourhood of 34 nodes | 34, 93 | 52 / 23 | 0.92 | 0.93 | 0.79 | 52.5 / 43.4 | 0.29 / 0.26 | 4.6 / 1.3 | – |

No drawing has a cluster violation, an edge passing a node, or an edge that turns back across the
layers. Packed (`layoutPacked` against `dot` with `pack=true`): code site C has 0.38 times `dot`'s
crossings, 0.81 times its edge length and 1.56 times its area; its largest module is one
component (its one cluster holds every node), so packing changes nothing there.

What the table says. Without clusters the drawings have about as many crossings as `dot`'s (0.75
to 1.23 times), shorter edges on most graphs (0.69 to 1.14 times; the tree 1.21, because the ends
are spread along the node's side) and a smaller or similar area. An edge turns about as much as in
`dot`'s drawing (within a sixth on most graphs: 48 degrees against 44 on blueprint A, 15 against
18 on blueprint B) and changes the side it bends to less often on most. No edge comes nearer than
3.5 pixels to a node it does not end at, where `dot`'s edges touch or cross such nodes on most
graphs. With clusters, layered from the inside out, the blueprint graphs have fewer crossings and
shorter edges than `dot`'s (0.60 to 0.98 and 0.88 to 0.90 times) and no edge through a cluster it
does not end in, at the cost of more turning (75 and 100 degrees an edge against 52 and 66: an
edge goes round a cluster where `dot`'s goes through it) and of drawings that are about as tall
as wide where `dot`'s are wide strips. Code site C has half of `dot`'s crossings and edges 1.04
times as long; 13 times an edge still passes through a cluster that holds neither of its ends
after the twelve rounds (in `dot`'s drawing 896 of the 5,516 edges do, through 3,104 clusters in
all), and its drawing is five and a half times the area of `dot`'s, about 251,000 by 28,000
pixels against 325,000 by 4,000: most of its width is the room of the edges between the clusters.

PILean takes one to two times as long as `dot` on most graphs without clusters (45 ms against 27
on blueprint A, 0.8 s against 0.4 s on the 800-node module graph) and up to seven times on the
dense neighbourhoods (1.1 s against 0.16 s for 290 nodes), with the starts of the crossing
reduction on several processors; `LayeredOptions.starts` sets the number of extra starts. A
graph with clusters takes longer: the cluster rules make a sweep slower, and code site C takes
about 25 s for its twelve rounds (`clusterRounds`; one round is about 2 s, and `dot` takes 1.6 s
for a drawing with the edges through the clusters).

What would close the remaining gaps: an order of the sibling clusters found for the whole level at
once, so that fewer rounds are needed; sifting under the cluster rules; bundling the edges between
the same two clusters, which is what would make the drawing of a graph like code site C narrow;
and a cheaper network simplex exchange (the low/lim numbering of Gansner et al. for the cut
search) so that the coordinate phase can finish within the bound on larger graphs.

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
* **Labelling checks** (`PILean.Plot.Check`). A panel whose axes have no label, or with several
  series that neither the legend nor direct labels name, is reported in the scheme of the plane
  checks (`Figure.checks`: `ignore`, `warn`, `fail`); a panel bare on purpose says so
  (`Panel.bare`). Every plot of the gallery and of the manual is labelled.
* **Style.** `Style` holds every visual constant; `Style.light` and `Style.dark`. The palette is
  Okabe and Ito's, ordered so that adjacent colours stay apart under colour-vision deficiencies;
  both palettes pass a palette validator's checks of lightness band, chroma, CVD and
  normal-vision separation of neighbours, on their surfaces. Text never takes a series colour.

The 2000 × 1200 function plot (`lake exe pilean-test --bench`, one core of an Apple M2 Ultra,
load average about 14): layout 3 ms, drawing 320 ms, conversion to an 8-bit image 98 ms, PNG
encoding 732 ms (159,548 bytes). PNG encoding dominates (LZ77 and Huffman at level 6), then the
rasteriser's full-image background and curve strokes.

## Plane figures

A `Plane.Figure` is a list of items, a page width (and optionally a height), a padding, a `Style`
and metadata. Items are in world coordinates (`y` up, angles counterclockwise in radians); the
frame maps them to the page with one scale for both axes, so circles stay round and angles true.

* **Fitting.** Every item has *reaches*: world points with the pixel extent of what is drawn at
  them (a marker's radius, half a stroke, an arrowhead, an angle mark's radius, a label's box).
  `Frame.fit` takes the largest scale at which every reach fits inside the padding across the
  page (bisection over the scale: when no label is wider than the page, the scales that fit form
  an interval from 0; extents wider than the page are first shrunk until they fit, so a label
  too wide for the page does not collapse the scale), centres the drawing, and makes the page as
  tall as the reaches need, in whole pixels. With `view`, a given world box is fitted instead. Lines
  and rays reach the two
  points that define them and are drawn to the edge of the page (Liang and Barsky's clipping).
* **Pixel sizes.** Stroke widths, marker radii, arrowheads, label sizes and offsets and angle
  marks are in pixels at every scale; only world lengths (radii of circles, disks, arcs) scale.
* **Labels** are attached to a point with a placement (centred, one of eight sides, or a
  direction) and an offset: the label's box stands `offset` pixels from the point, measured with
  the style's text engine, so a label follows its point and LaTeX labels (`pilean-leantex`) are
  placed by their own measure.
* **Colours** are roles of `Style.plane`: the ink, three accents (Okabe and Ito's blue,
  vermilion and bluish green, adjusted per background), a faint construction colour and the
  opacity of tinted fills. The light and the dark values meet WCAG contrast on their backgrounds
  (ink 7:1, accents and faint 4.5:1; on a tinted fill, ink 7:1, accents 4.5:1, faint 3:1, mixed
  both in linear light and in sRGB), checked by the tests. A figure in `Style.dark` is the dark
  twin; Verso sites show the twin that matches the page (`pilean-verso-manual`'s `SiteOutputs`).
* **Metadata.** Every item (and the figure) can carry a title, a description, classes, an id and
  a Lean declaration (`Item.named`, `describedBy`, `withClass`, `withId`, `declRef`), written as
  SVG `title` and `desc` children and `class`, `id` and `data-lean-decl` attributes of a `g`
  (`Canvas.Shape.tagged`); images leave them out. Ids and classes are reduced to ASCII letters,
  digits, `_`, `-` and `.`.
* **Exact points** (`PILean.Exact.Plane`). A type with an instance of `Exact.PlanePoint` gives
  rational balls around the two coordinates of its values at any precision (`Exact.RealValue`
  for real numbers, such as radii); the figure converts the centres at 64 bits to `Float` at the
  last step. The core has no real numbers, so that a ball holds the value is declared by the
  instance; the laws that can be stated without them (radii between 0 and `2⁻ᵏ`) are the classes
  `LawfulRealValue` and `LawfulPlanePoint`. A representation that needs a context (a cyclotomic
  ring with its tables) gives the instance on a type that carries it. The tests have worked
  instances for Gaussian rationals, ℚ(√5) and ℤ[ζ₅] (integer coefficient arrays, compared by
  their normal form), whose balls are checked exactly by squaring rationals.
* **No made-up enclosures.** Ball arithmetic is exact rational arithmetic, so sums and products
  of enclosures are enclosures; an operation that is not defined on every number of its input's
  ball says so in its result: `RatBall.inv` and `RatBall.div` are `none` on a ball that holds 0
  (a fallback ball there is the alternative rejected: it is not an enclosure, and a construction
  built on it can report a point outside a disk it lies in). The constructions (`foot`,
  `circleCircle`, `lineCircle`) decide,
  from balls at 64 to 512 bits, that a divisor is at least some `m > 0` (`positiveBound?`) and at
  every working precision divide by the part of the divisor's ball above `m`
  (`RatBall.invAbove`), so a low precision gives a wide ball, never a wrong one; they decide the
  sign under a square root the same way, and answer what the balls do not decide with `none` or
  `Meeting.undecided` (tangency is decided only for data whose balls have radius 0, rationals and
  integers, where the deciding number is exactly 0). The square root is `√(max x 0)`, total.
  Refinement says when it did not reach the radius asked (`refine`, `Enclosed.meetsPrecision`).
  A radius is taken as given, not through its square: a radius not decided to be positive is
  `Meeting.degenerate` (and `diskIncidence?` is `none`), so `-r` is never read as `r`; reading
  it as `|r|` was the alternative rejected, since a negative radius is a mistake in the data, not
  a circle. The order and equality of `QSqrt d` require `[QSqrt.NonSquare d]`: for a square `d`
  the pair `(a, b)` does not determine `a + b √d`, so comparing pairs would be wrong; computing
  the rational value for a square `d` was the alternative rejected, since a square `d` is
  ℚ written twice and only hides a mistake in the radicand.
* **Specifications that write out the items.** A figure's theorem states its item list
  literally (each item as the builders and modifiers that make it: data, colour, title, marker,
  recorded incidences, labels with their text, point and placement), so that the exact facts
  about the data (that `E` is on the left circle) are facts about the items that draw them, and
  a change to the item list (an item, a label, a role or a recorded incidence) breaks the build;
  the style's colour values, the width, the frame, the layout and the pixels are not pinned.
  `lake test` makes such changes to copies of the modules and requires each to fail in the
  specification (`PILeanTest/SpecMutations.lean`).
  Naming the items in the theorem with predicates such as `Plane.Exact.IsPoint` was the
  alternative rejected: the list itself was left to a definition `rfl` restated, so an item could
  be removed or a label moved without breaking any proof. The strict figure link (`figure_proves`:
  the figure's constant occurs in the theorem) holds for each.
* **Regions, fills, markers, ticks.** The intersection, union and difference of two disks are
  regions bounded by exact circular arcs of their circles (`regionArcs`, `Path.arcTo`); a shape's
  tint (colour, opacity) and outline are styled apart; markers are dots, rings, squares, diamonds
  or crosses on a halo; a tick crosses a line with a length in pixels, resolved at fitting.
* **One colour space for tints.** The image of a plane figure is composited in sRGB, as browsers
  composite an SVG's `fill-opacity`, so a tint (and a tint over a tint) has the same colour in
  the PNG and in the SVG shown by a browser. Plots and graphs keep the rasteriser's linear light.
  Animations and explorers made from plane figures (`Plane.animation`, `Plane.slider`,
  `Plane.stepper`) keep the figure's sRGB and its text as shapes (`Animation.srgb`,
  `Animation.textAsShapes`). The rule is tested by sampling the PNG inside a tint against
  the expected sRGB composite in both themes. Pre-blended opaque fills were the alternative; they
  would need the overlap regions of every pair of translucent shapes computed, and give the same
  colours.
* **Checks** (`PILean.Plane.Check`): overlapping labels, labels over lines or markers they do not
  name (a label is attached only to the marker at its point, so a label centred on a line is
  reported), things beyond the page, markers that read as one, points too near an element to be
  seen on it or off it unless they record their incidence relative to that element, colours of
  too little contrast against what they are drawn on (at their alpha; at a label's centre, a
  marker's, and along every stroke, over the page and the fills beneath), in both themes, numbers
  that are not finite, degenerate polygons, polylines and segments, circles, disks, arcs,
  sectors, regions and angle marks with a radius that is zero, negative or not finite (drawn as
  nothing), roles the style does not name, and colours the inline dark theme would restyle
  wrongly (also for plots). Direction controls and invisible characters in a label's text are
  dropped when it is drawn and measured (`labelText`); showing a visible mark for them was the
  alternative rejected, since the built-in lettering has no glyph for one and an SVG text label
  would still be reordered by the control. A recorded incidence names its element by title
  (`Item.named`) and is held to
  it: a point recorded on an element but drawn away from it, or on the wrong side of a region, is
  itself a problem, and a record against one element does not excuse a point from another. A
  figure's `checks` level makes builds warn or fail. Automatic placement (`auto`, and `across` a
  segment for a piece's label) takes the least offset and the first side that clears, 3 pixels
  from strokes and markers where it can, chosen twice (the second time in the frame the first
  placement gives).
* **Dark colours of inline pictures.** A page that shows a picture inline restyles it in its dark
  theme by its light colour values (`Style.darkColourPairs`). Classes on every drawn shape, keyed
  on its role, are the alternative rejected: they would change the drawing that the proofs
  describe and every file. The check `darkThemeClash` reports instead each element whose colour
  would come out other than its dark twin's: a fixed colour equal to a style colour, or roles
  that share a light colour with different dark ones; for plots, a fixed colour of a series, a
  bar group or a band equal to a style colour. Graphs are not put inline. The site check ties the
  page's theme rules to the pairs the manifest records for the file.
* **Text and small screens.** SVG text is drawn as shapes by default (`textAsShapes`), so every
  viewer shows the lettering the layout measured; `narrowWidth` renders the figure a second time
  at a narrower page with labels and markers at their full pixel size, for small screens. For
  mathematical labels the LeAnTeX engine is the one to use (`loadSans` sets formulas in New
  Computer Modern's sans-serif math font, Greek included); the built-in lettering is meant for
  plain words and numbers.
* **Explorers and inline pictures on web pages** (`pilean-verso`, `pilean-verso-manual`). An
  `Explorer`'s frames are put inline in the page (`:::figure_explorer`), as a single figure can be
  (`:::figure … (inline := true)`): elements with a title show it on hover, elements that name a
  declaration link to it in the site's link mode (`--figure-lean-links ideil|site|none`: `lean:`
  links for an editor, links into the built site, or none), and one picture serves both themes
  through attribute selectors keyed on its light colours (`Style.darkColourPairs`), in a `style`
  element a content policy must allow. Each inline picture names its file in the figures folder,
  and the example's site check compares the two against the manifest. A small script of the
  site, with no network, no `eval` and no `innerHTML`, shows one frame at a time and pans and
  zooms with cooperative gestures, as embedded maps do (the page keeps the wheel and one-finger
  swipes; Ctrl or ⌘ with the wheel, and two fingers, zoom the picture); without it every frame is
  shown in a grid. Alternatives rejected: the wheel always zooming (it traps the page's scrolling
  under every explorer), one finger panning (the same on touch screens), and a view box shared
  in pixels between frames of different sizes (it crops the smaller ones). The inline SVG of one
  figure is limited (`--figure-inline-limit`, 2,000,000 bytes by default), counted once over all
  the pages put inline for it. The example manual's explorers page (two explorers of 5 and 4
  frames and one inline figure with its narrow rendition, 11 pictures) is about 200 KB of HTML, of
  which 121 KB are the pictures: a plane frame of a few dozen elements is 10 to 14 KB of inline
  SVG, about 4 KB of it its theme rules. Frames share no definitions (plane figures have none to
  share).
* **Explorers as files.** Every frame of an `Explorer` is an output of its own (an SVG named
  `-frame-k`), so every picture a page shows inline is a file in the manifest with its
  fingerprint, the inline picture byte for byte the file before its source record; the poster's
  SVG and PNG come first. Every frame keeps the problems of its figure's checks, which a build
  reports frame by frame, or which stop the explorer when a frame's level is `fail`;
  `Explorer.toAnimation` gives every step the same number of frames (`Explorer.stepTiming`).
* **Arcs** (`Path.arc`): at most a quarter turn per cubic, control points on the tangents at
  `(4/3) tan(δ/4) r`, radial error at most `r (2/27) sin⁶(δ/4) / cos²(δ/4)` (Goldapp 1991), at most
  `2.73 × 10⁻⁴ r`; the tests sample the curves against this bound.

## Combinatorial diagrams

`PILean.Diagram` draws a finite object from its data so that what is drawn can be read back and
compared with the object. The choices:

* **Exact marks with parts.** A `Diagram` is a list of `Mark`s: an exact shape (rational points)
  and the `Part` of the object it depicts. The kinds' predicates read the diagram back by parts
  (`Diagram.edges`, `cells`, …), never by position in floating point, so the theorems are about
  the same values the drawing is made from and decidable for any diagram, which is what the
  planted-fault tests use. The alternative, a theorem about the plane figure's items, would be
  about floating-point numbers that no theorem can pin.
* **Full lists, then mark by mark.** Each `Faithful` states the drawn parts as a list equal to a
  canonical list of the data's parts (all of them, in order, each once) and checks every mark
  against the layout. The canonical list has its own characterisation (`mem_edgePairs`,
  `mem_coverPairs`, `mem_cellList`, `mem_inversions`), so the reader of a theorem need not read
  the list's code.
* **Rendered as plane figures.** `Diagram.toPlane` makes one plane item per mark with the exact
  builders, so styles, themes, labels, layout checks and outputs are those of plane figures, and
  the renderer's identity covers `Diagram.Basic`. A dot that lies exactly on a circle of the
  diagram records it (an exact rational test), as the plane checks require.
* **Caps before work.** Each builder checks its cap on the data before any work that grows with it
  (`Diagram.capped` takes the diagram as a function of `Unit` so that it is not computed past the
  cap); beyond the cap the figure is a note. The theorems for `figure` take the cap as a
  hypothesis; `draw` has none.
* **Layouts.** The circle uses rational points exactly on the circle (the rational
  parametrisation at a rounded tangent, turned by exact quarter turns), near the equal angles; the
  Hasse layout layers by height, the lowest at the bottom, ordering each layer by one sweep of mean
  positions; trees use the tidy algorithm of Reingold and Tilford (contours, separation 1, parents
  centred), chosen over Buchheim's linear-time variant because the work is bounded by the cap and
  the simpler algorithm is easier to state; a Venn diagram uses fixed circles and fixed places per
  region whose membership is decided once by the kernel (`slots_correct`), so that the statement
  about every element follows without arithmetic at drawing time.
* **The Mathlib side.** The core holds the kinds over plain data and no Mathlib; `pilean-mathlib`
  gives each kind a function from Mathlib's object and a theorem in Mathlib's terms, and its
  figures are defined in a module without Mathlib so that the drawing program does not contain it.
* **Standing.** Whether a figure is proved is computed where the table of figures is elaborated,
  from the links `figure_proves` recorded, re-checked there, and carried on every `Output` so that
  the positional constructors of `FigureEntry` and `SourceData` that the Verso adapters use stay
  as they are.

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
`Init` and `Std` only for the drawing library, so that any Lean program can use it without a large dependency. LeAnTeX
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

