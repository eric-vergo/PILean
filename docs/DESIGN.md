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
| `PILean.Pdf` (`Object`, `Write`, `Read`, `Check`, `Figures`) | one-page vector PDF 1.7 of any picture, written from the SVG nodes its PNG is drawn from (paths, fills, strokes, opacities, transparency groups, clips, shadings for gradients, text as outlines, raster images with soft masks); a bounded reader of objects, cross-reference tables and the information dictionary; a structural check of PDF files | done; see "PDF" below |
| `PILean.Png` | PNG writer and reader: CRC-32, Adler-32, DEFLATE (stored, fixed and dynamic Huffman; inflate with every bound checked), filters, `tEXt`/`iTXt`/`zTXt`, `sRGB`, `gAMA`, `pHYs` (written); the reader takes every colour type and depth and Adam7 (the writer does not interlace) | done |
| `PILean.Anim` | a `FrameSeq` (equally sized RGBA frames, a rational delay each, a loop count) and its codecs. APNG: writer (frame differencing to the changed rectangle, equal frames merged, delays as reduced fractions) and reader (composes `dispose_op` and `blend_op`, any PNG colour type, caps on size, frames and bytes). GIF89a: writer (LZW, one global palette by median cut or the exact colours, optional Floyd–Steinberg dithering, differencing with a transparent index, delays in centiseconds with exact cumulative time, loop extension) and reader (global and local tables, interlacing, disposal 0–3, transparency, caps) | done |
| `PILean.Canvas`, `PILean.Style` | the vector canvas (`Shape`: paths with fills and strokes, text, groups with transforms, opacity and clips, metadata through `Shape.tagged` and `ShapeInfo`; gradients), written as SVG or drawn as PNG from the same SVG nodes; the `Style` record of every visual constant, `Style.light` and `Style.dark`, with the plane colours and sizes `PlaneStyle` | done |
| `PILean.Plane` (`Basic`, `Frame`, `Draw`, `Check`, `Render`, `Graph`, `Motion`, `MotionPlan`, `MotionOutput`) | plane figures: elements in world coordinates (`Geom`: points, lines, arcs, regions of disks, ticks, labels, …), looks by role (`Look`, `Tone`, named roles), items with metadata (`Item`), builders and modifiers; the frame (`Frame`, one scale, `y` up) fitted to the items' reaches (`Frame.fit`), clipping (`clipLine`); the figure (`Figure`) drawn on the canvas; layout checks and automatic label placement; outputs (sRGB images, outlined text, narrow renditions); graphs inside plane figures, step animations; motions through exact key frames (turns, slides, fades, morphs) written as SMIL and baked as frames | done; motions are build outputs (`PILean.Trust.Motion`) |
| `PILean.CheckLevel` | how strictly a figure's checks apply (`ignore`, `warn`, `fail`), shared by plots and plane figures | done |
| `PILean.Explorer` | families of frames for web pages (a parameter axis, steps with captions, or the values of a second parameter), figures as functions of one or two parameters over a grid (`Explorer.family`, `family₂`), caps on frames and bytes, their poster files and animations | done |
| `PILean.Exact.Plane`, `PILean.Exact.Algebraic`, `PILean.Exact.Spec` | exact points: rational balls (`RatBall`, `sqrtBall`), the classes `RealValue` and `PlanePoint` with their laws, instances for `Rat`, `Int` and their pairs, builders from exact points, theorems on where they are drawn; exact incidence with a disk; ℚ(√d), ℤ[ζ₅], exact square roots, constructions with certified enclosures; what an item of a figure is in exact terms (`IsPoint`, `IsDisk`, `IsSegment`, `IsRegion`), for specifications | done |
| `PILean.Diagram` (`Basic`, `Graph`, `Hasse`, `Young`, `Perm`, `Tree`, `SetSystem`, `Path`, `CommDiagram`, `Group`, `Quiver`) | diagrams of finite combinatorial objects and orders drawn from their data: exact marks tagged with the part they depict, read back by `Faithful` predicates with theorems for every kind, drawn as plane figures | done; faithfulness proved for every kind, see [`PROOFS.md`](PROOFS.md) |
| `PILean.Graph.Fixed` | graphs at given positions (page, world or exact), edges straight or bent around nodes | done |
| `PILean.Text` | `TextEngine` (measure, ascent, descent, shapes, identity, whether its strings are plain text) and the built-in single-stroke lettering that draws text into images; LeAnTeX implements it in the package `pilean-leantex` (`leantex/`) | done |
| `PILean.Anim.Animation` | an animation as a drawing over time, written as animated SVG (SMIL), APNG and GIF, with a poster frame | done |
| `PILean.Anim.Timeline`, `PILean.Anim.Smil` | timelines of looping motions through key frames (exact rational durations, cubic Bézier easing, the seam that closes the loop; tiling of the cycle proved) and SMIL animation elements on such a timeline, with an evaluator of SMIL timing for tests | done; used by the motions of plane figures |
| `PILean.Graph` | `Graph` (nodes, edges, clusters), the layered (Sugiyama) layout with spline, orthogonal or bundled edges (one entry and one exit port per node, tracks in channels, concentric corners), arrowheads, edge labels and clusters, circular and tree layouts, components laid out apart and packed, mirrored layouts, drawing on the canvas as SVG and PNG, and as SVG for a web page | done; layering proved, see below |
| `PILean.Trust` | done: a figure's standing (`linked` or `illustration`, recorded in its files and the manifest, `--require-standing`); SHA-256 (`Sha256`, padding and digest size proved, FIPS and NIST vectors tested); source information (module, declaration, file, line, repository, commit, version, fingerprint) written into SVG, PNG, APNG, GIF and PDF and read back by a bounded reader, `lake exe pilean-info`, see [`TRUST.md`](TRUST.md). `@[figure]` and `figures%` (declaration, file, line, source hash), fingerprints of figure specifications (SHA-256), `lake exe pilean-build` (deterministic build with `manifest.json`, `--check`) and `lake exe pilean-verify`; `figure_links` links a figure to a theorem about it ([`PROOFS.md`](PROOFS.md)); motions as build outputs (`PILean.Trust.Motion`: the animated SVG, key stills, contact sheet, the manifest's `motion` kind) | done |

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
  `laneGap` per track, and as much and an arrowhead below its last; nothing is squeezed. A route
  keeps `clusterGap` (by default twice `laneGap`) from every cluster that holds neither of its
  ends: a lane and the corridors a node keeps on its right stand that far from
  the side of a cluster they stay outside, clusters side by side stand that far apart (so a route
  inside one keeps it from the other), and the first and last tracks of a channel keep as much
  from the clusters that end above it and begin below it. The tests check this on the hostile
  graphs at lane gaps from 3 to 40 (`PILeanTest/GraphBundles.lean`).
* *Lanes placed.* The coordinate phase keeps a long edge's dummy nodes in one column (the weights 1,
  2 and 8 of Gansner et al.), but in the place the crossing reduction gave them in each layer, and
  that place is often the end of the layer: the lane then runs round the outside of the drawing or
  of a cluster, a long way from both of its ends. Before the routes, `placeLanes` moves every
  chain's dummy nodes, long chains first, to places found by a shortest path over the chain's
  layers: in each layer the candidates are the free places (at least the separation of the
  coordinate phase from every node, dummy node and cluster side there, inside the cluster that holds
  the chain's block and no deeper) nearest the stretch between the ports of the edge's two ends,
  where a rectilinear route is no longer than the distance between its ends; a step between two
  layers costs its length across, `4 × laneGap` when it moves across at all (a run and two corners)
  and as much for every leg of another edge it crosses, and does not cross the side of a cluster
  that reaches over both layers unless the old step did. The new places are kept when they save more
  than `4 × laneGap`, cross no more legs of other edges and cross no more other edges twice than the
  old ones. Only the part of a layer within `64 × laneGap` of the ends' stretch and of the old place
  is looked at. Two such passes; a bound on the work (60 million steps: items of the layers, legs
  compared, candidates) stops them on a graph too large for it. Then jogs narrower than a lane are
  closed: a run of a chain's dummy nodes moves onto the line of its neighbour in the chain
  (`straightenLanes`), and a real node moves by less than a lane onto the line of one of its edges'
  next nodes (`alignPorts`), each when that closes a jog without opening another and its layer has
  room (at most three passes each, linear in the dummy nodes or the ends of the edges times the
  breadth of a layer). One column for the whole chain, the free one nearest its ends, was measured
  first: on the blueprint of 67 nodes with the site's style it took off 0.5 thousand of the 18
  thousand pixels by which the routes exceed the distances between their ends, where the shortest
  paths take off 3.5 thousand, because a column free in every layer of a long chain is rare.
* *Corners.* Corners of one turn whose centres can coincide (lanes `laneGap` apart turning onto
  tracks `laneGap` apart lie on one diagonal) form a bundle and are concentric quarter circles: the
  innermost of radius `radius`, the lane `k` places further out `radius + k × laneGap`. The rule
  that fits them: of a segment between two corners each takes at most its share in proportion to
  the radii they want, of a segment at a port at most its length less the stem (and the
  arrowhead); a bundle that does not fit keeps its corners concentric with a smaller innermost
  radius when one of at least zero is enough, and is scaled as a whole otherwise.

Work: the legs of the routes are the sum of the spans of the edges; placing the lanes costs, per
chain and pass, the breadth of each of its layers and, per step, the legs of other edges in that
channel times the logarithm of the candidates and the candidates squared (at most 13 a layer),
within its bound; a channel of `k` runs costs
`O(k²)` (the nesting order and the tracks compare runs pairwise; at most `k` doglegs, each `O(k)`
to find its column), up to `BundleStyle.maxRuns` (4000) runs; a channel with more gives each run
a track of its own in `O(k log k)`, without the constraints between them: the promises tested
below (no shared segment, lanes apart) do not hold for such a channel. `lake test` lays out
5000 bundled routes leaving one node, 20000 parallel edges and 10000 nodes with ten self-loops each
under CPU and memory bounds.

*Proved* (`Graph/Channel`, `Graph/Bundle`): two runs in conflict never share a track
(`tracksInOrder_ne`, for any symmetric conflict, and the conflict of `placeRuns` is symmetric:
`RunPart.conflicts_comm`; that this conflict covers every pair that must not share a track is
tested); every route, before its corners are rounded and its ends cut for stems and arrowheads, is a
walk of horizontal and vertical moves that starts at its source's exit port and ends at its target's
entry port (`routeWalk_head`, `routeWalk_last`, `routeWalk_axis`). *Tested*
(`PILeanTest/GraphBundles.lean`, on every measured graph and graph file but the two largest, on
hostile graphs: multi-edges, self-loops, cycles, a node with 200 edges in or out, a chain with
shortcuts, complete bipartite graphs, nested clusters, labels, an undirected graph; from the top
down, left to right, both mirrored and packed; each checker with a planted fault): every route
leaves at the exit port and enters at the entry port of the finished picture, its segments and the
straight pieces of its path are horizontal or vertical, no two edges share a piece of a segment
except the trunk of a port both use, no route passes within two pixels of a node it does not end at,
parallel segments of two edges are at least `laneGap` apart, no route comes nearer than `clusterGap`
to a cluster that holds neither of its ends, one arrowhead per entry port and none on an edge;
crossings at most a fiftieth above the spline routes'; no more edges through a foreign cluster than
the spline routes; in random channels two runs cross at most once, and not when their ends agree.
The style space is tested at its defaults on the corpus and, by an independent check, from lanes 3
to 12 apart, radii 0 to 20, stems 0 to 30 and track gaps 4 to 24 on hostile and 500 random graphs,
and the hostile graphs also with lanes 8 apart, radius 10, stems 14 and track gap 16. Two edges can
still cross more than once in all when the layers' order swaps them in one channel and back in
another (the measures count such pairs: up to 6 of 793 edges on the neighbourhood of 290 nodes; with
the site's style, 13 of 171 on blueprint 67 by chapter). Placing the lanes keeps a move only when
the chain then crosses no more other edges twice; a step of the ordering that removed them would
have to see the channels as the routes cross them, which the crossing reduction (two layers at a
time, edges as straight segments) does not.

*Measured* (`lake exe pilean-test --bundle-measures`, the default `BundleStyle`: lanes 6 pixels
apart, innermost radius 6, stems 10, runs on one track 12 apart; the routes measured as polylines
from port to port, the spline routes as flattened curves; `dot`'s numbers are the recorded ones of
`PILeanTest/graphs/dot-recorded.tsv`, its area without cluster boxes, PILean's with them; the
longest route, the length by which the routes exceed the rectilinear distances between their ends,
and the routes with a point outside the box around the nodes are the bundled routes'). The bundled
routes follow the spline routes' orders, and placing the lanes only removes crossings, so their
crossings are at most the spline routes' and up to 8 per cent fewer (and fewer than `dot`'s on the
graphs with clusters); they are about 1.3 to 1.7 times as long (a rectilinear route against a
straight or curved one), and the drawings take up to about a tenth more area, as the channels grow
with their tracks, except where one node has hundreds of edges: every edge has its own lane, so a
node with 400 neighbours in the layer below needs 200 tracks on each side of its stem (seven times
the spline drawing's area). Drawing the runs that leave one stem in one direction on one shared
track, which the edges leave one by one, would remove that cost, but the edges would then share
horizontal segments outside the stems, and keeping the channel's constraints for such a track needs
runs with several ends on it (the multi-terminal nets of channel routing), which `placeRuns` does
not place; there is no such mode.

| Graph | Crossings (spline / bundled / `dot`) | Edge length (spline / bundled / `dot`) | Longest route | Length beyond the ends' distance | Area, Mpx² (spline / bundled; `dot` without clusters) | Bends per edge | Jogs narrower than a lane | Pairs crossing twice | Routes outside the nodes' box |
|---|---|---|---|---|---|---|---|---|---|
| blueprint-a | 254 / 238 / 252 | 59712 / 85728 / 71977 | 2908 | 7500 | 2.93 / 3.29; 3.29 | 2.95 | 1 | 0 | 1 |
| blueprint-a-chapters | 264 / 250 / 310 | 76561 / 107325 / 84947 | 3634 | 9066 | 4.31 / 4.58; 3.77 | 3.41 | 2 | 0 | 2 |
| blueprint-67 | 296 / 280 / 279 | 99094 / 126757 / 108473 | 3580 | 13960 | 5.08 / 5.14; 5.39 | 3.2 | 2 | 0 | 6 |
| blueprint-67-chapters | 437 / 404 / 529 | 135787 / 175437 / 127946 | 3866 | 9318 | 7.97 / 7.97; 4.96 | 3.72 | 0 | 0 | 1 |
| blueprint-b | 85 / 85 / 80 | 35348 / 47111 / 31074 | 1671 | 676 | 2.9 / 2.72; 2.76 | 2.14 | 2 | 0 | 0 |
| own-imports | 221 / 220 / 213 | 96236 / 124412 / 108109 | 3098 | 10804 | 4.38 / 4.46; 5.48 | 3.01 | 8 | 0 | 2 |
| project-imports | 105 / 105 / 140 | 39959 / 57290 / 46426 | 1356 | 1504 | 2.77 / 2.94; 3.49 | 2.43 | 1 | 0 | 0 |
| code-site-c-modules | 185 / 184 / 163 | 66847 / 91566 / 66155 | 3474 | 9648 | 6.74 / 6.96; 6.96 | 2.81 | 0 | 0 | 0 |
| module-800 | 7594 / 7563 / 6190 | 966400 / 1315173 / 988805 | 9904 | 36654 | 40.73 / 46.75; 41.92 | 2.65 | 22 | 0 | 1 |
| dense-dag | 751 / 741 / 713 | 74916 / 125765 / 109216 | 1019 | 5288 | 2.4 / 2.51; 7.18 | 3.14 | 6 | 2 | 0 |
| sparse-dag | 249 / 249 / 270 | 54793 / 81071 / 50956 | 1672 | 300 | 5.26 / 5.84; 8.93 | 1.66 | 1 | 0 | 0 |
| neighbourhood-34 | 146 / 144 / 159 | 40869 / 56403 / 44034 | 2359 | 4706 | 1.78 / 1.98; 2.26 | 2.97 | 1 | 0 | 5 |
| neighbourhood-150 | 2892 / 2743 / 3776 | 748520 / 1000350 / 1064583 | 12931 | 67214 | 26.89 / 27.94; 27.08 | 3.91 | 10 | 1 | 5 |
| neighbourhood-290 | 6198 / 6192 / 7229 | 1197885 / 1702168 / 1534595 | 14194 | 90688 | 32.68 / 67.03; 26.80 | 3.38 | 2 | 6 | 0 |
| tree | 0 / 0 / 0 | 11418 / 15333 / 9468 | 1547 | 0 | 2.55 / 2.12; 2.12 | 1 | 0 | 0 | 0 |
| neighbourhood-star-401 | 0 / 0 / 0 | 10670338 / 11194781 / 10594068 | 54788 | 0 | 19.9 / 140.17; 12.84 | 2 | 0 | 0 | 0 |
| code-site-c-largest-module | 16 / 16 / 1003 | 10766097 / 11317539 / 10901646 | 54788 | 0 | 33.21 / 191.93; 13.22 | 1.97 | 0 | 0 | 0 |


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
  be removed or a label moved without breaking any proof. The strict figure link (`figure_links`:
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
  SVG, PNG and PDF come first.
* **Families over a grid.** `Explorer.family` and `Explorer.family₂` make an explorer of a figure
  as a function of one or two parameters (`ExplorerParam`: a name, values, a label): the frames
  are the function at the points of the grid, axis-major, computed when the explorer is built
  (`family₂_frames`, `mem_family₂_frames`), and the page only shows the frames it was given. The
  second parameter is the explorer's steps with a name (`Explorer.stepName`), which the page shows
  with a slider beside previous, play and next, so one structure serves step sequences, one
  parameter and two. An explorer over a family gets its standing from a theorem quantified over
  the grid (`∀ p ∈ grid, …`) that names the explorer, as `figure_links` requires; the gallery's
  `cayleyExplorer` and `latticeExplorer` (`PILeanTest/Explorers.lean`) have such linked theorems, with
  bindings to `ZMod n` and `Submodule.span ℤ` in `pilean-mathlib`. Separate controls for each
  parameter, each with its own play button, were the alternative; one played parameter keeps the
  controls few and the motion legible. Caps: at most `Explorer.maxFrames` (400) frames and
  `Explorer.maxBytes` (8 MiB) of frames' SVG together, checked before the outputs are written;
  the Verso adapters' inline limit (`--figure-inline-limit`) applies on top. Every frame keeps the problems of its figure's checks, which a build
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
* **Every mark by class.** The kinds of algebra (commutative diagrams, Cayley tables, quivers)
  state `Faithful` as one list per class of part (`Diagram.marksWhere`) equal to the builder's,
  and no mark of another part; so a tip, a hook, a colour or a label the data does not call for
  is refused without a predicate per shape. A colour role is compared where it means something
  (an element's colour in a table, a generator's in a Cayley graph, a marked vertex), never its
  RGB value.
* **Arrows.** An arrow's body is a `Shape.path` of exact points cut where it meets the boxes of
  its objects' labels (estimated from their lengths, in units of the grid); straight arrows are
  cut exactly, bent ones and loops are Bézier curves sampled at exact rational parameters.
  Parallel straight arrows stand `1/8` apart, the first leftmost. The tips are the plane figures'
  arrowheads on the last piece of the body, so they follow its direction.
* **Commutation is about the object.** A picture of a diagram makes no claim by itself; the claims
  are data (`paths`), decided for maps between finite sets in the core and stated for morphisms of
  a category in `pilean-mathlib`, where the realisation carries the morphisms with their types so
  that no cast is needed beyond the identity of an object to itself.
* **Plots of sequences.** A plot is a diagram, not a `Plot.Figure`: its points are exact marks
  tagged `datum k n`, so that the theorem says which values are drawn and where. The axes stand a
  tenth of a unit outside the lowest value and the first tick, so that no point lies on an axis
  (the alternative, axes through the origin, puts points of value `0` on the line, where the
  plane checks rightly cannot tell incidence from nearness); the index axis starts at the multiple
  of its tick step at or below `lo`, so the ticks fall on round indices. The points' radius is
  `135 / count` pixels between `1` and `3`, so that, up to 140 indices, consecutive indices keep a
  gap of more than half a point's width between them at the page width (with `180 / count` the points of a run of
  equal values touched). The plane checks require markers of a geometric figure to keep a ring and a gap
  apart; a plot of a hundred points cannot, and its abscissae already tell the indices apart, so
  `plotProblems` accepts two points of a plot whose discs do not overlap, and a point near a
  comparison curve (a point is read against the axes, not the curve). Everything else of the
  checks applies.
* **Grids and lattices.** A grid's marked cells are tinted when they carry text and filled opaque
  when they do not (an Ulam spiral), the filled ones a twelfth of a unit inside their square and
  the tinted ones a sixteenth, so that marked neighbours stand apart and no stroke lies on a
  fill. A grid can ring one cell, inside it (the Ulam spiral rings `1`, its start) and write a legend below
  its cells: a sample of the marked fill and what it means (the sieve: a prime; the table of
  residues: a nonzero square mod `p`); both are decorations its `Faithful` accounts for. A lattice's coefficients are bounded
  from the window by Cramer's rule, rounded up; the core proves that the dots are the candidates
  in the window, and `pilean-mathlib` that the bound covers every lattice point of the window
  (inequalities over ℚ are Mathlib's). Points on the axes record that they are on them
  (`axesThrough`, an exact rational test), as points on circles do.
* **Zeros and poles** (`RationalPlot`, `Diagram/ZeroPole.lean`). The numerator and the
  denominator are lists of rational coefficients and the zeros and poles are supplied as Gaussian
  rationals with their multiplicities; the core decides, in exact Gaussian rational arithmetic,
  that each supplied point is a root of exactly its multiplicity (the derivatives of lower orders
  vanish there, that of its order does not) and that the multiplicities add up to the degrees,
  and `pilean-mathlib` turns these into `Polynomial.rootMultiplicity` and "every complex root is
  marked" by the count of roots (`card_roots'`). Finding the roots was the alternative rejected:
  roots of degree five and more are not expressible, and an approximate root is not a mark a
  theorem can name; a supplied root is checked instead. Zeros are open circles in accent 0, poles
  crosses in accent 1, a multiplicity above 1 written beside its point, the function's name
  drawn as the title above the window.
* **Domain colouring** (`DomainColouring`, `Raster/DomainColouring.lean`) is a raster picture of a
  `Float` function, hue from the argument (OKLCH, so equal angles are equal steps of hue) and
  bands of lightness from `log₂ |f|`. It has no theorem and is marked `@[figure illustration]`,
  which its files, the manifest and the pages say; its outputs are a PNG and a PDF that embeds it
  (an SVG would have to embed a raster image, which the inert check refuses, or draw a rectangle
  per pixel).
* **Values computed or proved.** The figures of number theory compute with plain functions, and
  `pilean-mathlib` proves each equal to Mathlib's function for every argument, so the theorems
  stay quick to check; what the kernel evaluates is finite and small (the caps, the layouts, the
  Ulam spiral's positions in linear time by a bit mask, and the factor witnesses of the Gaussian
  integers of the window that are not prime). Kernel-evaluated loops are written by structural
  recursion (`spiralFrom`), since the kernel cannot unfold `while`.
* **Standing.** Whether a figure is linked is computed where the table of figures is elaborated,
  from the links `figure_links` recorded, re-checked there, and carried on every `Output` so that
  the positional constructors of `FigureEntry` and `SourceData` that the Verso adapters use stay
  as they are.

## PDF

`PILean.Pdf` writes a picture as a one-page PDF 1.7 file for papers (`Plot.Figure.toPdf`,
`Plane.Figure.toPdf`, `Graph.toPdf`, `ExplorerFrame.toPdf`, `Animation.posterPdf`,
`Image.toPdf`). The choices:

* **From the PNG's nodes.** The page is written from the SVG nodes the PNG is rasterised from
  (text as shapes from the style's text engine), read by the rasteriser's own readers of SVG
  (`Raster.shapeOf`, `Style.apply`, `clipPaths`, `gradients`), so the PDF and the PNG cannot
  disagree about what is drawn, and the specification and fingerprint of the PNG cover the PDF.
  A writer from the canvas's `Shape` directly was the alternative; it would be a third reading of
  the drawing beside the SVG writer and the rasteriser.
* **Page size.** One CSS pixel (`1/96` inch) is `0.75` points (`1/72` inch): a picture of
  `w × h` pixels is a page of `0.75 w × 0.75 h` points, and the content keeps the pixel
  coordinates under `0.75 0 0 -0.75 0 H cm`.
* **Text as outlines, no fonts.** Text reaches the PDF as the text engine's outlines, as it
  reaches the PNG, so the file embeds no font and every viewer shows the letters the layout
  measured. Text cannot be selected or searched; embedding the lettering or LeAnTeX's fonts as
  Type 3 or TrueType fonts was the alternative and is not built.
* **Opacity.** `fill-opacity` and `stroke-opacity` are `ExtGState` alpha constants. A group's
  `opacity` is a transparency group (a form XObject drawn at that alpha), as SVG composites it; a
  group that holds one shape painted once (a fill or a stroke) takes the opacity into the shape's
  alpha instead, which composites the same and needs no form.
* **Gradients** are axial and radial shadings painted inside the shape as a clip (`sh`), with a
  stitching function through the stops PILean writes into the SVG (sampled from its linear-light
  interpolation), extended at both ends as SVG pads; a gradient whose stops have different
  opacities is drawn at their mean opacity (a soft mask is not built).
* **Colour.** `DeviceRGB` with the file's 8-bit sRGB values; no ICC profile, so a viewer treats
  them as its device's RGB (on most screens and printers, sRGB). PDF viewers composite in that
  space, as browsers composite SVG; a plot's PNG composites in linear light, so its anti-aliased
  edges differ by a level or two.
* **Deterministic bytes.** The objects in a fixed order, numbers through `fmtNum`, content streams
  compressed by PILean's DEFLATE, no date, and a document ID from the SHA-256 of the body.
* **The source record** is the document information dictionary, added by an incremental update
  (`Trust.withSourcePdf`), so the writer stays unchanged and the reader of `pilean-info` follows
  one trailer to one dictionary. XMP metadata was the alternative: a stream of XML that the reader
  would have to parse, for no field the information dictionary cannot hold.
* **Checked.** `Pdf.check` reads a file through (cross-reference offsets, every object, stream
  lengths, the page tree, every operator of every content stream and the resources it names) and
  `pilean-build` refuses a PDF that fails it; `lake test` runs it on every gallery PDF with planted
  faults, and runs it and the source reader on 1100 mutated files and on hostile files under
  memory and time bounds (`PILeanTest/Bounds.lean`). `tools/pdf-compare.py` renders the gallery's
  PDFs with Ghostscript and Quick Look and compares them with the PNGs.

Across the gallery a PDF is 0.17 to 0.95 times the size of the picture's SVG (the median about a
third; the content streams are compressed, while the outlines of text make them longer than an
SVG with `<text>`), at most about 49 KB; the function plot of 640 × 400 pixels is 6 KB. The reader and the check are bounded (`Pdf.Limits`: 64 MiB of
input, nesting 32, strings of 64 KiB, dictionaries of 4096 keys, a million cross-reference
entries, 32 sections; content streams decode to at most 256 MiB, measured before they are
allocated).

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
instead of the motion under `prefers-reduced-motion: reduce`. The rule's classes carry the
library's prefix (`pilean-motion-poster`, `pilean-motion-live`), so that it reaches nothing else
when such a picture is put inline in a page; generic names (`.poster`, `.motion`) were the
alternative rejected, since a page's own elements of those classes would be hidden by them. The
moving picture is hidden and made transparent (`visibility:hidden; opacity:0`), not taken out of
the rendering (`display:none`): a browser that stops rendering a group and renders it again can
show it frozen until each animation next repeats. The transparency hides the frames of a
frame-switching animation, which animate their own `visibility`. `tools/anim-browser-check.py` loads
the wave and the graph-build animations in headless Chromium (through Playwright): the pictures at
0 s and 1.3 s differ, and with `prefers-reduced-motion: reduce` the motion is hidden, the picture
does not change with time and it matches the poster PNG.

A 120-frame animation of 640 × 360 pixels (the travelling wave, `lake exe pilean-test
--anim-bench`, load average about 14.5): drawing the frames 5.6 s; animated SVG 0.1 s (134,789
bytes); APNG encoding 5.9 s (1,876,963 bytes); GIF encoding 5.3 s (785,813 bytes). Drawing and
encoding share the time; the wave changes most pixels of every frame, so frame differencing
saves little here (the growing-bars animation is 63 KB as APNG).

### Timelines and SMIL motions

A motion through key frames has its timing in a `Timeline` (`PILean/Anim/Timeline.lean`), built
from its steps (`Step`: a move, or an idle step in which nothing moves, each with its duration and
its easing) and a `Pacing` (durations of turns, slides, fades, holds and idle steps, the first and
last holds, the easing that the steps made from it get, and the seam). The cycle is a rest on
key 0, then each step's move and the rest on the key it reaches, closed by the seam: under
`Seam.cut` the picture jumps back to key 0 when the cycle repeats; under `Seam.crossfade d` the
cycle starts with a fade in and ends with a fade out, `d / 2` each, so that jump happens while
nothing is visible. One function, `Timeline.spec`, gives every segment's duration and easing
(rests and fades are not eased). Durations are rationals (`Rat`): the start of every segment, the
cycle and the key times are exact, and the order of the segments, their durations and easings,
the tiling of the cycle, the key times from 0 to 1 and the segment found at a time are theorems
(`PILean/Anim/TimelineProofs.lean`, [`PROOFS.md`](PROOFS.md)). Floating point begins with the
eased progress through a segment: `Easing.eval` solves the cubic Bézier of SMIL's `keySplines`
(and CSS's `cubic-bezier`) for its parameter by 64 halvings and has its control values clamped
into `[0, 1]`, so it never overshoots.

`PILean/Anim/Smil.lean` writes SMIL animation elements on a timeline: `animateRotate` (values
`θ cx cy` of an `animateTransform` of type `rotate`), `animateTranslate`, `animateOpacity`,
`animateD` (a morph between paths with the same commands, checked with `interpolable`) and
`seamOpacity` (the fades of the motion layer). Each is first a `Smil.Track` (values at the
boundaries, key times, one easing per interval) and then an element; a builder gives `none` for a
cycle that is not longer than zero. Every element has the same timing (`smilTiming`: the cycle as
`dur` to the microsecond, the key times to eight decimals, one spline per segment,
`calcMode="spline"`, indefinite repetition, `begin="0s"`), so all the animations of a document run
on one clock; `Smil.clockProblem?` checks a whole tree for that. The values are written at the
segment boundaries, a rest repeating its value under the identity spline `0 0 1 1`. The builders
write no static `transform`: a transform is only ever the animated value of an `animateTransform`
that `group` places, alone, in a `g` without attributes, and only `transform`, `opacity` and `d`
are animated, so the inline dark-theme rules, which restyle colours, keep working
(`Smil.invariantProblem?` checks a tree, and also refuses `gradientTransform`,
`patternTransform`, a `style` with a transform, and `additive` or `accumulate`). An actor turned in
several steps sits in one group per turn with the earliest turn innermost, so that every centre is
a point of the page (`Smil.nest` builds the chain in that order); `turnAngles` turns exact fractions
of a full turn per step into the angles after each key, and `uprightAngles` gives the
counter-rotation that keeps a label upright about its anchor.

A segment of length zero would give two equal key times in a row. `Smil.Options.gap` (default
`1/10000` of the cycle, at least `10⁻⁷` when above zero, at most `1/(2m)` for `m` intervals)
keeps consecutive key times that far apart: a time too close to the one before it moves later,
then one too close to the one after it moves earlier, so the first stays `0`, the last `1`, and
only times next to a short segment move. The written key times are proved to start at `0`, end at
`1`, lie in `[0, 1]` and increase strictly; a gap of `0` writes equal key times as they are.
`Smil.valueAt` computes the value of an animation element at a time as SMIL defines it and refuses
what SMIL makes an error (key times that do not start at `0` or end at `1` or decrease, counts that
disagree, spline values outside `[0, 1]`, a `dur` that is not a positive clock value), so tests
compare what a document shows with what the timeline means without a browser; key times written to
eight decimals move an angle by less than `1e-5` degrees on the tests' 22.6-second cycle.

### Motions of plane figures

A `Plane.Motion` (`PILean/Plane/Motion.lean`, `MotionPlan.lean`, `MotionOutput.lean`) animates a
plane figure through exact key frames: key `k` is a `Plane.Figure` (exact data, as any figure), and
each step between two keys says what its *actors* do (`MotionStep`, `Move`): an actor is a top-level
item with an id (`Item.actor`), which turns about a centre by an exact fraction of a full turn
(`Plane.Exact.turnAbout`), slides (`Plane.Exact.slideFromTo`), appears, vanishes or morphs.

*What is exact.* The key frames are the figures as written, drawn by the plane figures' own
pipeline in one view (`commonViewWith`, so nothing rescales during the loop; the view holds what
the turns sweep, `Motion.sweptItems`, and a check keeps every layer inside the picture while it
moves, `boundsProblems`), an actor's automatic labels placed as on the first key where it appears:
the stills (`Motion.keyFigure`) are those drawings, byte for byte, and no still or raster is
derived from the animation. The timing is the exact rational `Anim.Timeline` of the steps.

*What the checks promise.* The arrival check compares the actor in key `k`, carried by the declared
turn or slide (applied in floating point to the page points that fix its drawing, `anchors`: a
point, the ends of a segment, a circle's centre, a polygon's vertices, the ends of an arc, a label's
point), with the actor in key `k + 1`: the same leaves in order, of the same kinds, looks, texts,
placements and metadata, radii and every anchor within 0.01 px. It does not determine the direction
or the number of revolutions of a turn (for a turn by `1/5`, `6/5` and `-4/5` land too; a turn by a
whole turn or more is an error unless the step sets `allowFullTurns`), says nothing about what the
turn leaves alike (a disk centred on the turn's centre, a whole turn: a note says so), and does not
tell a slide from a turn with the same end points; for a single point and an angle that is not a
whole turn, the centre is determined. A polygon whose vertex list is the same after a symmetry turn
is refused (the next key lists the turned vertices in the turned order). A move that misses its key
is an error and is not animated as that move. The stronger guarantee is the rest check
(`Motion.restProblems`, part of `Motion.problems` for every motion): at the middle of every key's
rest the whole baked drawing, every path and every text in order, must be the key's still within
0.05 px (plus `5.5e-4 r` for a path of half-width `r`, the most two cubic approximations of one
circle of radius `r` differ, since a turned circle is not drawn by the same cubics as the next key
draws it; a text also unturned within `1e-4` radians); this bounds what the per-step tolerance adds
up to along a chain, and catches a wrong upright position or stacking order. The comparison is
between outlines: it does not see the phase of a dash pattern, so a dashed circle turned about its
own centre passes while its dashes move. The writer is checked against the baker for every motion
too (`Motion.writerProblems`): at the middle of every rest and every move, the written picture, read
with `Smil.valueAt`, must show what the baker draws, which checks what the baker never reads, such
as the angles of the counter-rotations. A key that draws its layers in another order than the
earlier keys is an error. An item without an id that changes between two keys is crossfaded with a
note; an actor that changes without a declared move, leaves without `vanish`, comes without `appear`
or has a morph that cannot be interpolated, an empty title, and neither a description nor a caption,
are errors under `checks := .fail`, the default, under which `Motion.svg?` and `Motion.animation?`
give the errors instead of the picture. `Motion.report` computes the keys, the plan and the problems
once, for all the checked outputs. The names that end in `Unchecked` (`Motion.toSvgUnchecked`,
`figureAtUnchecked`, `toAnimationUnchecked`) write whatever the problems say, for tests and tools.
An actor's recorded incidences (`Item.incident`) describe a key, not the drawing: two keys draw an
item alike, and a move carries it, whatever its records and their words in its title
(`Item.baseForm`); a layer whose records change between its keys is written without them, and the
stills keep each key's. Every key passes the layout checks as drawn; an automatic label of an actor
keeps its first key's placement on the later keys, where it must pass the checks too. Lines and rays
(drawn to the edge of the page) cannot turn or slide; a segment can. Labels and point markers keep
their look and ride the turns upright; ticks, angle marks and every other element turn with their
actor (a tick marks a direction, and the next key draws it turned).

*What the browser interpolates.* The animated SVG (`Motion.svg?`) writes every drawable part of
the motion once (a *layer*: an actor for as long as its steps carry it, an item without an id for
as long as the keys draw it alike) and moves it with SMIL on one clock: each turn is the
`animateTransform` of type `rotate` of a group of its own, the earliest turn innermost, so that
each centre is a point of the page and the browser draws true circular arcs; each slide is one of
type `translate`; labels and point markers sit inside a counter-rotation about their anchor by
minus the angle so far, so that they ride the turns upright; fades animate `opacity` and morphs
`d` (between drawings whose paths have the same commands, else the two crossfade). Between the
keys the browser computes the eased angle, offset, opacity and path data: that is floating point
in the browser, checked in Chromium. Actors that move alike in every step share one chain of
groups (a rigid body of many items is one chain), and consecutive layers shown on the same keys
share one opacity animation (points that appear together are one animation). Every group with an
actor carries `data-pilean-actor` and `data-pilean-anchor`, and every group of upright leaves
`data-pilean-upright` (a point's marker and its label, siblings with one anchor, share one
counter-rotation), so that tests can find them. The root has `role="img"` and the motion's
title, and a description with the captions; the poster key's still is inside, shown instead under
reduced motion. Only `transform`, `opacity` and `d` are animated and no static transform is
written, so the inline dark-theme rules keep working.

*The baked frames.* `MotionPlan.figureAtUnchecked` draws the same plan on the vector canvas at a
time: every layer's shapes turned and slid by its chain's transform then (labels and markers
translated only), at its opacity, with the values the SVG writes (rounded as written) at the key
times it writes; `Motion.animation?` makes it an `Animation` for APNG and GIF. What pins what is
listed in [`PROOFS.md`](PROOFS.md): the stills are the keys; the baker is the stills at every rest
(`Motion.restProblems`, every element); the tests read the written tree with `Smil.valueAt` and
require as many actors and upright groups as the plan declares, each anchor, opacity and whole
transform where the baker has it (`1e-6`), at 50 times, and compare the baker with the model
computed apart from the plan (`1e-3` px); `tools/motion-browser-check.py` checks in Chromium that
each key's rest is the key's still up to antialiasing (every channel of every pixel within the range
of the other picture's pixels at most one pixel away, widened by 40; this sees a label moved by
about 2 px or more) and at its positions (every actor and every label's anchor within 0.05 px), that
a quarter, a half and three quarters of each turn lie on the turn's circle (0.05 px) at the eased
angle (0.5°), that labels and markers are not turned (0.01°) and are all there, that reduced motion
shows the still and switching it off again shows the running clock, and that the picture plays.

A morph is interpolated in the page's coordinates, so it must come before any turn or slide of its
layer (a later one starts a new layer, crossfaded). With figures between its keys (`Motion.between`)
a morph is sampled at `morphSamples` intervals: interval `i` ends at the time where the step's
easing has done `(i + 1) / n` of the step (`easedTime`), and every animation's value there is the
exact fraction `(i + 1) / n` of its change, so every animation of the step, turns included, follows
the eased motion piecewise linearly, within `1 / n` of its change, on one clock. For a turn the
deviation is a gap in timing along the arc, not off it: the item stays on its circle and is ahead or
behind the eased angle by at most `1 / n` of the turn; measured, a quarter turn is within 5.79° of
the eased angle with 4 samples, 2.92° with 8 and 1.45° with 16, and a fifth of a turn within 1.16°
with the default 16. The plan (`MotionPlan`) holds every animated value as a function of a phase (a
key, or a fraction of a step) and is computed in a drawing environment on a given timeline
(`Motion.planOn`; `Motion.planIn` on the motion's own), so that a picture of several panels lays out
each motion in a frame of its own on one shared timeline (below).

### Motions as panels on one clock

A `Plane.MotionPanels` (`PILean/Plane/MotionPanels.lean`) puts several motions side by side (or one
above another) in one `<svg>` on one timeline: the traditional view of a construction beside the
same construction in another frame, both moving at once. Each panel is a `Motion` with its own key
figures, steps and moves and its own view, under a title; the captions, the pacing, the title and
description and the level of checks are the picture's.

*One timeline.* All panels have the same number of keys, and step `j` of the picture is step `j` of
every panel. The step is idle only when every panel's step is idle; otherwise it lasts as long as
the longest kind of move any panel makes in it (a panel without moves idles while the others move),
unless the picture gives the step a duration or an easing of its own (`MotionPanels.timing`). A
panel's step may not set its own duration or easing: one step has one duration. A morph sampled in
one panel (`Motion.between`) divides the step for every panel at the same times, so the other
panels' turns there follow their eased motion piecewise linearly, as they would in a single motion.
Panels that sample one step in different numbers of intervals are sampled in their least common
multiple (at most 1024), which keeps every panel's own samples, when each panel's figures between
its keys answer at the fractions of that multiple (`Motion.stepSamples` carries the number to the
panel). When one does not, the step is drawn unsampled: each morph interpolated directly between its
keys, or crossfaded where it cannot be; that is an error under `.fail` and a note saying so under
`.warn`. Every panel is laid out on the shared timeline (`Motion.planOn`), so every animation
element of the picture has the same timing; the panels are in phase by construction, and the browser
check confirms it at every rest and at three points of every move.

*Common and independent scale.* Side by side, each panel gets a share of the width: the shares given
(`shares`, for a larger right panel), or under the common scale the least widths at which the panels
fit at one scale (found by bisection on the scale), or under independent scales the widths of the
panels' own key figures. Under `PanelScale.common` every panel is drawn at the smallest of the
scales at which each fits its share (`Frame.fit` of its reaches), and centred again at that scale,
so a unit length is as long in every panel; under `PanelScale.independent` each is fitted on its own
(a zoom panel). A panel's reaches are those of its keys and of what its turns sweep
(`Motion.sweptItems`), as for a single motion, so that nothing turns out of it; a panel whose keys
set a view of their own (a zoom) keeps that view, and what turns out of it is an error. The panels
side by side are as tall as the tallest needs, their content centred; stacked, each is as tall as it
needs. Because a panel's view is the union of all its keys (and sweeps), a panel can show empty room
at some keys (the golden picture's right panel is empty along its bottom at key 0 and filled there
at key 2): that is the price of one view through the loop, not slack the layout could trim. The
title band above the panels is the style's panel title size and title gap; a title wider than its
panel is made smaller, down to three quarters of its size (`titleFit`, measured by the style's text
engine), and one still too wide is an error, so titles never run into a neighbour. A gap below zero
(panels overlapping) is an error. A panel is placed by moving the origin of its frame on the page
(`shiftEnv`); nothing is wrapped in a `transform`, so the invariant of the SMIL builders holds for
the whole picture. A line or a ray in a panel is refused, since it is drawn to the edge of the whole
page, not of its panel.

*The narrow rendition.* With `narrowWidth`, `MotionPanels.narrow` is the same picture with its
panels stacked at that width (at one scale if the picture asks for it), checked and written as a
picture of its own.

*Ids and stills.* Every id, reference and `data-pilean-actor` of panel `i` carries the prefix `p{i +
1}-`, and the poster's ids `poster-p{i + 1}-`, so that panels may use the same actor ids; each
panel's moving picture is a group marked `data-pilean-panel`. The report checks that every id of the
document is distinct (`idProblems`). A picture's own prefix (`MotionPanels.idPrefix`, and
`Motion.idPrefix` for a single motion) goes before all of them, so that several pictures can be put
inline in one page; empty by default, which leaves every output as it was. Key `k` of the picture is
the composition of the panels' key-`k` stills (each panel's `Motion.keyFigure`, as laid out, drawn
in its shifted frame) under the titles; each panel's own key figure stays available
(`MotionPanelsReport.panelKeyFigure?`), and `stepRows` lists every step with its kind, duration and
every panel's moves, for a table of steps. A picture's stills carry the same ids as its moving
picture: a page that shows both inline gives them prefixes of their own.

*Checks.* Every check of a motion applies to each panel on the shared timeline and is reported with
the panel's name: arrival and the step rules, the layout checks of its keys, the stacking order, the
rest check of its whole drawing against its stills, its writer against its baker, and that nothing
leaves its panel while it moves (every layer drawn at eight times through every move, every point
within 0.5 px of the panel's box; the same check keeps a single motion inside its picture). Then the
picture's own problems: panels with different numbers of keys, captions that are not one per key,
sampling the panels disagree on, two panels with one title, a gap below zero, a panel whose content
or title does not fit its share, a panel's own step timing, a line or a ray in a panel, panels on
different backgrounds, an id twice in the document, a missing title or text alternative. Last come
the composed picture's rest check against the composed stills and its writer against the composed
baker; these run only for a well-formed picture with no error so far, and otherwise a note says that
the picture was not checked as a whole, so a picture written under `.warn` despite errors says so.
`.fail` is the default, under which `MotionPanels.svg?` and `animation?` give the errors instead of
the picture.

### Outputs of a motion

`PILean/Trust/Motion.lean` makes a motion, or a picture of panels, a figure of the build
(`@[figure illustration]` on a `Plane.Motion` or a `Plane.MotionPanels`). The outputs read a
*checked motion* (`CheckedMotion`), made only from a motion or a picture of panels
(`Motion.checked`, `MotionPanels.checked`, which compute its report; the constructor is private): the animated SVG of the checked route
(`svg?`, never a route that ends in `Unchecked`), the key stills ready-made (`MotionStill`), the
captions, the poster, the cycle, the table of the steps, the check level and the problems.
`ToCheckedMotion` says which report a type is checked by; `motionOutputs` writes the files. For a
motion declared as `d` with `n` keys the files are:

| Suffix | Formats | What it is |
|---|---|---|
| (none) | SVG | the animated SVG; for a page also its body without the file's own reduced-motion `style` and poster group (`MotionData.live`), the stills with their captions and the step table (`Output.motionPage`) |
| `-poster` | PNG, PDF | the poster key's still |
| `-keys` | SVG, PNG, PDF | the contact sheet: the title, then every key's still at its own size in a grid with its caption wrapped below it (`sheetOf`, one drawing, written like a frame of an explorer; its SVG with a `title` and a `desc` listing the captions); for print, PDF and the LeAnTeX path |
| `-key-k` | SVG, PNG | the still of key `k` (from 0): for a motion, byte for byte the files of `Motion.keyFigure k` (through `ExplorerFrame.ofPlane` and `stillOutputs`); for a picture of panels, `keyStillSvg k` and `keyStillPng k` |
| `-narrow`, `-narrow-key-k` | SVG; SVG, PNG | the narrow rendition and its stills: a picture of panels with a `narrowWidth` (stacked panels); a single motion has none |
| (none) | APNG, GIF | the baked frames, only with `MotionFigure.rasters` |

The grid has as many columns as fit in 800 pixels (two stills of 360 pixels), then as few as keep
the number of rows, so the rows are filled evenly; printed across a page of 6.5 inches its
14-pixel captions are about eight points tall. A stopped motion (an error under `fail`; at every
level, a motion that is not well formed, an id written twice, panels with different text engines)
renders none of the files, and gives no inline picture and no page data; a narrow rendition is
also stopped by its own errors. Every output records the motion (keys, cycle, captions, check
level, errors left) in its source record and the manifest (`docs/TRUST.md`, "Motions"). A picture
of panels uses one text engine, so that its stills and its sheet are drawn with it. The dark twin
of a motion, for a site with a dark theme, is the same outputs of `Motion.withStyle d`
(`MotionPanels.withStyle d`) with `d` the dark twin of `Motion.style` (`MotionPanels.style`): the
stills and the sheet are drawn by the same routes in that style, with no drawing code of their
own.

### A motion shown in a page

The Verso adapters (`verso/`, `verso/manual/`) show a motion inline wherever `:::figure` names one
(`PILeanVerso.motionHtml`, `PILeanVerso.motionCss`); nothing of it needs a script.

* **Markup.** A wrapper `div.pilean-motion` with the attribute `data-bp-motion` (what the Verso
  Blueprint motion switch looks for) holds the *stage* and the *stills*. The stage holds the
  moving picture (`MotionData.live`) as an inline `svg.pilean-motion-live` with the figure's text
  alternative as its name and the stills' captions as its description, and, for a picture of
  panels with a narrow rendition, the narrow one's beside it; both are in the page from its load,
  since an `svg` inserted by a script would start a clock of its own. Over them lies the poster
  key's still (`span.pilean-motion-still`, hidden from assistive technology). The stills are an
  ordered list `ol.pilean-motion-keys`: each key's still as a picture of its file (`-key-k`, the
  narrow rendition's `-narrow-key-k` as its source on small screens, and the `-dark` twins that
  follow the page's theme), loaded lazily, with its caption "Step k of N: …". The moving picture
  gets no declaration links: hovering or focusing it shows the still instead, so they could not be
  reached.
* **Ids.** Every id, reference to an id and `data-pilean-actor` of a moving picture gets a prefix
  made from the figure's anchor (`<anchor>-motion-mw-`, and `-mn-` for the narrow rendition), so
  several motions, their renditions and other inline pictures share a page; the stills are
  pictures of files and add no id.
* **Theme.** The moving picture's own `style` element restyles its light colours under the page's
  dark theme (`themeCss`), as for any inline picture; only `transform` and `opacity` are animated,
  so the restyling holds while it moves.
* **What is shown.** Motion on (the default): the moving picture; the stills' captions stay in the
  accessibility tree, visually hidden, their pictures not drawn. Hover (on a device that hovers,
  `@media (hover: hover)`, so a tap on a phone does not leave it stuck) and keyboard focus (the
  stage is a tab stop with a visible focus ring; a tap focuses it too): the poster key's still in
  the picture's own box, so nothing around it moves. Motion off (the root's
  `data-motion="reduce"`, which the Blueprint's switch sets, or the reader's
  `prefers-reduced-motion: reduce`): the stage is hidden and the stills are a grid with their
  captions. Print: the stage is left out and the stills are printed. Without JavaScript the same,
  by the stylesheet alone. Small screens (560 pixels or less, the plane figures' breakpoint): the
  narrow rendition, and the narrow stills.
* **Hiding.** A moving picture that may be shown again is hidden with `visibility: hidden` (and,
  where it must take no space, `position: absolute`), never `display: none`: in Chromium an inline
  SMIL picture shown again after `display: none` stays frozen until its animations next repeat,
  although its clock runs. The hidden rendition and the stage while motion is off are hidden so;
  only print uses `display: none`. The example sites' browser check shows the picture following
  its clock after each of these, and that the check notices `display: none`.
* **Layout.** The stage is as wide as the picture and reserves its box: hover and focus change
  nothing around it, and the hidden rendition takes no space. Turning motion off replaces the
  picture by the taller grid of stills, a change the reader asked for.
* **The figure's page.** Besides the picture and the files (the animated SVGs, the stills, the
  contact sheet with its PDF): the standing (for a linked motion, what a theorem about a motion can
  state, `motionLinkedWords`), `MotionData.words` (with `MotionData.checkWords` for a motion not
  checked strictly), the table of the steps (each step's keys, its duration exactly, and each
  move with its panel, actor and `MotionMoveRow.words`, a crossfade marked), the key stills with
  their captions, always shown, and the contact sheet.
* **The Blueprint.** A motion's caption ends with the Blueprint's link to its switch,
  "Animations can be turned off in the page menu." (`PILeanVerso.motionLinkText`), which the
  Blueprint shows only when its script runs.

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

