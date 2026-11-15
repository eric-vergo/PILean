# What an image proves

A PILean picture can come with a theorem. The theorem is about the Lean object the picture was
drawn from, not about the picture's pixels. This page says, in plain words, what is proved, what
is only tested, and what you still have to trust.

## The idea

Every picture here is the value of a Lean declaration. Four kinds have an exact specification:

| Picture | The Lean object | What the theorem says |
|---|---|---|
| Function plot | an exact function on the rational numbers, `f : Rat → Rat` (a polynomial or a quotient of polynomials with rational coefficients, or any other Lean function from rationals to rationals), a rational interval `[lo, hi]` and a number of steps `n` | the plotted series has exactly the `n + 1` points `(x, f x)` with `x` on the grid `lo + k (hi - lo) / n`, `k = 0, …, n`, in order and no others, each coordinate converted to a floating-point number |
| Data plot | a list of integer (or exact rational) points | the plotted series has exactly the points of the list, in order, none added or dropped, each coordinate converted to a floating-point number |
| Graph | a list of nodes and a relation on them (or an edge list) | the nodes are exactly the list and the edges exactly the related pairs, each once; the layout has one route for each edge, with that edge's two ends, and the picture draws those routes. Nothing is said about where a node is placed or how a route runs |
| Animation | a drawing as a function of time, a frame rate | frame `i` is the drawing function applied to the exact rational time `i / fps` converted to a floating-point number. Nothing is said about the drawing function itself or about the number of frames |

**Floating point.** Every statement in this table is about exact numbers and lists. The picture
is computed from them in floating-point arithmetic: the conversion of each exact number
(`Exact.toFloat`), the axis scales, the positions on the page, the rasteriser. That part is
tested, not proved, so no theorem here speaks of a pixel ("Where floating point begins" below
says exactly where the line runs).

**Samples, not graphs.** For a function plot the theorem says that the curve is drawn through
exactly these sample points; it does not say that the curve is the graph of `f`. Between two
consecutive samples the picture is a straight segment, and nothing in this library is proved about
the distance from that segment to `f`.

**Which functions.** The theorem is about functions with exact rational values. A plot of `sin`,
`exp` or a square root made with `Series.function`, such as the first example of the README, is
sampled in floating point by an adaptive sampler and has no theorem.

The rational numbers are `Rat`, the type of Lean's core library: a fraction in lowest terms, so
equality of rationals is `=`. All the theorems about values are statements about exact numbers.
A theorem is stated about the very definition the figure is built from (for instance
`provedFunction_spec` mentions `cubicSeries`, the series that `provedFunction` plots), so
changing the figure changes what is proved, and a figure that no longer satisfies its theorem
does not build.

## Where floating point begins

The exact numbers are turned into `Float` in one place, `Exact.toFloat` (the numerator and the
denominator of the fraction in lowest terms, each converted, then divided). Everything the
theorems say about the *data* is before that point. After it:

* The series holds exactly the converted samples, in order: `Series.ofExact_points` and
  `Series.ofIntPoints_points` say the series' point array is the exact list mapped through the
  conversion.
* The drawing code maps each point to the page with `PanelLayout.pos` and breaks the line where a
  point has no position (a value that is not a number, or a non-positive value on a logarithmic
  axis). When every point has a position, `Series.ofExact_draw` and
  `Series.ofSamples_draw` say the picture is one polyline through the page positions of exactly
  those points in order (and `Series.scatterOfSamples_draw`, one marker at each). When some do
  not, `Plot.runs_sublist` and `Plot.runs_length` say what remains: runs of at least two
  consecutive positioned points, in order, and nothing that was not there.

The value of `Exact.toFloat` (how near it is to the rational number), the position of a point
(the axis scale, clamping to the page) and everything after it are floating-point and tested, not
proved.

## What is proved

Every theorem below depends on no axiom beyond Lean's three standard ones (`propext`,
`Classical.choice`, `Quot.sound`); there is no `sorry`, no `native_decide` and no `bv_decide`
anywhere in the library. Each main theorem sits beside an `example` that shows its hypotheses can
be met. The gallery pictures (`examples/README.md`) each carry theirs next to the code in
`PILeanTest/ProvedExamples.lean`.

**Function plots** (`PILean/Exact.lean`, `PILean/Plot/Exact.lean`)

* `Exact.grid_length`: the grid has `n + 1` points.
* `Exact.gridPoint_eq`, `Exact.gridPoint_zero`, `Exact.gridPoint_last`, `Exact.gridPoint_succ`:
  the `k`-th point is `lo + k (hi - lo) / n`, the grid starts at `lo`, ends at `hi`, and
  consecutive points differ by `(hi - lo) / n`. These are equalities of rational numbers.
* `Exact.mem_samples`, `Exact.samples_fst`, `Exact.samples_length`: the exact samples are the
  pairs `(x, f x)` with `x` on the grid, their abscissae are the grid in order.
* `Series.ofExact_points`, `Series.ofExact_xs`, `Series.ofExact_ys`, `Series.ofExact_size`: the
  series is the samples converted pointwise.
* `Series.ofExact_draw`: with every converted sample positioned, the drawing is one polyline
  through their page positions (nothing for `n = 0`).

Not proved: anything about the curve between two samples, and anything about a function that is
not rational-valued.

**Data plots**

* `Series.ofIntPoints_points`, `Series.scatterOfIntPoints_points`: the series points are the
  integer list converted pointwise.
* `Series.ofIntPairs_recover`: the numerators of the exact points are the integer list, so the
  exact layer added, dropped or changed nothing.
* `Series.ofSamples_draw`, `Series.scatterOfSamples_draw`, `drawSeries_line_unmarked`,
  `drawSeries_scatter`: what the drawing does with the points.
* `Plot.polylinesWith_all`, `Plot.runs_map_some`, `Plot.runs_length`, `Plot.runs_sublist`: the
  function that breaks a polyline, which `PanelLayout.polylines` calls.

**Graphs** (`PILean/Graph/Spec.lean`, with the existing `layout_edges_complete` and friends in
`PILean/Graph/Proofs.lean`)

* `Graph.ofRelation_node_labels`: the nodes are the input nodes, in order.
* `Graph.mem_relationPairs`, `Graph.relationPairs_nodup`, `Graph.ofRelation_edge_pairs`: the edges
  are exactly the related pairs, each once, in a fixed order.
* `Graph.layout_edge_endpoints`, `Graph.layout_edges_of_valid`, `Graph.ofRelation_layout_edges`,
  `Graph.ofNames_layout_edges`: the layout has exactly one route per edge, in order, with the
  edge's own ends and index. An edge that spans several layers is routed through dummy nodes
  inside the layout; it is still one route, whose `points` include them.
* `Graph.Layout.draw_edges`: the picture draws the layout's routes.
* `Graph.assignLayers_lt`, `Graph.assignLayers_lt_input`: after cycle removal every edge points
  to a deeper layer. This holds by construction: `assignLayers` ends with a repair pass
  (`fixLayers`) that moves a node down until its incoming edges point down, and the theorem is
  about that pass. Nothing is proved about the layers network simplex and balancing produce
  before it (`layersBeforeRepair`); a test checks, on random graphs, the fixtures and the import
  graphs, that the repair changes nothing there, so the layers you see are the simplex's own.

**Animations** (`PILean/Anim/Proofs.lean`)

* `Animation.exactTime_eq`, `Animation.time_eq_exactTime`: the exact time of frame `i` is the
  rational number `i / fps` (for a positive frame rate), and the time handed to the drawing
  function is its conversion `Exact.toFloat`.
* `Animation.frameSeq_getElem`, `Animation.frameTrees_getElem`: frame `i` of the raster frame
  sequence (animated PNG, GIF) and of the animated SVG is the drawing at that time.

## What is tested, not proved

* The rasteriser (coverage, compositing, colour conversion), the PNG, APNG and GIF encoders and
  decoders, the SVG writer: tested against published values, other software and the golden files
  in `examples/`.
* The quality of a graph layout (layers, crossings, coordinates, curves): tested, including
  against Graphviz. Only the *set* of drawn edges and the downward direction of the layers (by
  the repair pass) are proved, not where the edges run, and not that network simplex finds a
  feasible or optimal layering on its own (`layersBeforeRepair` is tested, see above).
* The floating-point conversion and the page mapping. `Exact.toFloat` divides the numerator by
  the denominator as floating-point numbers; when both have at most 53 significant bits (as in
  the gallery) the two conversions are exact and IEEE 754 division gives the floating-point
  number nearest to the rational. That is an argument about the arithmetic of the machine, not a
  theorem of this library. The tests check values of the conversion (among them fractions with 53
  significant bits, and that a fraction and the same fraction not in lowest terms convert alike)
  and the positions of the gallery's points; that is a check on those pictures.
* The adaptive sampler of `Series.function`, which plots a `Float → Float` function by refining
  where the curve bends and breaking it at poles and jumps. Its guarantee is weaker: it is
  tested (refinement, poles, jumps, undefined regions), not proved. Use `Series.ofExact` when the
  statement "these are exactly the values of this function on this grid" matters.
* `Animation.frameCount`, which rounds the duration times the frame rate as floating-point
  numbers.
* The hypotheses of the drawing theorems on the gallery pictures (every converted point has a
  page position) are checked at run time by `lake test`.

## What is trusted

* **Lean itself**: the kernel that checks the proofs, the compiler and the runtime that execute
  the code (a theorem is about the Lean definition; that the compiled program computes it is
  Lean's responsibility), the standard library, and the three standard axioms.
* **The build**: that the bytes in a file are the ones the build produced from the declaration
  they name. `docs/TRUST.md` describes how this is made checkable (the source record, the
  fingerprint, the manifest, `pilean-build --check` and `pilean-verify`); a theorem is in the same
  module as its picture, so building the module checks it, but a file edited afterwards is only
  detected by those tools.
* **The viewer** that displays the file: a browser, an image program or a printer draws the SVG or
  PNG its own way.
* The reader of the theorem: that the statement says what you mean. The statements are short and
  in plain definitions on purpose, and the `example` beside each one is there to show that they
  are not empty.

## How to read a picture's guarantee

1. Find its source record (`lake exe pilean-info FILE`): the module, declaration and line.
2. Read the theorem beside the declaration. It names the exact function, list, relation or time.
3. Run `lake build` on that module; the theorem checks.
4. For the part after floating point begins, the tests and `docs/TRUST.md` say what is compared.
