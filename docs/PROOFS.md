# What an image proves

A PILean picture can come with a theorem. The theorem is about the Lean object the picture was
drawn from, not about the picture's pixels. This page says, in plain words, what is proved, what
is only tested, and what you still have to trust.

## The idea

Every picture here is the value of a Lean declaration. Four kinds have an exact specification:

| Picture | The Lean object | What the theorem says |
|---|---|---|
| Function plot | an exact function `f : Q → Q`, an interval `[lo, hi]` and a number of steps `n` | the curve goes through exactly the points `(x, f x)` with `x` on the grid `lo + k (hi - lo) / n`, `k = 0, …, n`, in order, and no others |
| Data plot | a list of integer (or exact rational) points | the line or the markers are the list, point for point, in order; none added, none dropped |
| Graph | a list of nodes and a relation on them (or an edge list) | the nodes are exactly the list and the edges exactly the related pairs, each once; the layout draws one route for each edge |
| Animation | a drawing as a function of time, a frame rate | frame `i` is the drawing at the time `i / fps`, as an exact fraction converted to a number |

`Q` is PILean's small exact rational type (`PILean/Exact.lean`): an integer over a positive
natural number. All the theorems about values are statements about exact numbers. A theorem is
stated about the very definition the figure is built from (for instance `provedFunction_spec`
mentions `cubicSeries`, the series that `provedFunction` plots), so changing the figure changes
what is proved, and a figure that no longer satisfies its theorem does not build.

## Where floating point begins

The exact numbers are turned into `Float` in one place, `Q.toFloat` (numerator and denominator
converted and divided). Everything the theorems say about the *data* is before that point. After
it:

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

The position of a point (the axis scale, clamping to the page) and everything after it are
floating-point and tested, not proved.

## What is proved

Every theorem below depends on no axiom beyond Lean's three standard ones (`propext`,
`Classical.choice`, `Quot.sound`); there is no `sorry`, no `native_decide` and no `bv_decide`
anywhere in the library. Each main theorem sits beside an `example` that shows its hypotheses can
be met. The gallery pictures (`examples/README.md`) each carry theirs next to the code in
`PILeanTest/ProvedExamples.lean`.

**Function plots** (`PILean/Exact.lean`, `PILean/Plot/Exact.lean`)

* `Q.grid_length`: the grid has `n + 1` points.
* `Q.gridPoint_equiv`, `Q.gridPoint_zero`, `Q.gridPoint_last`, `Q.gridPoint_succ`: the `k`-th
  point is `lo + k (hi - lo) / n`, the grid starts at `lo`, ends at `hi`, and consecutive points
  differ by `(hi - lo) / n`. (Rationals are compared by `Q.Equiv`, cross multiplication; `Q` is
  not normalised.)
* `Q.mem_samples`, `Q.samples_fst`, `Q.samples_length`: the exact samples are the pairs `(x, f x)`
  with `x` on the grid, their abscissae are the grid in order.
* `Series.ofExact_points`, `Series.ofExact_xs`, `Series.ofExact_ys`, `Series.ofExact_size`: the
  series is the samples converted pointwise.
* `Series.ofExact_draw`: with every converted sample positioned, the drawing is one polyline
  through their page positions (nothing for `n = 0`).

**Data plots**

* `Series.ofIntPoints_points`, `Series.scatterOfIntPoints_points`: the series points are the
  integer list converted pointwise.
* `Series.ofIntPairs_recover`: the exact layer gives the integer list back, so nothing was added,
  dropped or changed.
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

**Animations** (`PILean/Anim/Proofs.lean`)

* `Animation.time_eq_exactTime`: the time handed to the drawing function for frame `i` is the
  conversion of the exact fraction `i / fps`.
* `Animation.frameSeq_getElem`, `Animation.frameTrees_getElem`: frame `i` of the raster frame
  sequence (animated PNG, GIF) and of the animated SVG is the drawing at that time.

## What is tested, not proved

* The rasteriser (coverage, compositing, colour conversion), the PNG, APNG and GIF encoders and
  decoders, the SVG writer: tested against published values, other software and the golden files
  in `examples/`.
* The quality of a graph layout (layers, crossings, coordinates, curves): tested, including
  against Graphviz. Only the *set* of drawn edges is proved, not where they run.
* The floating-point conversion and the page mapping: `Q.toFloat` is the nearest `Float` when
  numerator and denominator have at most 53 significant bits (as in the gallery), and the tests
  check the positions of the gallery's points; that is a check on those pictures, not a theorem.
* The adaptive sampler of `Series.function`, which plots a `Float → Float` function by refining
  where the curve bends and breaking it at poles and jumps. Its guarantee is weaker: it is
  tested (refinement, poles, jumps, undefined regions), not proved. Use `Series.ofExact` when the
  statement "this curve is exactly this function on this grid" matters.
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
