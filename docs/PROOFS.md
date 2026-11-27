# What an image proves

A PILean picture can come with a theorem. The theorem is about the Lean object the picture was
drawn from, not about the picture's pixels. This page says, in plain words, what is proved, what
is only tested, and what you still have to trust.

## The idea

Every picture here is the value of a Lean declaration. Six kinds have an exact specification:

| Picture | The Lean object | What the theorem says |
|---|---|---|
| Function plot | an exact function on the rational numbers, `f : Rat → Rat` (a polynomial or a quotient of polynomials with rational coefficients, or any other Lean function from rationals to rationals), a rational interval `[lo, hi]` and a number of steps `n` | the plotted series has exactly the `n + 1` points `(x, f x)` with `x` on the grid `lo + k (hi - lo) / n`, `k = 0, …, n`, in order and no others, each coordinate converted to a floating-point number |
| Data plot | a list of integer (or exact rational) points | the plotted series has exactly the points of the list, in order, none added or dropped, each coordinate converted to a floating-point number |
| Graph | a list of nodes and a relation on them (or an edge list) | the nodes are exactly the list and the edges exactly the related pairs, each once; the layout has one route for each edge, with that edge's two ends, and the picture draws those routes. Nothing is said about where a node is placed or how a route runs |
| Animation | a drawing as a function of time, a frame rate | frame `i` is the drawing function applied to the exact rational time `i / fps` converted to a floating-point number. Nothing is said about the drawing function itself or about the number of frames |
| Combinatorial diagram (`PILean.Diagram`) | plain finite data: a relation on `Fin n` (a graph, a digraph, an order), row lengths (a Young diagram) or a filling (a tableau), a permutation in one-line notation, parent links (a forest, a binary tree), a list of sets, a list of integer steps (a lattice path), a list of cells (a polyomino) | the marks the diagram draws, read back from it, are exactly the parts of the data, in a fixed order, each at the exact rational position the layout gives it: the edges are exactly the related pairs (for an order, exactly the covers, whose transitive closure is the strict order of a partial order), the cells exactly `(i, j)` with `j < λᵢ`, the written entries exactly the filling, the crossing strands of a wiring diagram exactly the inversions, an element written in a Venn diagram inside circle `s` exactly when it belongs to set `s`. Nothing is said about how the marks look: text, the conversion to floating point, the frame, colours, style and pixels |
| Plane figure of exact points | points of a type with rational enclosures (`Exact.PlanePoint`: rationals, integers, or an algebraic representation such as ℤ[ζ₅] by integer coefficients) | each exact point is drawn as a marker centred at the frame's image of its conversion (the centre of its ball at 64 bits, converted by `Exact.toFloat`), a segment between the images of its ends; a figure of points draws one marker per point, in order. A figure's specification can also write out its items, labels included, with their colours, titles and recorded incidences, with the incidences decided by exact arithmetic in the representation. A rational point is its own ball. That the ball of another representation holds its value is declared by its instance, not proved (the core has no real numbers); the frame's fitting is floating point |

**Floating point.** Every statement in this table is about exact numbers and lists. The picture
is computed from them in floating-point arithmetic: the conversion of each exact number
(`Exact.toFloat`), the axis scales, the positions on the page, the rasteriser. That part is
tested, not proved, so no theorem here speaks of a pixel ("Where floating point begins" below
says exactly where the line runs).

**Samples, not graphs.** For a function plot the theorem says that the curve is drawn through
exactly these sample points (converted to floating point); it does not say that the curve is the
graph of `f`. Between two consecutive samples the picture is a straight segment, and nothing in
the core library is proved about the distance from that segment to `f`. The optional package
`pilean-mathlib` proves such a bound over the real numbers, for the exact samples ("Plots against
the real numbers" below).

**Which functions.** The theorem is about functions with exact rational values. A plot of `sin`,
`exp` or a square root made with `Series.function`, such as the first example of the README, is
sampled in floating point by an adaptive sampler and has no theorem. (The package
`pilean-mathlib` has a plot of the sine with one: it plots a polynomial with rational
coefficients and bounds the distance from the polyline through its exact samples to the real
sine.)

The rational numbers are `Rat`, the type of Lean's core library: a fraction in lowest terms, so
equality of rationals is `=`. All the theorems about values are statements about exact numbers.
The theorem of a gallery picture that has one names the picture: `provedFunction_spec` begins by
saying that the series of the figure `provedFunction` are `cubicSeries` and `parabolaSeries` and
no other, and then says what the points of those series are. So changing what the theorem states
of the figure breaks its proof, and a figure that no longer satisfies its theorem does not build.
Every theorem linked to a figure of the gallery and of the examples begins by writing the whole
figure out, so nothing of the figure's value can change without breaking it ("What a gallery
theorem pins" below).

Many of these theorems are short: the series constructors are defined to hold the converted
samples, so `Series.ofExact_points` holds by unfolding the definition. They are stated as theorems
so that the specification of a picture can be read without reading the code, and so that a
change to the code that broke it would be caught.

## What a gallery theorem pins

`figure_links` checks names only: a theorem that names its figure and says little of it is still
linked. The gallery's and the examples' theorems say more, and a check makes sure of it. Each one
begins with the figure written out, `fig = …`, followed by every definition of the gallery's own
modules that the written-out figure uses, `c = …` or `∀ x, c x = …`, then every definition those
use, and so on, until what is left are definitions of the libraries (PILean, LeAnTeX, Mathlib, Lean).
`#assert_figures_pinned A B …` (`PILean/Trust/Attr.lean`, `figurePinProblem?`) checks this for
every theorem linked to a figure declared in a module whose name starts with `A`, `B`, …: it
walks the links of the environment, not a list of names, finds the equations among the
statement's conjuncts (under its leading quantifiers), and fails if one of those definitions has
none, if an equation's right-hand side mentions a variable of the statement, or if equations lead
back to the definition they give. Each package runs it in its build: the core's test modules
(`PILeanTest/Axioms.lean`), the Mathlib package (`PILeanMathlib/Axioms.lean`, with the core's
figures it states again in Mathlib's terms), the LeAnTeX package's test driver, the Verso example
and the Verso manual example (their test modules), and the manual (`manual/Main.lean`).

What this guarantees: each such theorem being proved, its figure is equal to a term built from the
libraries' definitions alone, and the statement writes that term out. Any change to a definition
of the gallery's modules that changes the figure's value, in any field, makes the statement false,
and the theorem does not build. For each kind of figure the fields a reader sees are therefore all
pinned:

| Kind | Fields a reader sees | Pinned |
|---|---|---|
| Plot (`Plot.Figure`) | title, accessible description, width, height, each panel's axis names, scales, domains and ticks, each series' name (the legend's text), points, line, dash, marker and colour role | all |
| Plane figure (`Plane.Figure`) | title and description, width, narrow width, padding, view, the style set by the figure (such as the reference figure's house style: its widths, marker sizes and role colours), every item with its exact data, colour or role, title, description, width, marker, dash, fill and recorded incidences, every label with its text, point, placement, colour and size | all |
| Diagram (`Diagram.Diagram`, the combinatorial, algebraic and number-theoretic kinds) | title, description, width, every mark (part, exact shape, text, colour role), and through the data the names of vertices, objects, arrows, sets, sequences, cells and headings | all |
| Graph (`Graph`) | the node labels, the edges | all |
| Animation (`Animation`) | width, height, frame rate, duration, loops, the drawing at every time (so every frame's content: the shapes, their colours, sizes and positions), the text engine | all |
| Motion (`Plane.Motion`) | title and description, captions, poster, every key figure in full (as for a plane figure), every step's moves (the actor, the kind, a turn's centre and exact fraction, a slide's vector), each step's duration and easing, the pacing, the check level; not the frames the browser draws between the keys, which no statement can name | all |
| Picture of panels (`Plane.MotionPanels`) | as a motion, for each panel with its title, and the picture's captions, timing, arrangement, scale, width and narrow width | all |
| Explorer (`Explorer`) | the parameters' names, values and the labels the slider writes, the frame at every point of the grid (each frame's figure in full), the poster | all |

Nothing of a gallery figure is left unpinned on purpose. What no theorem states, by design, is
the libraries' own code, which the written-out figure names: how the builders and modifiers make
marks and items, the colour values of the library's styles (`Style.light`, `Style.dark` and the
roles' defaults), the lettering and LeAnTeX's typesetting, the layouts, and the drawing in
floating point down to the pixels. A change there can change a picture without breaking a
gallery theorem; it is tested (the goldens in `examples/`, compared byte for byte by `lake test`),
not proved.

What it does not guarantee: that the statement says what its reader expects; the equations tie the
statement to the figure, and the other conjuncts say what the figure means, which is still the
reader's to judge. The check sorts definitions by module: a definition of a module outside the
named prefixes counts as library code. A recursive definition cannot be written out by an
equation that mentions it, so the gallery gives such definitions in a closed form proved equal
to them (the logarithm's and the arctangent's partial sums as finite sums, the integer square
root's bisection as an iteration, the harmonic numbers as Mathlib's `harmonic`, the triangular
numbers as `n (n + 1) / 2`) or by their values (the Collatz stopping times). `figure_links` does
not require any of this of a project's own figures; the command is there for a project that
wants it. The five figures of `PILeanTest/Standing.lean` and three of the Verso manual example
are linked to empty statements on purpose, to show what a link does not say, and are left out of
the check.

`lake test` compiles changed copies of the gallery's modules for these fields as well (what the
clock's frames draw, a series' name, an axis's name, a width, an accessible description, the
house style's marker size, a narrow width, a layout's radius, a title; in the Mathlib package
the sine's legend and axis and the Petersen graph's width and layout; in the LeAnTeX package the
figure's width and title) and requires each to fail inside its theorem
(`PILeanTest/SpecMutations.lean`, `visibleMutations`; `PILeanMathlibTest/Mutations.lean`;
`PILeanLeAnTeXTest/Main.lean`).

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
  positioned points, in order, and nothing that was not there. (That a run is a stretch of
  consecutive points, and which points are left out, follows from the definition of `Plot.runs`
  and is tested, not stated by these theorems.)

The value of `Exact.toFloat` (how near it is to the rational number), the position of a point
(the axis scale, clamping to the page) and everything after it are floating-point and tested, not
proved.

## What is proved

Every theorem below depends on no axiom beyond Lean's three standard ones (`propext`,
`Classical.choice`, `Quot.sound`); there is no `sorry`, no `native_decide` and no `bv_decide`
anywhere in the library. The build of the tests checks this for every declaration of the library
and of the test modules the test driver imports, of every kind (theorems, definitions, opaque
constants, inductive types with their constructors and recursors), without a list of names, and
reports any `axiom` they declare, used or not (`PILeanTest/Axioms.lean`); every `lake test`
checks that no file of the library is left out of that check and that every test module in the
test driver's imported environment is in it. The check reads the axioms Lean records for each
declaration of an environment that it trusts: it does not check the declarations again in the
kernel. Each main theorem sits
beside an `example` that shows its hypotheses can be met. The gallery pictures that have a theorem
(`examples/README.md`) carry it next to the code in `PILeanTest/ProvedExamples.lean`.

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
  graphs, that the repair did not change the balanced layers there, so on those graphs the layers
  you see are those of network simplex followed by balancing. Least total edge span is the
  objective of network simplex, reached when it finishes within its work budget (`layerWork`);
  nothing checks that it was reached.
* `Graph.assignNested_lt`, `Graph.assignWide_lt`: the same for the two other layerings the layout
  calls: of a graph with clusters, layered from the inside out (every edge between two different
  nodes points, from the node that comes first in the order `assignNested` returns, to a deeper
  layer), and of a graph whose wide layers are split into rows. Both hold by the same repair
  pass; that the pass changes nothing after them, so that a cluster keeps its block of layers,
  is tested, not proved.
* Not proved: the routes of the edges (`Graph/Route`): that a route passes every gate and is the
  shortest, that the curve stays in its zones and that no edge turns back across the layers are
  checked on random cases and on every measured graph, each check with a planted fault it must
  report (`PILeanTest/GraphRoutes.lean`). The coordinates are floating point.
* Not proved: the crossing reduction's sifting and seeded starts, the packing of components
  (`Graph.layoutPacked`), `Layout.mirror` and the SVG for web pages (`Layout.toWebSvg`). They are
  tested (`PILeanTest/GraphOrder.lean`), not proved; that every edge of the input has one route
  is proved for `Graph.layout` only.

**Animations** (`PILean/Anim/Proofs.lean`)

* `Animation.exactTime_eq`, `Animation.time_eq_exactTime`: the exact time of frame `i` is the
  rational number `i / fps` (for a positive frame rate), and the time handed to the drawing
  function is its conversion `Exact.toFloat`.
* `Animation.frameSeq_getElem`, `Animation.frameTrees_getElem`: frame `i` of the raster frame
  sequence (animated PNG, GIF) and of the animated SVG is the drawing at that time.

**Timelines** (`PILean/Anim/TimelineProofs.lean`), for every list of steps and every pacing
(`Timeline.build steps p`, with `steps.size + 1` key frames):

* `build_kinds_cut`, `build_kinds_crossfade`: the segments are, in order, the rest on key `0`,
  then for each step `j` the move of step `j` and the rest on key `j + 1`, with the fade in first
  and the fade out last under a crossfade; `build_size_cut`, `build_size_crossfade`: so there are
  `2 n - 1` segments for `n` key frames under a cut and `2 n + 1` under a crossfade.
* `build_segment_spec`, `build_move_spec`, `build_rest_spec`, `build_seam_spec`: the move of step
  `j` lasts as long as step `j` and has its easing; the rest on key `k` lasts `Pacing.restOf k`
  (`restOf_own`: a key's own rest in `Pacing.holds`, for the first and the last key too;
  `restOf_default`: otherwise `firstHold` on key `0`, `lastHold` on the last key, any other rest
  `hold`); the fades exist only under a crossfade `d` and last `d / 2` each; rests and fades are
  not eased (a negative duration counts as zero).
* `build_start_zero`, `build_start_succ`, `build_stop_last`, `build_dur_nonneg`: the segments
  tile the cycle: the first starts at `0`, each starts where the one before it ends, the last ends
  at the end of the cycle, and no duration is negative (a negative one given counts as zero).
* `keyTimes_size`, `keyTimes_zero`, `keyTimes_last`, `keyTimes_mono`: the key times (the
  boundaries as fractions of the cycle) are one more than the segments, start at `0`, never
  decrease, and end at `1` when the cycle is longer than zero, which it is when the first rest is
  (`build_cycle_pos`).
* `divide_tiles`, `divide_dur_nonneg`: divided into parts (`Timeline.divide`, for a step sampled
  for a morph and for a step or a rest cut at the ends of its fades' windows), each list of parts
  ending at `1`, the segments still tile the cycle (`Tiles`: the first starts at `0`, each starts
  where the one before it ends, the last ends at the end of the cycle), and when the parts' ends do
  not decrease from `0`, no part lasts less than zero (`tiles_layout`, `tiles_partsFrom`,
  `tiles_divide`, `tiles_flatMap`, `partsFrom_dur_nonneg` are the steps).
* `wrap_mem`, `segmentAt_mem`, `progress_mem`, `locate_fst`: any rational time, brought into a
  cycle longer than zero, lies in `[0, cycle)` and in the segment `segmentAt` names (from its
  start, inclusive, to its end, exclusive), and the progress through that segment is in `[0, 1)`.

What the SMIL builders write (`PILean/Anim/SmilProofs.lean`), for the same timelines:

* `times_size`, `times_mono`, `times_zero`, `times_last`, `times_mem`, `times_strict`: the key
  times written (`Smil.times`, the timeline's key times spread by the gap) are one more than the
  segments and never decrease; when the cycle is longer than zero they start at `0`, end at `1`,
  lie in `[0, 1]`, and with a gap above zero each is more than the one before it.
* `keyValues_size`, `seamLevels_size`, `track_counts`: every track has as many values as key times
  and one easing (`keySplines` entry) fewer.
* `track_splines`, `track_splines_move`, `track_splines_still`: interval `i` has the easing of
  segment `i`: the step's own for a move, the identity for a rest and for a fade.
* `seamLevels_crossfade`: under a crossfade the motion layer's opacity is `0` at the first and the
  last boundary.

These stop before the conversion to text: that `fmtNum` of the converted key times keeps their
order is tested, not proved.

For one key frame (no steps) the timeline is the rest on key `0` (between the fade in and out under
a crossfade); there are no timelines of zero key frames. When every duration is zero the cycle is
zero, every key time is `0`, and the statements that need a cycle longer than zero do not apply.
These are equalities and inequalities of rational numbers; the eased progress (`Easing.eval`,
`Timeline.locate`'s second part) is floating point and tested.

**Motions of plane figures** (`PILean/Plane/Motion.lean`, `MotionPlan.lean`, `MotionOutput.lean`)

* `MotionPlan.anim_eq`: every animation element `MotionPlan.anim` builds is its name, its own
  attributes, its values, then `Smil.smilTiming` of the plan's timeline: its timing depends on
  nothing else. The writer builds every animation element through `anim` (the chains, the
  counter-rotations, the opacities, the morphs' path data, the seam); that is how it is written,
  not a theorem, and `lake test` checks the one clock of every output (`Smil.clockProblem?`).
* `MotionPlan.chainNodes_push`, `chainNodes_empty`: the link added last to a chain is its
  outermost group (the earliest link is innermost, which turns about page points require).
* `MotionVersion.steps_links`, `MotionVersion.mem_links`, `linkOf_step`: a layer's links are the
  links (`linkOf`) of its declared turns and slides, in strictly increasing order of their steps.
* `linkOf_turn`: the angle the writer turns a link by, for a turn by `q` of a full turn, is
  `Exact.toFloat (-(360 * q))` (counterclockwise in the figure is clockwise in SVG's measure).
* `Motion.keyAngle_eq`: `Motion.keyAngle`, a function of the model that the writer does not call,
  is minus 360 times the exact sum of an actor's turns before key `k`. The writer's angles at the
  keys are sums of the per-link angles in floating point, rounded as written; they are tested.
* `Motion.timeline_keys`: the timeline of a well-formed motion (`Motion.WellFormed`: one key more
  than steps, a caption per key, the poster among the keys; decidable, and decided by
  `Motion.problems`) has as many key frames as the motion.

What pins what, for motions (everything below the exact keys is floating point and checked, not
proved):

1. *Exact keys → stills.* A still (`Motion.keyFigure k`) is key `k` drawn by the plane figures'
   pipeline in the motion's one view; the goldens' stills are byte for byte the keys drawn in that
   view (tested).
2. *Baker ↔ stills, at every rest, every element.* `Motion.restProblems`, part of
   `Motion.problems` for every motion an author writes: the whole baked drawing at the middle of
   each key's rest is the still: the same paints in the same order, every path within 0.05 px
   (Hausdorff's distance between the outlines flattened to 0.01 px) plus `5.5e-4 r` for a path of
   half-width `r` (two cubic approximations of one circle of radius `r` differ by at most that),
   every text within 0.05 px and turned by at most `1e-4` radians. It bounds what the per-step
   arrival tolerance (0.01 px) adds up to along a chain. It compares outlines, not the phase of a
   dash pattern: a dashed circle turned about its own centre passes while its dashes move.
3. *Writer ↔ baker, by the evaluator.* `Motion.writerProblems`, part of `Motion.problems` for
   every motion: at the middle of every rest and every move, `Smil.valueAt` over the written
   moving picture finds as many actors and upright groups as the plan declares, each anchor,
   opacity and whole transform where the baker has it, within `1e-6`; this checks the
   counter-rotations, which the baker does not read. The tests do the same at 50 times for the
   goldens and fixtures. The baker uses the numbers as the SVG writes them, so this comparison
   alone would not catch a wrong value shared by both; that is what 2 and 4 are for.
4. *Baker ↔ the model computed apart from the plan* (tests): each actor's anchor from its key and
   the declared moves at the exact timeline's eased fraction, within `1e-3` px, at 50 times
   (outside sampled morph steps, whose turns follow the eased motion within `1 / n` of their
   angle, also tested).
5. *Browser ↔ stills, by positions and pixels* (`tools/motion-browser-check.py`, outside `lake
   test`): at every rest every actor is at the still's position and every label's or marker's
   anchor where the plan draws it (0.05 px), and the picture is the still up to antialiasing
   (every channel of every pixel within the range of the other picture's pixels at most one pixel
   away, widened by 40: a moved label shows from about 2 px); turns follow true arcs at the eased
   angle; labels stay upright and are all there.

The arrival check (`Motion.problems`, within 0.01 px) compares the actor in key `k`, carried by
the declared move, with the actor in key `k + 1`; it does not determine a turn's direction or
number of revolutions, nor see moves that leave the drawing alike (see
[`DESIGN.md`](DESIGN.md)).

**Motions as panels of one picture** (`PILean/Plane/MotionPanels.lean`)

* `Motion.planOn_timeline`: a motion laid out on a timeline (`Motion.planOn`) has that timeline;
  `Motion.planIn` is `planOn` on the motion's own timeline.
* `MotionPanels.timelineOf_keys`, `MotionPanelsReport.timeline_keys`: the picture's shared
  timeline has one key more than the picture has steps; `MotionPanels.timelineOf_keys_panel`: for
  a well-formed picture (`MotionPanels.WellFormed`: a panel, every panel with the picture's number
  of keys and one step fewer, a caption per key, the poster among the keys, the timing of no step
  or of every step; decidable, and decided by `MotionPanels.problems`) as many as every panel.
* `MotionPanels.report_timeline`: every panel's two plans, on its own
  page (for its checks) and on the picture's page (for the SVG and the baker), are laid out on the
  shared timeline. With `MotionPlan.anim_eq` this gives `MotionPanelsReport.panel_anim_eq`: every
  animation element a panel's plan builds has `Smil.smilTiming` of the shared timeline. The
  picture's writer builds every animation element through a panel's plan's `anim` (each panel's
  moving picture, and the seam through the first panel's); that is how it is written, not a
  theorem, and the tests check `Smil.clockProblem?` on the whole root of every output.
* `panelPrefix_append_ne`: an id prefixed for panel `i` (`p{i + 1}-`) is never an id prefixed for
  another panel, whatever the two ids were. That the ids within one panel are unique is the
  motion's own matter (two actors with one id in a key are an error), and the report checks at
  run time that every id of the document is distinct (`MotionPanelsReport.idProblems`), so the
  guarantee does not rest on the prefixes alone.

What is tested, not proved, for pictures of panels: the layout (the common scale gives a unit
segment the same length in every panel within `1e-9` px; shares; titles made smaller to fit their
panel, or refused; the narrow rendition stacked at its width); the step kinds and durations of the
shared timeline, and sampling shared in the least common multiple or refused with what is drawn;
that the composed stills are, byte for byte, the panels' key figures drawn in their shifted frames,
and each panel's part of them is its own still translated to its place (`1e-9` px); every per-panel
check of `Motion.problems` (arrival, layout of the keys, stacking, the rest check, writer against
baker and nothing leaving the panel while it moves, on the shared timeline), labelled with the
panel, and the picture's own problems; the composed picture's rest check and writer against baker
(`MotionPanelsReport.restProblems`, `writerProblems`, part of `MotionPanels.problems`). Those two
composed checks run only for a well-formed picture with no other error; otherwise a note says the
picture was not checked as a whole, and under `.warn` such a picture is written with that note. In
Chromium (`tools/motion-browser-check.py`): each panel's part of every rest against the composed
still; every actor of every panel where the composed baker has it at every rest and at a quarter, a
half and three quarters of every move, at one clock time (the panels are in phase); and at 60 times
through the cycle each panel's moving picture, shown alone, inside its own box and the titles'
band. That a turn's swept extent is inside the view (`Motion.sweptItems`: the turned drawing at 96
steps a full turn and wherever a point of it is farthest on its circle) is tested on a point turned
half a turn about a far centre, alone and as a panel; the check that nothing leaves the picture
(`boundsProblems`, eight times per move, 0.5 px) catches a turn out of a view the keys set.

**Plane figures** (`PILean/Exact/Plane.lean`, `PILean/Exact/Spec.lean`, `PILean/Plane/Draw.lean`)

* `Exact.PlanePoint.re_ratPair`, `im_ratPair`, `toPoint_ratPair`, `toPoint_intPair`,
  `RealValue.toFloat_rat`: a rational (integer) point is its own ball, of radius 0, at every
  precision, and is drawn at its coordinates converted by `Exact.toFloat`; the instances for
  `Rat`, `Int` and their pairs satisfy `LawfulRealValue` and `LawfulPlanePoint`.
* `Plane.Figure.draw_eq`: the drawing is the background, then each item's shapes in order.
* `Plane.drawGeom_point`, `Plane.drawGeom_segment`, `Plane.Env.marker_centred`,
  `Plane.drawItem_shape`: a point is drawn as filled circles centred at the frame's image of it, a
  segment as the polyline between the images of its ends.
* `Plane.Exact.point_draw`, `point_draw_default`, `segment_draw`, `points_draw`,
  `figure_points_draw`, `pointNearDisk_eq`, `Plane.drawItem_point`: the same for exact points
  through `PlanePoint.toPoint`; a figure whose items are exact points draws, after its background,
  one marker at the image of each, in order. `Plane.Exact.DrawsExactPoints` and
  `drawsExactPoints` state this for a figure, ready for `figure_links`.
* `Plane.Figure.autoPlaced_of_noAuto`: a figure without automatically placed labels is drawn as
  it is (the outputs draw `autoPlaced`).
* `Plane.Exact.IsPoint`, `IsDisk`, `IsSegment`, `IsRegion` say what an item is, for lemmas
  about items: an item is the point `p` (a point item at the conversion of `p`) in a given tone
  with exactly the given recorded incidences, or the disk, segment or region of disks of given
  exact data in a given tone with a given title (the name a recorded incidence refers to).
  `Plane.Exact.IsPoint.draw`: such a point is drawn as a marker in that tone at the frame's image
  of the conversion of `p`.
* The gallery's two disks (`PILeanTest/Examples.lean`, `disks_spec`), the house-style reference
  figure (`PILeanTest/PlaneExact.lean`, `reference_spec`), the gallery's `zetaSteps`
  (`PILeanTest/PlaneExact.lean`, `zetaSteps_spec`) and the LeAnTeX example
  (`leantex/PILeanLeAnTeX/Examples.lean`, `planeDisks_spec`) each write out the figure's item
  list in drawing order, proved by `rfl`: every item as the builder and modifiers that make it,
  so with its exact data, its colour (accent, role, `faint` or the ink), its title, its width,
  marker, dash and fill where it sets them, the incidences it records, and every label with its
  text, the point it is attached to, its placement and its colour; and the exact data
  themselves (`E = ζ - ζ²`, the centres, the radius `√(3 + φ)`). `lake test` checks that this
  pins the figure: for each of these figures it compiles copies of the module with one change to
  the figure's definitions (an item removed, a point moved, a label moved or its text changed,
  two colours swapped, a radius or a marker changed, a recorded incidence dropped, two items
  reordered) and requires each copy to fail inside the specification and nowhere else
  (`PILeanTest/SpecMutations.lean`, and the LeAnTeX driver for its figure). Each also states, as
  equalities and comparisons in ℚ(√5) computed from ℤ[ζ₅] (`Zeta5.normSq`, `QSqrt.lt`), that the
  records hold: for `E = ζ - ζ²`,
  `|E + 1|² = 3 + φ` and `|E - 1|² < 3 + φ` (`E` on the left circle, inside the right disk, so on
  the lens's boundary), the same for `-E` with the sides exchanged, `|ζ - ζ⁴ ± 1|² = 3 + φ` (the
  circles cross at `±(ζ - ζ⁴)`); the reference figure adds that `φ⁻¹ = ζ + ζ⁴` is real and
  between 0 and 1, so the piece from `-φ⁻³ E` to `E` passes through `0`; `zetaSteps_spec` states
  which steps `ζʲ` lie in the window (decided in ℚ(√5)), which is why they are in accent 0, and
  what each point records (`diskIncidence?`). These are statements about the representation:
  that `Zeta5.normSq z` is `|z|²` for the complex number `z` denotes (`ζ = e^{2πi/5}`) is what
  the code computes, checked in floating point by the tests (`PILeanTest/FigureChecks.lean`),
  not a theorem. `QSqrt.lt`, `le`, `nonneg` and the equality of `QSqrt d` compare the pairs
  `(a, b)`; they are the order and the equality of the real numbers `a + b √d` exactly when
  `√d` is irrational, that is when `d` is not the square of a natural number, and they require
  that (`[QSqrt.NonSquare d]`, an instance for 2, 3 and 5, for another `d` by `decide +kernel`),
  so for a square `d` (0, 1, 4, 9, …) they cannot be used, and `d` is a natural number, so it is
  never negative. That this comparison of pairs is the real order for a non-square `d` is the
  classical fact that `√d` is then irrational, used here, not proved in the core.
* What the plane specifications do not pin: how the builders and modifiers draw (the library's
  code; `Plane.drawItem_point`, `Plane.Exact.IsPoint.draw` and the theorems above for points and
  segments), the colour values of the library's styles, the fitting of the frame, the label
  placement for `auto`, the fonts and lettering (LeAnTeX's typesetting for its example), the
  rendering to SVG and the pixels. The figure's own fields (width, narrow width, padding, view,
  title, description, the style it sets) are written out ("What a gallery theorem pins").
* Not proved: the fitting of the frame, label placement, the layout checks (among them the
  numerical check of each recorded incidence against the element it names), arcs and regions,
  and the rasteriser (tested); that the balls of ℚ(√d), ℤ[ζ₅], square roots and the constructions
  of `PILean.Exact.Algebraic` hold their values (checked exactly by squaring, or against values
  known in closed form, in the tests: `PILeanTest/Enclosures.lean`). The constructions read a
  radius as given: a radius not decided to be positive is no circle (`Meeting.degenerate`,
  `diskIncidence?` gives `none`), and a figure element with a radius that is zero, negative or
  not finite is drawn as nothing and reported (`degenerate`); a negative radius is never read as
  its absolute value.

**Combinatorial diagrams** (`PILean/Diagram/*.lean`; the gallery's figures with their
specifications in `PILeanTest/Diagrams.lean`)

A `Diagram` is a list of marks, each an exact shape (rational coordinates) tagged with the part
of the object it depicts (`Part`: vertex, edge, cell, entry, strand, set, member, step). Each kind
has a decidable predicate `Faithful` that reads the diagram back (`Diagram.edges`, `vertices`,
`cells`, `entries`, `strands`, `steps`, `members`, `texts`, `decorations`) and compares it with
the data as full lists, and mark by mark with the layout, and leaves no mark unaccounted for: a
mark of a part the data does not call for, a text the data does not write, or a decoration (a
`guide` or `note`) beyond the kind's own is refused. The colour role of a mark (`Ink`) is compared
where it carries meaning (a marked vertex's dot, every mark of a commutative diagram, a cell of a
Cayley table, an edge of a Cayley graph); the colour a role has (its RGB value in a style) is not
part of any theorem; the theorems below say that the builders satisfy it for every
input within the kind's cap (`builder_faithful` takes the cap as its hypothesis; beyond it the
figure is a note, and nothing is drawn).

* `Diagram.toPlane_items`: the plane figure's items are the marks' items, in order (each built
  from the mark's exact points by the builders of `PILean.Exact.Plane`, so the theorems of plane
  figures about exact points apply to them).
* Graphs: `FinGraph.mem_edgePairs` (a pair `(i, j)` is drawn exactly when `i, j < n` and the pair
  is drawn by the relation: `adj i j` for a directed graph, `i ≤ j` and `adj i j ∨ adj j i` for
  an undirected one), `FinGraph.edgePairs_nodup`, `FinGraph.draw_faithful` (at every layout the
  drawn edges are `edgePairs` in order, the vertex dots `0, …, n - 1`, each dot, name and edge at
  the layout's positions in its colour role (dots by their mark, names in the ink, edges faint), a loop a circle through its vertex), `FinGraph.toGraph_layout_edges`
  (the layered layout of `PILean.Graph` has one route per drawn pair).
* Hasse diagrams: `FinPoset.mem_coverPairs` (an edge is drawn exactly when it is a cover:
  `i < j` and nothing strictly between), `FinPoset.draw_faithful`, and
  `FinPoset.transGen_covers_iff` (for a partial order, `i < j` exactly when a chain of drawn edges
  leads from `i` to `j`).
* Young diagrams and tableaux: `mem_cellList` (cell `(i, j)` is drawn exactly when `j < λᵢ`),
  `cellList_nodup`, `YoungShape.draw_faithful` and `Tableau.draw_faithful` (the drawn cells, in
  order, each the unit square of its convention, English or French; the written entries are the
  filling, cell by cell, each at its cell's centre).
* Permutations: `FinPerm.oneLine_faithful`, `twoLine_faithful`, `matrix_faithful` (the marked
  cells are exactly `(i, σ i)`), `cycles_faithful` and `mem_cycles_edges` (an arrow `i → j` is
  drawn exactly when `σ i = j`), `wiring_faithful` and `wiring_crossings` (the pairs of strands
  that cross, decided from their drawn ends, are exactly the inversions, in order;
  `wiring_crossings_length`: as many crossings as inversions), `mem_inversions`.
* Trees: `Forest.draw_faithful`, `Forest.mem_edges` (an edge `(p, c)` is drawn exactly when `p`
  is the parent of `c`), `BinTree.builder_faithful`.
* Set systems: `slots_correct` (each place of each region of the Venn diagrams of one, two and
  three sets is inside exactly the circles of its region, decided by the kernel in rational
  arithmetic), `SetSystem.venn_faithful`, `SetSystem.venn_inside` (the name of every element is
  written at a point inside the circle of set `s` exactly when the element belongs to `s`),
  `SetSystem.incidence_edges`.
* Lattice paths and boards: `LatticePath.draw_faithful` (step `k` is drawn from point `k` to point
  `k + 1`), `LatticePath.point_succ` (point `k + 1` is point `k` plus step `k`),
  `LatticePath.ofDyck_step_rises`, `Polyomino.draw_faithful`.
* The gallery's fourteen diagrams (`PILeanTest/Diagrams.lean`) each have a specification that
  writes out the drawn parts in full (the fifteen edges of the Petersen graph, the twelve covers
  of the Boolean lattice, the cells, the entries, the six inversions, the regions of the twelve
  numbers, the 21 incidences of the Fano plane, the points of the Dyck path), checked by the
  kernel, and `figure_links` links it to the figure. `lake test` compiles copies of the module
  with a datum changed and requires each to fail inside the specification
  (`PILeanTest/SpecMutations.lean`), and plants faults in the drawn diagrams (a mark dropped,
  added, moved or relabelled) that each kind's `Faithful` must refuse.
* Not proved: the layouts' qualities (that a Hasse edge goes up the page, that the tidy layout
  keeps siblings apart and centres each parent, that the points of `Layout.circular` are near the
  equal angles; the points are exactly on the circle, which is tested), and everything after the
  exact marks (the floating-point conversion, the frame, text, colours, the rasteriser), as for
  every plane figure.

**Diagrams of algebra** (`PILean/Diagram/CommDiagram.lean`, `Group.lean`, `Quiver.lean`; the
gallery's figures with their specifications in `PILeanTest/AlgebraDiagrams.lean`)

These kinds account for every mark by class: the predicate lists the marks of each class of part
(objects, arrows, 2-cells; cells, entries, headings, decorations) and requires each list to be
exactly the builder's, shape, position and colour role included, and no mark of any other part.

* Commutative diagrams: `CommDiagram.draw_faithful`, `CommDiagram.builder_faithful` (the drawn
  arrow bodies, `Diagram.arrows`, are exactly `(k, src k, tgt k)` for the data's arrows, in order,
  `arrows_draw`; the texts of the arrows are exactly their labels and the `≅` of isomorphisms; the
  objects' labels are at their positions; every body, tip, tail mark, hook, bar and 2-cell is the
  builder's). The body of a straight arrow runs from where the segment between the objects'
  centres leaves the first label's box to where it enters the second's, a bent arrow is a
  quadratic Bézier curve sampled at exact rational points, a loop a cubic one; that those are
  good pictures is tested, not proved. `FinMaps.Commutes` (the maps between finite sets fit the
  arrows and the two paths of every claim agree at every element) and `FinMaps.StylesHold` (an
  arrow drawn `↣` or `↪` is injective, `↠` surjective, `≅` bijective, `=` the identity) are
  decided on the data.
* Cayley tables and graphs: `FinMagma.table_faithful`, `FinMagma.entries_table` (the entry
  written in cell `(a, b)` is the name of `a * b`, and every cell has its entry; the cell is
  tinted in series colour `a * b`), `FinMagma.isGroup` decides associativity, an identity and
  inverses on the table; `FinMagma.mem_cayleyArrows` (an arrow of the Cayley graph in colour `c`
  joins `g` to `g * s` for `s = gens[c]`, an involution's pairs as one line without a tip).
* Hasse diagrams with marked elements: `FinGraph.ink_of_faithful` (a vertex dot is in accent 1
  exactly when the vertex is marked).
* Quivers: `FinQuiver.draw_faithful`, `FinQuiver.arrows_toCommDiagram` (the drawn arrows are the
  quiver's, several between two vertices and loops included; the vertex labels are the
  dimensions).
* The gallery's seven figures of algebra each have a specification checked by the kernel (the
  arrows and labels written out; that the reductions of `ℤ/12` and the cube of reductions of
  `ℤ/30` commute; that doubling `ℤ/2 → ℤ/4` is injective, the reduction surjective, and the image
  of each map the kernel of the next; the table of `S₃` a group, not commutative, with trivial
  centre); `lake test` compiles changed copies that must fail inside them and plants a fault in
  every class of mark.

**Plots of sequences, grids of numbers and lattices** (`PILean/Diagram/Sequence.lean`,
`Lattice.lean`; the gallery's figures with their specifications in
`PILeanTest/NumberDiagrams.lean`)

These kinds account for every mark by class as the diagrams of algebra do.

* Plots of sequences: `SeqPlot.draw_faithful`, `SeqPlot.builder_faithful` (the points,
  `Diagram.data`, are exactly `(k, n, point n (f n))` for every sequence `k` and every `n` of the
  range, sequence by sequence; the curves are the polylines through their values at the indices;
  the axes, ticks, tick labels, the legend's samples and names and the name of the index axis are
  the builder's, colours included; nothing else is drawn), `SeqPlot.mem_data` (`(k, n, p)` is
  drawn exactly when sequence `k` is `f`, `lo ≤ n ≤ hi` and `p` is the point of `n` and `f n`).
* Grids of numbers: `CellPlot.draw_faithful`, `CellPlot.builder_faithful` (the cells and their
  texts are the data's, cell by cell, at their positions, in the colour of their mark; the
  headings are the plot's), `CellPlot.mem_marked`.
* Lattices: `PlaneLattice.draw_faithful`, `PlaneLattice.builder_faithful` (the dots are exactly
  the candidates `m ω₁ + n ω₂` in the window, each in the colour of its mark; the parallelogram
  `0, ω₁, ω₁ + ω₂, ω₂` and the axes are the builder's), `PlaneLattice.mem_points`. That the
  candidates include every lattice point of the window is proved in `pilean-mathlib`
  (`PlaneLattice.natAbs_le_bound`), not in the core.
* The gallery's four figures (the totient on `1, …, 100`, a sieve of `1, …, 100`, the Gaussian
  primes with `|a|, |b| ≤ 4`, a skew lattice) each have a specification that writes out the
  values, the marked numbers and points, or the lattice points, checked by the kernel; `lake test`
  compiles changed copies that must fail inside them and plants a fault in every class of mark.
* Zeros and poles of a rational function (`PILean/Diagram/ZeroPole.lean`,
  `PILeanTest/ComplexDiagrams.lean`): `RationalPlot.draw_faithful`, `builder_faithful` (the
  circles are exactly the supplied zeros, in order, at their exact positions; the crosses the
  poles; the written multiplicities those above 1; the axes and the title the builder's; nothing
  else), `RationalPlot.Verified` (decided: each supplied zero is a root of the numerator of exactly
  its multiplicity, in exact Gaussian rational arithmetic, each pole one of the denominator, the
  zeros distinct, the poles distinct, no zero a pole) and `RationalPlot.Complete` (decided: the
  multiplicities add up to the degrees). `rationalFigure_spec` states both for
  `f(z) = (z² + 1)(z − 1/2)² / ((z² − 2z + 2)(z + 3/2))`, with the data and the written `2`
  beside `1/2`; `lake test` changes copies (a multiplicity, a zero, a pole, a coefficient, the
  window) that must fail inside it.
* Not proved: that the pictures are good (the axes a tenth of a unit outside the points, ticks at
  round indices, the points' radius shrinking with their number, the cells of an Ulam spiral
  apart, marked cells of a table apart), which is tested. The layout checks of plane figures run on these figures with two
  allowances for the points of a plot (`plotProblems`): two points may stand closer than markers
  must in a geometric figure when their discs do not overlap, and a point may lie near a
  comparison curve.

## Plots against the real numbers

The core has no real numbers, so it cannot say that a curve is near `sin`. The optional package
`pilean-mathlib` (folder [`mathlib/`](../mathlib/README.md), which requires Mathlib; users of the
core never need it) adds a specification over ℝ and theorems that connect the exact samples to
it.

* **The specification.** `PILean.polyline ps` is the union of the segments joining consecutive
  points of a list, a subset of the real plane; `PILean.Exact.plot g lo hi n` is the polyline
  through the exact samples of `g`. `PILean.IsVerticallyWithin S f s δ` says: every point of `S`
  has its abscissa in `s`, above every abscissa of `s` there is a point of `S`, and every point
  `(x, y)` of `S` has `|y - f x| ≤ δ`.
* **Why vertical distance.** A plot is read above an abscissa: at `x`, how far is the curve from
  `f x`? This is stronger than the distance between the two curves as subsets of the plane:
  `IsVerticallyWithin.hausdorffDist_le` proves that vertical distance at most `δ` gives Hausdorff
  distance at most `δ` (for the maximum metric), and the converse fails where the graph is steep.
* **The general theorem**, `PILean.Exact.isVerticallyWithin_plot`. Let `g : ℚ → ℚ` be plotted
  with `n ≥ 1` steps on `[lo, hi]`, `lo < hi`. Let `f : ℝ → ℝ` be continuous on `[lo, hi]` and
  twice differentiable on the open interval `(lo, hi)`, with `|f''| ≤ M` there. If
  `|g x - f x| ≤ ε` at every grid point `x`, then the polyline through the exact samples of `g`
  is vertically within `ε + M h² / 8` of the graph of `f` over `[lo, hi]`, `h = (hi - lo) / n`.
  It rests on `PILean.abs_chord_sub_le`, the classical bound `M (v - u)² / 8` for the error of
  linear interpolation, proved here by Rolle's theorem.
* **The example**, `sineFigure` with `sineFigure_spec`. The figure plots the Taylor polynomial of
  the sine of degree 15, which has rational coefficients, on the grid of 96 steps from −3 to 3.
  The theorem says that the polyline through its 97 exact samples is vertically within `1/2000`
  of the graph of the real sine over `[−3, 3]`. At the gallery size (640 × 400, 143.5 pixels for
  one unit of the ordinate) that is 0.072 pixel.

What this does not prove: anything after the exact samples. The conversion of each sample to a
floating-point number, the position on the page and the rasteriser are the same tested,
unproved code as for every other picture. The theorem bounds the distance from the *exact*
polyline to the sine; that the pixels show that polyline is tested.

Each theorem of the package depends on the three standard axioms only. Its build checks this for
every declaration of the package's modules, without a list of names, reports any `axiom` they
declare, used or not, and fails if a file of the package is left out of the check
(`PILeanMathlib/Axioms.lean`, with the commands of `PILean.Trust.Attr`); every `lake test` of the
package checks that no file is left out.

**Certified plots** (`PILeanMathlib/CertifiedPlot.lean`, `CertifiedPlotBound.lean`,
`Examples/Real.lean`). The sine's theorem as a kind: `CertifiedPlot.Certifies c f` is
`IsVerticallyWithin` of the polyline through the exact samples of the approximant and the graph
of `f` over `[lo, hi]` at the bound `delta`, and `CertifiedPlot.certifies_of` proves it from an
error at the grid points and a bound on `|f''|`. The figures' theorems name the function, the
interval, the number of steps and the bound, pin the title (which states them) and the one curve,
and prove the bound: `exp` on `[−2, 2]` within `1/1000` (Taylor, degree 15, `e² ≤ 15/2`), `cos`
on `[−3, 3]` within `1/2000` (Taylor, degree 16), `log` on `[1/2, 3/2]` within `1/8000`
(Mathlib's estimate of the logarithm's series), `arctan` on `[−3/4, 3/4]` within `1/5000` (the
series' error by the mean value theorem, `abs_arctan_sub_arctanSumR_le`), `√` on `[1/4, 4]`
within `1/4000` (`|r − √x| ≤ |r² − x| / √x` with the squares checked by the kernel at the grid
points). The bounds are mostly the interpolation term `M h² / 8` with `M` the maximum of `|f''|`
over the interval, loose where `|f''|` is smaller. `lake test` compiles changed copies (a bound,
an interval, a number of steps, a name, a coefficient, a number of terms) that must fail inside
the theorems, and checks in floating point that each bound is under a tenth of a pixel in the
gallery's 640 × 400 pixel picture (at most 0.072 of a pixel; tested, not proved).

## Combinatorics against Mathlib

The package `pilean-mathlib` binds the diagrams to Mathlib's objects
(`PILeanMathlib/Combinatorics.lean`), with theorems stated in Mathlib's own definitions:

* `FinGraph.ofSimpleGraph_mem_edgePairs`: a pair `(a, b)` is drawn for a `SimpleGraph (Fin n)`
  exactly when `a < b` and `G.Adj a b`; `FinGraph.ofDigraph_mem_edgePairs`: for a `Digraph`,
  exactly when `G.Adj a b`.
* `FinPoset.ofOrder_mem_coverPairs`: for a partial order enumerated by `e : Fin n ≃ α`, an edge
  `(a, b)` is drawn exactly when `e a ⋖ e b` (`CovBy`); `FinPoset.ofOrder_isPartialOrder`.
* `YoungShape.ofYoungDiagram_cells`: cell `(i, j)` is drawn exactly when `(i, j) ∈ μ.cells`;
  `YoungShape.ofPartition_rows`: the row lengths of a `Nat.Partition` are its parts.
* `Tableau.ofSSYT_cells`, `Tableau.ofSSYT_entries`: for a `SemistandardYoungTableau μ`, the cells
  are those of `μ` and the entry written at `(i, j)` is `T i j`.
* `FinPerm.ofPerm_cycles_edges`, `FinPerm.ofPerm_crossings`: for an `Equiv.Perm (Fin n)`, an
  arrow `a → b` is drawn exactly when `σ a = b`, two strands cross exactly when `a < b` and
  `σ b < σ a`.
* `LatticePath.isDyck_dyckBits`, `LatticePath.ofDyckWord_step_rises`: the path of a `DyckWord`
  rises exactly at its `U`s.
* `SetSystem.ofFinsets_venn_inside`: an element is written inside circle `k` exactly when it
  belongs to the finset `sets[k]`.

Its gallery (`PILeanMathlib/Examples/Combinatorics.lean`) links a theorem of this kind to each of
nine figures: the divisors of 60 (`divisorsFigure_spec`: the elements are `Nat.divisors 60`, an
edge joins `a` to `b` exactly when `a ∣ b` and `b / a` is prime), the subsets of a 3-set with
`CovBy`, the Petersen graph as a `SimpleGraph`, a `YoungDiagram`, Mathlib's highest-weight
tableau, the cycles and the wiring diagram of a permutation (with its sign, `(-1)` to the number of
crossings), a `DyckWord` and three finsets in a Venn diagram. Each of these theorems also states
the kind's `Faithful` predicate of its figure (every mark is the builder's, so no mark can be
added), its title, and its labels against the object (vertex `i` of the Petersen graph is named
by the 2-subset it is, divisor `d` is labelled `toString d`, a subset by its elements, a Venn
element by its number and the set of the multiples of `m` as `mℤ`); `lake test` compiles changed copies
of each figure (a label, a title, an added mark, a colour role) that must fail inside the theorem.

## Algebra against Mathlib

`PILeanMathlib/Category.lean` realises a commutative diagram in a category
(`CommDiagram.Realisation`: an object for each object, a morphism for each arrow between the
objects of its ends), with `Realisation.Commutes` (the composites of the two paths of every claim
are equal) and `Realisation.StylesHold` (`↣` and `↪` are `Mono`, `↠` `Epi`, `≅` `IsIso`, `=` an
identity). `square_commutes_iff`: the drawn square commutes exactly when `CommSq f g h i`;
`triangle_commutes_iff`: the triangle exactly when `f ≫ g = h`; `shortExact_iff`: the marks of
`0 → X₁ ↣ X₂ ↠ X₃ → 0` hold of a short complex `S` and `S` is exact exactly when
`S.ShortExact`. `PILeanMathlib/Group.lean`: `FinMagma.ofMul_mul`, `ofMul_isGroup`,
`ofMul_isCommutative_iff`, `mem_centre_ofMul`, `ofMul_entries`, `ofMul_cayleyArrows`, and
`FinPoset.mem_coverPairs_of_equiv` (the edges of a Hasse diagram drawn through an enumeration are
the covers `⋖`).

Its figures (`PILeanMathlib/Examples/Algebra.lean`): the Cayley table of `DihedralGroup 4`
(`d4TableFigure_spec`: the entries are the products, a group, not commutative, centre `{1, r 2}`),
its Cayley graph (`d4CayleyFigure_spec`), its lattice of subgroups (`d4SubgroupsFigure_spec`: the
ten drawn subgroups are all the subgroups, each once, decided over the 256 subsets of the group;
each is named by generators and is the subgroup they generate, `Subgroup.closure`, the names of
the generators being those of `d4Name`; the edges are `⋖`; a dot is in colour exactly when its
subgroup is `Normal`; the names the table writes are `d4Name` of the elements), a `CommSq` of
reductions in `Type` (`commSqFigure_spec`: each drawn object is named by the `ZMod n` it is and
each arrow label by the reduction it is, `Realisation.Names`, so a renamed object or two swapped
labels break the theorem) and the drawing of a short exact sequence
(`shortExactFigure_spec`, for every short complex of a preadditive category with a zero object).

## Number theory against Mathlib

`PILeanMathlib/NumberTheory.lean`: `SeqPlot.data_iff` (the points of a faithful plot of one
sequence that agrees with `g` are exactly `(n, g n)` on the range), `card_filter_range` (a count
with a Boolean filter of `List.range n` is the `Finset` count), `isSquare_iff_any`,
`prime_of_norm_prime`, `prime_of_unit_mul`, `not_prime_of_mul`, `not_prime_of_shown` (a factor
witness found by `gaussianWitness` shows that a Gaussian integer is not prime), and
`nodup_of_distinctInBox` (points of a box, no two at one place, checked in linear time by a bit
mask). `PILeanMathlib/Lattice.lean`: `PlaneLattice.natAbs_le_bound`, `mem_points_iff`,
`mem_dots_iff` (a faithful figure of a lattice of independent periods draws exactly the points of
`Submodule.span ℤ {ω₁, ω₂}` in its window) and `nodup_dots` (each once).

Its figures (`PILeanMathlib/Examples/NumberTheory.lean`). The figures compute with plain
functions; `totient'_eq`, `divisorCount_eq`, `isPrime'_iff`, `primeCount_eq`, `harmonic'_eq`,
`legendre'_eq` and `prime_of_gaussianPrime` prove them equal to Mathlib's for every argument, so
the kernel evaluates only the caps, the layouts and the finite checks named below.

* `totientFigure_spec`: the points are exactly `(n, Nat.totient n)` for `1 ≤ n ≤ 100`, under the
  one name `φ(n)`, at positive scales.
* `divisorFigure_spec`: the points are exactly `(n, σ 0 n)` for `1 ≤ n ≤ 100`.
* `primeCountFigure_spec`: the points are exactly `(n, Nat.primeCounting n)` for `2 ≤ n ≤ 100`;
  the one curve is the polyline through `(n, n / (harmonic n - 1))` at the same indices.
* `ulamFigure_spec`: the cells are `1, …, 441`, `1` at the origin, each next to the one before,
  no two at one place (decided by a bit mask); a cell is filled exactly when its number is
  `Nat.Prime`.
* `residueFigure_spec`: for each `p` of `3, 5, 7, 11, 13` (row `i`) and `a < p`, the cell of key
  `100 p + a` stands in column `a` of row `i`, is marked exactly when `a` is a nonzero square in
  `ZMod p` and shows `legendreSym p a` (`−1` with a minus sign); there are 39 cells, no two with
  one key, so no others; the headings are written out.
* `gaussianFigure_spec`: the dots are exactly the `a + b i` with `|a|, |b| ≤ 7`, at `(a, b)`, in
  accent 1 exactly when `Prime (⟨a, b⟩ : GaussianInt)` and faint exactly when not. Both
  directions are proved: a marked point is prime by Mathlib's theorems (a prime norm, or a unit
  times a rational prime `≡ 3 (mod 4)`); an unmarked point is `0`, a unit, or a product of two
  factors of norm greater than one found by a search, which the kernel checks for every point of
  the window (`unmarked_shown`).
* `latticeFigure_spec`: the dots are exactly the points of
  `Submodule.span ℤ {(1, 0), (1/2, 7/8)}` in `[-3, 3] × [-2, 2]`, each once, all in the ink; the
  parallelogram is `0, ω₁, ω₁ + ω₂, ω₂` in accent 0.

Every one of these theorems also writes out the whole figure ("What a gallery theorem pins"), so
its title (its accessible name, which states the object and the range), width and style; the Ulam
spiral's positions are `ulamWalk 441`, and the residue table's headings are written out with their
positions. The colours a style gives the colour roles and the radius of the points, which the
library's layout computes, are library code.

`lake test` in `mathlib/` joins the figures' module and the theorems' module into one file,
compiles copies with a datum changed (a value, a range, a name, the curve, a marking, a text, a
heading, the window, a period, a colour) and requires each to fail inside the figure's theorem
and nowhere in the figures (`PILeanMathlibTest/Mutations.lean`). Möbius sums are not drawn: no
plain function is proved equal to `ArithmeticFunction.moebius`, and the kernel cannot evaluate
Mathlib's in practice.

## Zeros and poles against Mathlib

`PILeanMathlib/RationalPlot.lean` reads a list of rational coefficients as a polynomial over ℚ
(`ofCoeffs`) and over ℂ (`ofCoeffsC`): its value at `a + b i` is the core's Horner evaluation
(`eval_ofCoeffsC`), the core's derivative is the derivative (`ofCoeffs_iterDeriv`), and its degree
is at most the core's (`natDegree_ofCoeffs_le`). `rootMultiplicity_of`: a point that passes the
core's test of multiplicity `m` has `Polynomial.rootMultiplicity` exactly `m` (by Mathlib's
characterisation through iterated derivatives in characteristic zero). `RationalPlot.zeros_complete`
and `poles_complete`: in a verified and complete figure every complex root of the numerator (the
denominator) is a supplied zero (pole), by the count of roots (`Polynomial.card_roots'`,
`count_roots`). `PILeanMathlib/Examples/Complex.lean`: `rationalFigure_roots` states all of this for
the gallery's figure, frame by mark: each circle is a root of its written multiplicity, each cross
a root of the denominator, and there are no other complex roots.

## What is tested, not proved

* The rasteriser (coverage, compositing, colour conversion), the PNG, APNG and GIF encoders and
  decoders, the SVG writer, the PDF writer and its structural check: tested against published values, other software and the golden files
  in `examples/`.
* The layouts of the combinatorial diagrams (Hasse edges going up, the tidy layout of trees, the
  circle's points), and that the diagrams pass the layout checks of plane figures in both
  themes: tested.
* The quality of a graph layout (layers, crossings, coordinates, curves): tested, including
  against Graphviz's recorded measures (`PILeanTest/graphs/dot-recorded.tsv`); so are the
  sifting, the packing of components, mirrored layouts and the SVG for web pages. Only the *set* of drawn edges and the downward direction of the layers (by
  the repair pass) are proved, not where the edges run, and not that network simplex finds a
  feasible or optimal layering on its own (`layersBeforeRepair` is tested, see above).
* The floating-point conversion and the page mapping. `Exact.toFloat` divides the numerator by
  the denominator as floating-point numbers; when both have at most 53 significant bits (as in
  the gallery) the two conversions are exact and IEEE 754 division gives the floating-point
  number nearest to the rational. That is an argument about the arithmetic of the machine, not a
  theorem of this library. The tests check values of the conversion (among them fractions with 53
  significant bits, and that a fraction and the same fraction not in lowest terms convert alike)
  and the positions of the gallery's points; that is a check on those pictures.
* The domain colouring (`DomainColouring`): a picture of a `Float` function in floating point,
  marked `@[figure illustration]`; nothing about it is proved, and its standing says so.
* The adaptive sampler of `Series.function`, which plots a `Float → Float` function by refining
  where the curve bends and breaking it at poles and jumps. Its guarantee is weaker: it is
  tested (refinement, poles, jumps, undefined regions), not proved. Use `Series.ofExact` when the
  statement "these are exactly the values of this function on this grid" matters.
* `Animation.frameCount`, which rounds the duration times the frame rate as floating-point
  numbers.
* `Easing.eval` (against cubic Bézier values computed in 60-digit decimal arithmetic, solved for
  its parameter within `1e-12`, never decreasing), the SMIL attributes the builders of
  `PILean/Anim/Smil.lean` write (counts of values, key times and splines; key times that increase
  strictly), and what they mean: `Smil.valueAt`, an evaluator of SMIL timing, gives the eased value
  of the timeline at 50 times within `1e-9`, refuses what SMIL makes an error, and reproduces
  nested turns (`Smil.nest`) as the composed exact rotations. That a browser follows SMIL as
  `valueAt` does is not checked by the tests of the core.
* Motions of plane figures: that a declared move lands on the next key (`Motion.problems`, within
  0.01 px), tested with wrong angles and centres, turns of items that did not move, a slide that
  misses by 0.02 px, a polygon with only a later vertex out of place, a radius that changes under
  a slide, whole turns and moves of missing actors; the rest check, the evaluator, the model
  computed apart and the browser's pixels, as listed above under "Motions of plane figures";
  for pictures of panels, as listed under "Motions as panels of one picture".
* The hypotheses of the drawing theorems on the gallery pictures (every converted point has a
  page position) are checked at run time by `lake test`.

## What is trusted

* **Lean itself**: the kernel that checks the proofs, the compiler and the runtime that execute
  the code (a theorem is about the Lean definition; that the compiled program computes it is
  Lean's responsibility), the standard library, and the three standard axioms.
* **The build**: that the bytes in a file are the ones the build produced from the declaration
  they name. `docs/TRUST.md` describes how this is made checkable (the source record, the
  fingerprint, the manifest, `pilean-build --check` and `pilean-verify`). The theorem of a
  gallery picture that has one is in the picture's module, so building that module checks it
  (the Mathlib package keeps its theorem in a module that imports the picture's, and building
  that module checks it); a file edited afterwards is only detected by those tools.
* **The viewer** that displays the file: a browser, an image program or a printer draws the SVG or
  PNG its own way.
* The reader of the theorem: that the statement says what you mean. The statements are short and
  in plain definitions on purpose, and the `example` beside each one is there to show that they
  are not empty.

## How to read a picture's guarantee

1. Find its source record (`lake exe pilean-info FILE`): the module, declaration and line, and
   its standing as the build recorded it: `linked` with the theorems linked to it, or
   `illustration` (`docs/TRUST.md`, "Standing"). The record is what the file says about itself;
   `pilean-build --check` is what ties it to the source.
2. Read the theorem beside the declaration (in the Mathlib package, in the module that imports
   the declaration's: `PILeanMathlib.Examples.Sine` for `SineFigure`). It names the exact
   function, list, relation or time. The command `figure_links picture theorem` links the two,
   and fails the build unless the theorem is proved from the standard axioms and its statement
   names the picture itself (the picture's constant occurs in the statement once its `let`s and
   beta-redexes are reduced; a statement about a definition the picture is built from is
   refused; `docs/TRUST.md` has the exact rule). That check is about names only: it cannot tell
   a strong statement from an empty one that names the picture, so the statement is still yours
   to read. The link is a pointer to a statement, not a certificate that the picture is correct.
3. Run `lake build` on that module; the theorem checks.
4. For the part after floating point begins, the tests and `docs/TRUST.md` say what is compared.
