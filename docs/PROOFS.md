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
no other, and then says what the points of those series are. So changing the figure changes what is
proved, and a figure that no longer satisfies its theorem does not build.

Many of these theorems are short: the series constructors are defined to hold the converted
samples, so `Series.ofExact_points` holds by unfolding the definition. They are stated as theorems
so that the specification of a picture can be read without reading the code, and so that a
change to the code that broke it would be caught.

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
  `drawsExactPoints` state this for a figure, ready for `figure_proves`.
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
  segments), the figure's width, frame and style (the style's colour values), the layout, the
  label placement for `auto`, the fonts and lettering (LeAnTeX's typesetting for its example),
  the rendering to SVG and the pixels.
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
`cells`, `entries`, `strands`, `steps`, `members`) and compares it with the data as full lists, and
mark by mark with the layout; the theorems below say that the builders satisfy it for every
input within the kind's cap (`builder_faithful` takes the cap as its hypothesis; beyond it the
figure is a note, and nothing is drawn).

* `Diagram.toPlane_items`: the plane figure's items are the marks' items, in order (each built
  from the mark's exact points by the builders of `PILean.Exact.Plane`, so the theorems of plane
  figures about exact points apply to them).
* Graphs: `FinGraph.mem_edgePairs` (a pair `(i, j)` is drawn exactly when `i, j < n` and the pair
  is drawn by the relation: `adj i j` for a directed graph, `i ≤ j` and `adj i j ∨ adj j i` for
  an undirected one), `FinGraph.edgePairs_nodup`, `FinGraph.draw_faithful` (at every layout the
  drawn edges are `edgePairs` in order, the vertex dots `0, …, n - 1`, each dot, name and edge at
  the layout's positions, a loop a circle through its vertex), `FinGraph.toGraph_layout_edges`
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
  kernel, and `figure_proves` links it to the figure. `lake test` compiles copies of the module
  with a datum changed and requires each to fail inside the specification
  (`PILeanTest/SpecMutations.lean`), and plants faults in the drawn diagrams (a mark dropped,
  added, moved or relabelled) that each kind's `Faithful` must refuse.
* Not proved: the layouts' qualities (that a Hasse edge goes up the page, that the tidy layout
  keeps siblings apart and centres each parent, that the points of `Layout.circular` are near the
  equal angles; the points are exactly on the circle, which is tested), and everything after the
  exact marks (the floating-point conversion, the frame, text, colours, the rasteriser), as for
  every plane figure.

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
crossings), a `DyckWord` and three finsets in a Venn diagram.

## What is tested, not proved

* The rasteriser (coverage, compositing, colour conversion), the PNG, APNG and GIF encoders and
  decoders, the SVG writer: tested against published values, other software and the golden files
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
   its standing as the build recorded it: `proved` with the theorems linked to it, or
   `illustration` (`docs/TRUST.md`, "Standing"). The record is what the file says about itself;
   `pilean-build --check` is what ties it to the source.
2. Read the theorem beside the declaration (in the Mathlib package, in the module that imports
   the declaration's: `PILeanMathlib.Examples.Sine` for `SineFigure`). It names the exact
   function, list, relation or time. The command `figure_proves picture theorem` links the two,
   and fails the build unless the theorem is proved from the standard axioms and its statement
   names the picture itself (the picture's constant occurs in the statement once its `let`s and
   beta-redexes are reduced; a statement about a definition the picture is built from is
   refused; `docs/TRUST.md` has the exact rule). That check is about names only: it cannot tell
   a strong statement from an empty one that names the picture, so the statement is still yours
   to read. The link is a pointer to a statement, not a certificate that the picture is correct.
3. Run `lake build` on that module; the theorem checks.
4. For the part after floating point begins, the tests and `docs/TRUST.md` say what is compared.
