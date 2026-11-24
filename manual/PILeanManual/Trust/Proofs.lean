/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILean
import PILean.Trust.Attr
import PILeanTest.ProvedExamples
import PILeanVersoManual
import PILeanManual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open PILeanVerso.Manual
open PILeanManual

#doc (Manual) "What a Picture Proves" =>
%%%
tag := "proofs"
%%%

```lean -show
namespace PILeanManual.ProofsGuide
open PILean PILean.Plot PILeanTest.ProvedExamples
```

A PILean picture can come with a theorem. The theorem is about the Lean object the picture was
drawn from, not about the picture's pixels. This chapter says what is proved, what is only
tested, and what you still have to trust; it follows `docs/PROOFS.md`. Every theorem of the core
and of the gallery that it shows is printed from the library when the manual is built, so a
changed statement changes the page and a renamed one breaks the build; the theorems of the
optional Mathlib package are paraphrased ({ref "proofs-real"}[Plots Against the Real Numbers]).

# The Idea
%%%
tag := "proofs-idea"
%%%

Every picture is the value of a Lean declaration. Four kinds have an exact specification:

:::table +header
*
  * Picture
  * The Lean object
  * What the theorem says
*
  * Function plot
  * an exact function on the rational numbers, `f : Rat → Rat`, a rational interval `[lo, hi]`
    and a number of steps `n`
  * the plotted series has exactly the `n + 1` points `(x, f x)` with `x` on the grid
    `lo + k (hi - lo) / n`, `k = 0, …, n`, in order and no others, each coordinate converted to a
    floating-point number
*
  * Data plot
  * a list of integer (or exact rational) points
  * the plotted series has exactly the points of the list, in order, none added or dropped, each
    coordinate converted to a floating-point number
*
  * Graph
  * a list of nodes and a relation on them (or an edge list)
  * the nodes are exactly the list and the edges exactly the related pairs, each once; the layout
    has one route for each edge, with that edge's two ends, and the picture draws those routes.
    Nothing is said about where a node is placed or how a route runs
*
  * Animation
  * a drawing as a function of time, a frame rate
  * frame `i` is the drawing function applied to the exact rational time `i / fps` converted to a
    floating-point number. Nothing is said about the drawing function itself or about the number
    of frames
:::

*Floating point.* Every statement in this table is about exact numbers and lists. The picture is
computed from them in floating-point arithmetic: the conversion of each exact number
({name}`PILean.Exact.toFloat`), the axis scales, the positions on the page, the rasteriser. That
part is tested, not proved, so no theorem here speaks of a pixel.

*Samples, not graphs.* For a function plot the theorem says that the curve is drawn through
exactly these sample points (converted to floating point); it does not say that the curve is the
graph of `f`. Between two consecutive samples the picture is a straight segment, and nothing in
the core library is proved about the distance from that segment to `f`. The optional package
`pilean-mathlib` proves such a bound over the real numbers for the exact samples, under stated
hypotheses on the function; it is an experiment with one worked example, the sine
({ref "proofs-real"}[Plots Against the Real Numbers]).

*Which functions.* The theorem is about functions with exact rational values. A plot of `sin`,
`exp` or a square root made with {name}`PILean.Plot.Series.function` is sampled in floating point
by an adaptive sampler and has no theorem.

The rational numbers are Lean's {name}`Rat`: a fraction in lowest terms, so equality of rationals
is `=`. Many of the theorems are short: the series constructors are defined to hold the converted
samples, so {name}`PILean.Plot.Series.ofExact_points` holds by unfolding the definition. They are
stated as theorems so that the specification of a picture can be read without reading the code,
and so that a change to the code that broke it would be caught.

# Pictures with Their Theorems
%%%
tag := "proofs-gallery"
%%%

The repository's gallery has four pictures with a theorem, one of each kind, in the module
{sourceFile}`PILeanTest/ProvedExamples.lean`. The manual draws each from that declaration, and
the `figure` directive's `proves` option accepts the theorem only under the rule of
`figure_links` ({ref "proofs-link"}[Linking a Theorem to a Picture]); below each picture is the
theorem as the library states
it.

## A Function Plot
%%%
tag := "proofs-function"
%%%

:::figure PILeanTest.ProvedExamples.provedFunction (alt := "Two curves on [-3/2, 3/2]: the cubic x cubed minus x, rising from -15/8 through a hump and a dip to 15/8, and the dashed parabola x squared minus 1, from 5/4 down to -1 at 0 and back up.") (links := PILeanTest.ProvedExamples.provedFunction_spec)
:::

{docstring PILeanTest.ProvedExamples.provedFunction_spec}

The `example` beside it in the source shows the statement is not empty: the grid's first three
points are `-3/2`, `-11/8` and `-5/4`, and the values at `-3/2` are `-15/8` and `5/4`. The build
checks such facts; here they are evaluated:

```lean (name := functionFacts)
#eval (Exact.grid lo hi steps).take 3
#eval (cubic lo, parabola lo)
#eval Exact.gridStep lo hi steps
```

```leanResult functionFacts
```

## A Data Plot
%%%
tag := "proofs-data"
%%%

:::figure PILeanTest.ProvedExamples.provedData (alt := "A zigzag line with markers through 25 points (k, k squared mod 17 minus 8) for k from 0 to 24, between -8 and 8.") (links := PILeanTest.ProvedExamples.provedData_spec)
:::

{docstring PILeanTest.ProvedExamples.provedData_spec}

## A Graph
%%%
tag := "proofs-graph"
%%%

:::figure PILeanTest.ProvedExamples.provedGraph (alt := "The numbers 1 to 12 as nodes in layers, 1 at the top, with an arrow from a to b whenever a is less than b and divides it: 23 arrows in all.") (links := PILeanTest.ProvedExamples.provedGraph_spec)
:::

{docstring PILeanTest.ProvedExamples.provedGraph_spec}

## An Animation
%%%
tag := "proofs-animation"
%%%

:::figure PILeanTest.ProvedExamples.provedClock (alt := "A dot going once round a circle in one second, in ten frames.") (links := PILeanTest.ProvedExamples.provedClock_spec) (width := "200px")
:::

{docstring PILeanTest.ProvedExamples.provedClock_spec}

# Linking a Theorem to a Picture
%%%
tag := "proofs-link"
%%%

The command `figure_links fig thm` links a theorem to a registered figure. It is an error, so the
module does not build, unless `thm` is a theorem, depends on no `sorry` and on no axiom other than
`propext`, `Classical.choice` and `Quot.sound`, and its statement names the figure itself.

The rule, exactly ({name}`PILean.Trust.statementNamesFigure`, with
{name}`PILean.Trust.ruleStatement`):

1. The statement of `thm` is taken as Lean elaborates it and reduced, everywhere in the term and
   until nothing is left to reduce, by three steps and no others: a `let` or `have` is replaced by
   its body with the value put for the variable; `letFun v f` becomes `f v`; an application of a
   `fun` to arguments is beta-reduced.
2. The constant `fig` must occur in the result.

What this means:

* A field of the figure is a projection applied to it, so a statement about `fig.panels`,
  `fig.edges`, `fig.nodes` or `fig.frameSeq` names the figure. The usual shape begins with an
  equation that says what the figure holds and goes on about its parts.
* No definition is unfolded. A statement about a definition the figure is built from (a series, a
  data list, a relation), or about a term that happens to equal the figure, does not name it and is
  refused: the figure could be changed and leave such a statement true.
* A name that occurs only in the value of a `let` the statement does not use, or only as the
  argument of a `fun` that discards it, does not count: the reduction removes it.
* The reduction stops at definitions, so a name that a definition would discard still counts: a
  `match` on the figure, a projection of a pair built around it (`(fig, P).2`), a definition that
  ignores an argument, and an `if` whose condition settles the branch are accepted although the
  figure plays no part in what they say.
* The rule is about names; it does not judge what the statement says. A statement that names the
  figure and says nothing of substance about it passes: `fig = fig`, the figure in a hypothesis
  that is never used, a property that holds of every figure. What the theorem says is for its
  reader to judge.

A link is a pointer from a picture to a statement to read, not a certificate that the picture is
correct.

The command at work, on the gallery's function plot. A true statement about a series the plot uses
does not name the plot, and is refused:

```lean +error (name := refusedLink)
figure_links provedFunction cubicSeries_size
```

```leanResult refusedLink
```

and so is a statement that names the plot only as the argument of a `fun` that discards it:

```lean +error (name := refusedBeta)
figure_links provedFunction cubicSeries_size_beta
```

```leanResult refusedBeta
```

while the empty statement `provedFunction = provedFunction` is accepted, which is why the
statement is still yours to read:

```lean (name := emptyLink)
theorem provedFunction_self : provedFunction = provedFunction := rfl

figure_links provedFunction provedFunction_self
#eval "accepted"
```

```leanResult emptyLink
```

# What Is Proved
%%%
tag := "proofs-proved"
%%%

Every theorem of the library depends on no axiom beyond Lean's three standard ones (`propext`,
`Classical.choice`, `Quot.sound`); what that leaves trusted (Lean's kernel, compiler and runtime) is
listed under {ref "proofs-trusted"}[What Is Trusted]. The repository's test build checks this for
every declaration of the library and of the test modules the test driver imports, of every kind
(theorems, definitions, opaque constants, inductive types with their constructors and recursors),
without a list of names, and reports any `axiom` they declare, used or not
({sourceFile}`PILeanTest/Axioms.lean`); it also checks that no file of the library and no test
module the test driver imports is left out of that check. The manual's build runs the same command
over the modules of the library it imports (`PILean`, which imports every other module of the core,
and `PILean.Trust.Attr`). The command prints nothing when it passes and fails the build otherwise;
the line after it is only a label, printed once the command has passed:

```lean (name := axiomsCheck)
#assert_standard_axioms PILean
#eval "every declaration of the modules PILean.* uses at most the three standard axioms"
```

```leanResult axiomsCheck
```

The theorems, as the library states them:

## Function Plots
%%%
tag := "proofs-proved-function"
%%%

{docstring PILean.Exact.grid_length}

{docstring PILean.Exact.gridPoint_eq}

{docstring PILean.Exact.mem_samples}

{docstring PILean.Exact.samples_fst}

{docstring PILean.Plot.Series.ofExact_points}

{docstring PILean.Plot.Series.ofExact_size}

{docstring PILean.Plot.Series.ofExact_draw}

Not proved: anything about the curve between two samples, and anything about a function that is
not rational-valued.

## Data Plots
%%%
tag := "proofs-proved-data"
%%%

{docstring PILean.Plot.Series.ofIntPoints_points}

{docstring PILean.Plot.Series.ofIntPairs_recover}

{docstring PILean.Plot.Series.ofSamples_draw}

{docstring PILean.Plot.runs_sublist}

## Graphs
%%%
tag := "proofs-proved-graph"
%%%

{docstring PILean.Graph.mem_relationPairs}

{docstring PILean.Graph.relationPairs_nodup}

{docstring PILean.Graph.ofRelation_layout_edges}

{docstring PILean.Graph.layout_edge_endpoints}

{docstring PILean.Graph.Layout.draw_edges}

{docstring PILean.Graph.assignLayers_lt}

`assignLayers_lt` holds by construction: the layering ends with a repair pass
({name}`PILean.Graph.fixLayers`) that moves a node down until its incoming edges point down, and
the theorem is about that pass. Nothing is proved about the layers network simplex and balancing
produce before it; a test checks, on random graphs, the fixtures and the import graphs, that the
repair changes nothing there. Not proved: the routes of the edges, the crossing reduction's
sifting and seeded starts, the packing of components, mirrored layouts and the SVG for web pages;
the coordinates are floating point.

## Animations
%%%
tag := "proofs-proved-anim"
%%%

{docstring PILean.Animation.exactTime_eq}

{docstring PILean.Animation.time_eq_exactTime}

{docstring PILean.Animation.frameSeq_getElem}

{docstring PILean.Animation.frameTrees_getElem}

# Where Floating Point Begins
%%%
tag := "proofs-float"
%%%

The exact numbers are turned into `Float` in one place, {name}`PILean.Exact.toFloat` (the numerator
and the denominator of the fraction in lowest terms, each converted, then divided). Everything the
theorems say about the *data* is before that point. After it:

* The series holds exactly the converted samples, in order
  ({name}`PILean.Plot.Series.ofExact_points`, {name}`PILean.Plot.Series.ofIntPoints_points`).
* The drawing code maps each point to the page with {name}`PILean.Plot.PanelLayout.pos` and breaks
  the line where a point has no position (a value that is not a number, or a non-positive value on
  a logarithmic axis). When every point has a position, {name}`PILean.Plot.Series.ofExact_draw` and
  {name}`PILean.Plot.Series.ofSamples_draw` say the picture is one polyline through the page
  positions of exactly those points in order. When some do not, {name}`PILean.Plot.runs_sublist`
  and {name}`PILean.Plot.runs_length` say that the runs that remain add nothing and keep the
  order, and that each has at least two points; that a run is a stretch of consecutive points, and
  which points are left out, follows from the definition and is tested, not stated by these
  theorems.

The value of `Exact.toFloat` (how near it is to the rational number), the position of a point (the
axis scale, clamping to the page) and everything after it are floating point and tested, not
proved. When the numerator and the denominator both have at most 53 significant bits, the two
conversions are exact and IEEE 754 division gives the floating-point number nearest to the
rational; that is an argument about the arithmetic of the machine, not a theorem of this library.

```lean (name := toFloatEx)
#eval Exact.toFloat (1 / 3)
#eval Exact.toFloat (2 / 6) == Exact.toFloat (1 / 3)
#eval Exact.toFloat (-3 / 2)
```

```leanResult toFloatEx
```

# What Is Tested, Not Proved
%%%
tag := "proofs-tested"
%%%

* The rasteriser (coverage, compositing, colour conversion), the PNG, APNG and GIF encoders and
  decoders, the SVG writer: tested against published values, other software and the golden files
  of the gallery.
* The quality of a graph layout (layers, crossings, coordinates, curves), including against
  Graphviz's recorded measures; the sifting, the packing of components, mirrored layouts and the
  SVG for web pages. Only the set of drawn edges and the downward direction of the layers (by the
  repair pass) are proved.
* The floating-point conversion and the page mapping: the tests check values of the conversion
  and the positions of the gallery's points.
* The adaptive sampler of `Series.function`.
* `Animation.frameCount`, which rounds the duration times the frame rate as floating-point
  numbers.
* The hypotheses of the drawing theorems on the gallery pictures (every converted point has a page
  position) are checked at run time by `lake test`.

# What Is Trusted
%%%
tag := "proofs-trusted"
%%%

* *Lean itself*: the kernel that checks the proofs, the compiler and the runtime that execute the
  code (a theorem is about the Lean definition; that the compiled program computes it is Lean's
  responsibility), the standard library, and the three standard axioms.
* *The build*: that the bytes in a file are the ones the build produced from the declaration they
  name. {ref "trust-build"}[Builds, Fingerprints and Checks] says how this is made checkable. The
  theorem of a gallery picture
  that has one is in the picture's module, so building that module checks it; a file edited
  afterwards is detected by `pilean-build --check`, and by `pilean-verify` unless the manifest
  was edited as well.
* *The viewer* that displays the file: a browser, an image program or a printer draws the SVG or
  PNG its own way.
* *The reader of the theorem*: that the statement says what you mean. The statements are short
  and in plain definitions on purpose, and the `example` beside each one is there to show that
  they are not empty.

# How to Read a Picture's Guarantee
%%%
tag := "proofs-read"
%%%

1. Find its source record (`lake exe pilean-info FILE`, or the caption of a figure in a manual
   built with `pilean-verso-manual`, which shows the declaration, its file and line). The record
   is a claim by whoever wrote the file; `pilean-build --check` is the check that the file is what
   the declaration renders now ({ref "trust-check"}[What the Answers Establish]).
2. Read the theorem beside the declaration. It names the exact function, list, relation or time.
   `figure_links picture theorem` links the two, and fails the build unless the theorem is proved
   from the standard axioms and its statement names the picture itself. That check is about names
   only: it cannot tell a strong statement from an empty one that names the picture, so the
   statement is still yours to read.
3. Run `lake build` on that module; building it checks the theorem.
4. For the part after floating point begins, the tests and `docs/TRUST.md` say what is compared.

# Plots Against the Real Numbers
%%%
tag := "proofs-real"
%%%

The core has no real numbers, so it cannot say that a curve is near `sin`. The optional package
`pilean-mathlib` (the folder {sourceFile}`mathlib`, which requires Mathlib) adds a specification
over ℝ and theorems that connect the exact samples to it. This manual does not build that package
(it would need Mathlib); the names below are checked against its source when the manual is built,
and the statements are paraphrased from its documentation, not printed from Lean.

* *The specification.*
  {inSource "mathlib/PILeanMathlib/Polyline.lean"}`PILean.polyline` is the union of the segments
  joining consecutive points of a list; {inSource "mathlib/PILeanMathlib/ExactPlot.lean"}`PILean.Exact.plot`
  is the polyline through the exact samples of a function; `PILean.IsVerticallyWithin S f s δ`
  says that every point of `S` has its abscissa in `s`, that above every abscissa of `s` there is
  a point of `S`, and that every point `(x, y)` of `S` has `|y - f x| ≤ δ`.
* *Why vertical distance.* A plot is read above an abscissa. Vertical distance at most `δ` gives
  Hausdorff distance at most `δ` for the maximum metric
  ({inSource "mathlib/PILeanMathlib/Polyline.lean"}`IsVerticallyWithin.hausdorffDist_le`); the
  converse fails where the graph is steep.
* *The general theorem*, {inSource "mathlib/PILeanMathlib/ExactPlot.lean"}`PILean.Exact.isVerticallyWithin_plot`.
  Let `g : ℚ → ℚ` be plotted with `n ≥ 1` steps on `[lo, hi]`, `lo < hi`. Let `f : ℝ → ℝ` be
  continuous on `[lo, hi]` and twice differentiable on `(lo, hi)`, with `|f''| ≤ M` there. If
  `|g x - f x| ≤ ε` at every grid point `x`, then the polyline through the exact samples of `g` is
  vertically within `ε + M h² / 8` of the graph of `f` over `[lo, hi]`, `h = (hi - lo) / n`. It
  rests on {inSource "mathlib/PILeanMathlib/Interpolation.lean"}`PILean.abs_chord_sub_le`, the
  classical bound `M (v - u)² / 8` for the error of linear interpolation, proved there by Rolle's
  theorem.
* *The example*, {inSource "mathlib/PILeanMathlib/Examples/Sine.lean"}`sineFigure_spec`. The
  figure plots the Taylor polynomial of the sine of degree 15, which has rational coefficients, on
  the grid of 96 steps from −3 to 3; the theorem says that the polyline through its 97 exact
  samples is vertically within `1/2000` of the graph of the real sine over `[−3, 3]`.

What this does not prove: anything after the exact samples. The conversion of each sample to a
floating-point number, the position on the page and the rasteriser are the same tested, unproved
code as for every other picture. The theorem bounds the distance from the *exact* polyline to the
sine; that the pixels show that polyline is tested.
