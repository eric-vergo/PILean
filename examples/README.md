# Gallery

Every picture here is a Lean value in [`PILeanTest/Examples.lean`](../PILeanTest/Examples.lean),
written by `lake exe pilean-gallery`: figures as SVG (`Figure.toSvg`) and as PNG through PILean's
own rasteriser and PNG encoder (`Figure.toPng`), both drawn from the same canvas
(`Figure.draw`), in the light style and the dark one (`Style.dark`). `lake test` checks that every
file is reproduced byte for byte.

The SVG files carry their text as SVG text in the style's font family; the PNG files draw it with
PILean's built-in single-stroke lettering ([specimen](lettering-specimen.png)), so they look the
same everywhere.

## Plots

| Figure | Light | Dark |
|---|---|---|
| **Functions** — `sin x`, `cos x`, `sin x / x`, sampled adaptively in floating point; this picture has no theorem (`function-plot`) | ![](function-plot.svg) | ![](function-plot-dark.svg) |
| **Poles and jumps** — `tan x`, `1 / x`, `⌊x⌋ / 2`: broken at poles and jumps, no line across them (`poles`) | ![](poles.svg) | ![](poles-dark.svg) |
| **Step and dashed function** — π(n) as a step line against `n / ln n` (`primes-step-plot`) | ![](primes-step-plot.svg) | ![](primes-step-plot-dark.svg) |
| **Line with markers and a labelled point** — Collatz stopping times (`collatz-data-plot`) | ![](collatz-data-plot.svg) | ![](collatz-data-plot-dark.svg) |
| **Scatter** — two clusters (`scatter-plot`) | ![](scatter-plot.svg) | ![](scatter-plot-dark.svg) |
| **Band and area** — fill between two curves with its middle line, an area, a reference line (`band-area-plot`) | ![](band-area-plot.svg) | ![](band-area-plot-dark.svg) |
| **Grouped bars** (`grouped-bars`) | ![](grouped-bars.svg) | ![](grouped-bars-dark.svg) |
| **Stacked bars**, with a negative part (`stacked-bars`) | ![](stacked-bars.svg) | ![](stacked-bars-dark.svg) |
| **Histogram** — 2000 values (`histogram`) | ![](histogram.svg) | ![](histogram-dark.svg) |
| **Error bars** and a fitted line (`error-bars`) | ![](error-bars.svg) | ![](error-bars-dark.svg) |
| **Logarithmic axis** — `n³`, `2ⁿ`, `n!` (`log-axis`) | ![](log-axis.svg) | ![](log-axis-dark.svg) |
| **Small multiples** — four panels sharing both axes (`small-multiples`) | ![](small-multiples.svg) | ![](small-multiples-dark.svg) |
| **Awkward data** — no data, a constant, huge values, NaN and ∞ (`awkward-data`) | ![](awkward-data.svg) | ![](awkward-data-dark.svg) |

The PNG of each figure has the same name with `.png`.

## Plane figures

Figures of plane geometry (`PILeanTest/Examples.lean`, `PlaneFigures`, and
`PILeanTest/PlaneExact.lean`), in world coordinates fitted into the page with one scale, drawn on
the vector canvas; colours by role from `Style.plane`, light and dark (`-dark`).

| Figure | Light | Dark |
|---|---|---|
| **Two disks and a chord** — closed disks of radius `√(3 + φ)` about `±1`, the chord from `−E` to `E` (`E = ζ − ζ²`), `E` on the left circle and in its colour, `−E` on the right one and in its, the circles' crossings `±(ζ − ζ⁴)` as rings, a mark for a turn of 72° clockwise; every point exact in ℤ[ζ₅], and `disks_spec` says which item is which and proves each recorded incidence in ℚ(√5) (`plane-disks`) | ![](plane-disks.svg) | ![](plane-disks-dark.svg) |
| **The elements** — a line and a ray clipped to the frame, a dashed circle, an arc with an arrowhead, a sector, a regular pentagon, a tinted triangle, a polyline, arrows, angle marks both ways, labels on four sides of a point (`plane-constructions`) | ![](plane-constructions.svg) | ![](plane-constructions-dark.svg) |
| **Exact points of ℤ[ζ₅]** — the unit steps `ζʲ` and a window disk; the steps in the window are decided exactly in ℚ(√5), and `zetaSteps_spec` says where each point is drawn (`plane-exact`) | ![](plane-exact.svg) | ![](plane-exact-dark.svg) |

## Graphs

Graphs are Lean values (`PILeanTest/Examples.lean`, `GraphFigures`), laid out by
`PILean.Graph` and drawn on the vector canvas, so the SVG and the PNG (through the rasteriser,
text as shapes) show the same picture. Each is written light and dark (`-dark`).

| Graph | SVG | PNG |
|---|---|---|
| **Modules of a small compiler** — a layered layout with two clusters and a labelled edge (`compiler`) | ![compiler modules, SVG](graph-compiler.svg) | ![compiler modules, PNG](graph-compiler.png) |
| **A module graph of 120 nodes** — layers, long edges as straight runs of dummy nodes (`modules`) | ![120 modules, SVG](graph-modules.svg) | ![120 modules, PNG](graph-modules.png) |
| **A ring of seven nodes** — the circular layout of an undirected graph (`ring`) | ![ring, SVG](graph-ring.svg) | ![ring, PNG](graph-ring.png) |
| **A tree** — the tree layout (`tree`) | ![tree, SVG](graph-tree.svg) | ![tree, PNG](graph-tree.png) |

`graph-build`, among the animations below, is the compiler graph appearing layer by layer.

## Animations

Each animation is written four ways from one `Animation` value: an animated SVG (declarative SMIL
animation, no script), an animated PNG, a GIF, and a still poster frame, which the animated SVG
also shows instead of the motion when the viewer asks for reduced motion.

| Animation | SVG | APNG | GIF | Poster |
|---|---|---|---|---|
| **A travelling wave** — the path's points interpolated by the viewer between 30 keyframes (`wave`) | ![](wave.svg) | ![](wave.png) | ![](wave.gif) | ![](wave-poster.png) |
| **Growing bars**, played once (`growing-bars`) | ![](growing-bars.svg) | ![](growing-bars.png) | ![](growing-bars.gif) | ![](growing-bars-poster.png) |
| **A graph building up**, layer by layer: every element in every frame, only opacities change, so the SVG interpolates (`graph-build`) | ![](graph-build.svg) | ![](graph-build.png) | ![](graph-build.gif) | ![](graph-build-poster.png) |

## Raster pictures

Drawn directly with `PILean.Raster.Draw` (`PILeanTest/Examples.lean`, `rasters`), written as PNG.

| Picture | PNG |
|---|---|
| **Cards with drop shadows** — `Path.roundedRect` filled over `Draw.dropShadow` (a Gaussian blur of its coverage), one card with a diagonal gradient, mixed in sRGB (`shadow-cards`) | ![](shadow-cards.png) |

## Pictures with a theorem

One picture of each kind whose content is specified by a theorem about the Lean object it was
drawn from (see [`docs/PROOFS.md`](../docs/PROOFS.md): what is proved, what is tested, what is
trusted). The definitions and theorems are in
[`PILeanTest/ProvedExamples.lean`](../PILeanTest/ProvedExamples.lean); each picture is tagged
`@[figure]`. Light style shown; the dark style has the suffix `-dark`.

| Picture | Theorem |
|---|---|
| ![function plot](proved-function.svg) **Function plot** (`provedFunction`) | `provedFunction_spec`: the figure's series are the cubic's and the parabola's and no other; the points of each are the 25 exact samples `(x, f x)` (of the cubic `x³ − x`, of the parabola `x² − 1`) on the grid `−3/2 + k/8`, `k = 0, …, 24`, converted one by one (`Exact.toFloat` is where floating point begins); the grid starts at `−3/2` and ends at `3/2`; every sample is `(x, f x)` with `x` on the grid. Nothing is proved about the curve between two samples. |
| ![data plot](proved-data.svg) **Data plot** (`provedData`) | `provedData_spec`: the figure's series are a line and markers and no other; the line's and the markers' points are the list `residues` of 25 integer pairs, converted point for point, in order; the integers are recovered from the exact points, so none is added, dropped or changed. |
| ![graph](graph-proved.svg) **Graph** (`provedGraph`) | `provedGraph_spec`: the nodes are the numbers 1 to 12, the edges are exactly the pairs `a < b` with `a ∣ b`, each once (an `example` beside the theorem counts 23), and the layout draws one route per edge, in order, with the edge's own index and ends (long edges pass through dummy nodes inside the layout and are still one route). |
| ![animation](proved-clock.svg) **Animation** (`provedClock`) | `provedClock_spec`: frame `i` of the animation (in the SVG, the APNG and the GIF) is the drawing `clockFrame` at the time `i / 10`, the conversion of the exact rational number `i/10` to a floating-point number. The number of frames (10) is computed in floating point and is not part of the theorem. |

A fifth picture has a theorem over the real numbers. It belongs to the optional package
[`pilean-mathlib`](../mathlib/README.md), which requires Mathlib, and its files are in
[`mathlib/examples/`](../mathlib/examples/):

| Picture | Theorem |
|---|---|
| ![sine](../mathlib/examples/sine-proved.svg) **The sine** (`sineFigure`) | `sineFigure_spec`: the series' points are the 97 exact samples of the Taylor polynomial of the sine of degree 15 on the grid `−3 + k/16`, `k = 0, …, 96`, converted one by one; and the polyline through those exact samples is vertically within `δ = 1/2000` of the graph of the real sine over `[−3, 3]` (above every `x` of the interval, every point `(x, y)` of the polyline has `\|y − sin x\| ≤ 1/2000`). At this size, 640 × 400, one unit of the ordinate is 143.5 pixels, so `δ` is 0.072 pixel. The last step, from the exact numbers to the pixels, is floating point and tested, not proved. |

The PNG of each has the same name with `.png`; the animation's other files are
`proved-clock.png`, `proved-clock.gif` and `proved-clock-poster.png`.

## Checks against other software

```
lake exe pilean-test --compare-out /tmp/pilean-cmp && python3 -I tools/compare-render.py /tmp/pilean-cmp
lake exe pilean-test --anim-out /tmp/pilean-anim && python3 -I tools/anim-check.py /tmp/pilean-anim
```

The first renders each figure's SVG without its text with macOS's own SVG renderer (`sips`) and
compares it with PILean's PNG of the same nodes, pixel by pixel; the second decodes the animated
files with Python's standard library. The gallery's GIF and APNG files open in macOS's ImageIO
(`sips -g pixelWidth -g format FILE`).
