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
| **Functions** — `sin x`, `cos x`, `sin x / x`, sampled adaptively (`function-plot`) | ![](function-plot.svg) | ![](function-plot-dark.svg) |
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

## Pictures with a theorem

One picture of each kind whose content is specified by a theorem about the Lean object it was
drawn from (see [`docs/PROOFS.md`](../docs/PROOFS.md): what is proved, what is tested, what is
trusted). The definitions and theorems are in
[`PILeanTest/ProvedExamples.lean`](../PILeanTest/ProvedExamples.lean); each picture is tagged
`@[figure]`. Light style shown; the dark style has the suffix `-dark`.

| Picture | Theorem |
|---|---|
| ![function plot](proved-function.svg) **Function plot** (`provedFunction`) | `provedFunction_spec`: the series' points are the 25 exact samples `(x, f x)` of the cubic `x³ − x` on the grid `−3/2 + k/8`, `k = 0, …, 24`, converted one by one (`Q.toFloat` is where floating point begins); the grid starts at `−3/2`, ends at `3/2` and has the constant step `1/8`; every sample is `(x, f x)` with `x` on the grid. |
| ![data plot](proved-data.svg) **Data plot** (`provedData`) | `provedData_spec`: the line's and the markers' points are the list `residues` of 25 integer pairs, converted point for point, in order; the integers are recovered from the exact points, so none is added, dropped or changed. |
| ![graph](graph-proved.svg) **Graph** (`provedGraph`) | `provedGraph_spec`: the nodes are the numbers 1 to 12, the edges are exactly the pairs `a < b` with `a ∣ b` (23 of them), each once, and the layout draws one route per edge, in order, with the edge's own index and ends (long edges pass through dummy nodes inside the layout and are still one route). |
| ![animation](proved-clock.svg) **Animation** (`provedClock`) | `provedClock_spec`: frame `i` of the animation (10 frames, in the SVG, the APNG and the GIF) is the drawing `clockFrame` at the time `i / 10`, the conversion of the exact fraction `i/10`. |

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
