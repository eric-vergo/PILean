/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILean
import PILean.Trust.Attr
import PILeanVersoManual
import PILeanManual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open PILeanVerso.Manual
open PILeanManual

#doc (Manual) "Combinatorics and Order" =>
%%%
tag := "combinatorics"
%%%

```lean -show
namespace PILeanManual.CombinatoricsGuide
open PILean PILean.Diagram
```

# Diagrams Built from the Object
%%%
tag := "diagram-model"
%%%

{api}`PILean.Diagram` draws finite combinatorial objects (graphs, orders, Young diagrams and
tableaux, permutations, trees, set systems, lattice paths) from the object itself. Each kind has
plain data, the mathematical content: a relation on `Fin n` for a graph or an order, a list of row
lengths for a Young diagram, the one-line notation of a permutation. A pure layout gives exact
rational positions, and a builder draws a {name}`PILean.Diagram.Diagram`: a list of marks, each an
exact shape (a dot, a segment, a rectangle, a circle, a text) tagged with the part of the object
it depicts ({name}`PILean.Diagram.Part`: vertex `i`, edge `(i, j)`, cell `(i, j)`, the entry of a
cell, the strand of a value, a set, a step).

A diagram is drawn as a plane figure ({name}`PILean.Diagram.Diagram.toPlane`): one plane item per
mark, in order, from the mark's exact points, so the house style, both themes, labels through the
text engine, SVG and PNG are those of plane figures.

Every kind has a decidable predicate `Faithful` that reads the diagram back
({name}`PILean.Diagram.Diagram.edges`, {name}`PILean.Diagram.Diagram.cells`,
{name}`PILean.Diagram.Diagram.entries`, …) and compares what it draws with the data, as full lists
and mark by mark, and a theorem that the builder's diagram satisfies it. What the theorems tie is
the exact marks: which parts are drawn, in which order, at which exact positions. Text rendering,
the conversion of rationals to floating point, the fitting of the frame, rasterisation, colours
and style are not part of any theorem; they are the tested code of plane figures.

A figure whose theorem is linked by `figure_proves` is *proved*; any other figure is an
*illustration* (`@[figure illustration]` marks one openly, and `pilean-build --require-standing`
refuses a figure that is neither).

# Graphs
%%%
tag := "diagram-graphs"
%%%

A {name}`PILean.Diagram.FinGraph` is an adjacency relation on `Fin n`, directed or not. The pairs
it draws are {name}`PILean.Diagram.FinGraph.edgePairs`: for a directed graph every `(i, j)` with
`adj i j` (a loop as a circle through its vertex), for an undirected one every `(i, j)` with
`i ≤ j` and `adj i j` or `adj j i`.

* {name}`PILean.Diagram.FinGraph.mem_edgePairs`: `(i, j)` is drawn exactly when `i < n`, `j < n`
  and the pair is drawn by the relation; {name}`PILean.Diagram.FinGraph.edgePairs_nodup`: once.
* {name}`PILean.Diagram.FinGraph.draw_faithful`: at every layout, the diagram's edges are
  `edgePairs` in order, its vertex dots `0, …, n - 1`, and each dot, name and edge is where the
  layout puts it.
* {name}`PILean.Diagram.FinGraph.toGraph_layout_edges`: the layered layout of `PILean.Graph` has
  one route per drawn pair, in order.

The exact layouts are the circle ({name}`PILean.Diagram.Layout.circular`: rational points exactly
on the circle, near the equally spaced angles), the grid and given positions.

```lean
/-- The cycle graph on seven vertices. -/
def cycle7 : FinGraph :=
  { n := 7, adj := fun i j => (i.val + 1) % 7 == j.val || (j.val + 1) % 7 == i.val }

/-- Its diagram, on a circle. -/
def cycle7Diagram : Diagram := cycle7.figure

/-- The diagram as a plane figure. -/
@[figure]
def heptagon : Plane.Figure := cycle7Diagram.toPlane

/-- The figure is the diagram of `cycle7`, which draws exactly its seven edges. -/
theorem heptagon_spec :
    heptagon = cycle7Diagram.toPlane ∧
    cycle7Diagram.edges = [(0, 1), (0, 6), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6)] :=
  ⟨rfl, by decide +kernel⟩

figure_proves heptagon heptagon_spec
```

:::figure PILeanManual.CombinatoricsGuide.heptagon (alt := "Seven dots on a circle labelled 0 to 6, each joined to its two neighbours by grey segments, forming a heptagon.")
:::

# Hasse Diagrams
%%%
tag := "diagram-hasse"
%%%

A {name}`PILean.Diagram.FinPoset` is a relation `le` on `Fin n`. Its diagram draws an edge from
`i` up to `j` exactly when `j` covers `i` ({name}`PILean.Diagram.FinPoset.covers`: `i < j` and
nothing strictly between), the elements in layers by height, the lowest at the bottom, each layer
ordered by the mean position of what it covers.

* {name}`PILean.Diagram.FinPoset.mem_coverPairs`: a pair is drawn exactly when it is a cover.
* {name}`PILean.Diagram.FinPoset.draw_faithful`: the drawn edges are the covering pairs, in order.
* {name}`PILean.Diagram.FinPoset.transGen_covers_iff`: for a partial order, `i < j` exactly when a
  chain of drawn edges leads from `i` to `j`, so the diagram determines the order.

That every edge goes up the page is a property of the layout, tested, not proved.

# Young Diagrams and Tableaux
%%%
tag := "diagram-young"
%%%

A {name}`PILean.Diagram.YoungShape` is a list of row lengths `λ` and a convention: English (row 0
at the top, cell `(i, j)` the unit square `[j, j + 1] × [-(i + 1), -i]`) or French (row 0 at the
bottom). A {name}`PILean.Diagram.Tableau` is a filling, row by row.

* {name}`PILean.Diagram.mem_cellList`: cell `(i, j)` is drawn exactly when `j < λᵢ`;
  {name}`PILean.Diagram.cellList_nodup`: once.
* {name}`PILean.Diagram.YoungShape.draw_faithful`, {name}`PILean.Diagram.Tableau.draw_faithful`:
  the drawn cells are exactly those, in order, each the unit square of its convention; a tableau's
  written entries are its filling, cell by cell.
* {name}`PILean.Diagram.Tableau.IsSemistandard`, {name}`PILean.Diagram.Tableau.IsStandard` are
  decidable.

# Permutations
%%%
tag := "diagram-permutations"
%%%

A {name}`PILean.Diagram.FinPerm` is a permutation in one-line notation, drawn five ways: one-line
and two-line notation, the permutation matrix, the cycle diagram (the functional graph on a circle,
cycle by cycle) and the wiring diagram (strand `i` from `(i, 2)` to `(σ i, 0)`).

* {name}`PILean.Diagram.FinPerm.matrix_faithful`: the marked cells are exactly `(i, σ i)`.
* {name}`PILean.Diagram.FinPerm.mem_cycles_edges`: an arrow `i → j` is drawn exactly when
  `σ i = j`.
* {name}`PILean.Diagram.FinPerm.wiring_crossings`: the pairs of strands that cross, read from
  their drawn ends, are exactly the inversions, so there are as many crossings as inversions
  ({name}`PILean.Diagram.FinPerm.wiring_crossings_length`).

# Trees
%%%
tag := "diagram-trees"
%%%

A {name}`PILean.Diagram.Forest` gives each vertex its parent; a {name}`PILean.Diagram.BinTree` its
left and right child. Both are drawn with the tidy layout of Reingold and Tilford
({name}`PILean.Diagram.tidy`) in exact rationals: subtrees side by side at least 1 apart, each
parent centred over its first and last child, a lone binary child to its side.

* {name}`PILean.Diagram.Forest.mem_edges`: an edge `(p, c)` is drawn exactly when `p` is the parent
  of `c`.

# Set Systems
%%%
tag := "diagram-sets"
%%%

A {name}`PILean.Diagram.SetSystem` is drawn as a Venn diagram of one to three sets or as an
incidence drawing of any number.

* {name}`PILean.Diagram.SetSystem.venn_inside`: every element's name is written at a point inside
  the circle of set `s` exactly when the element belongs to `s` (decided in exact rational
  arithmetic, `|p - c|² < r²`), for every set.
* {name}`PILean.Diagram.SetSystem.incidence_edges`: an edge from element `x` to set `s` is drawn
  exactly when `x ∈ s`.

# Lattice Paths and Boards
%%%
tag := "diagram-paths"
%%%

A {name}`PILean.Diagram.LatticePath` is a list of integer steps; a Dyck path has the steps
`(1, ±1)`. A {name}`PILean.Diagram.Polyomino` is a list of cells; a Ferrers board is the
polyomino of a partition.

* {name}`PILean.Diagram.LatticePath.draw_faithful`: step `k` is drawn from point `k` to point
  `k + 1`, and {name}`PILean.Diagram.LatticePath.point_succ`: point `k + 1` is point `k` plus step
  `k`.
* {name}`PILean.Diagram.LatticePath.ofDyck_step_rises`: step `k` of a Dyck path rises exactly when
  letter `k` is an up step.
* {name}`PILean.Diagram.Polyomino.draw_faithful`: the drawn cells are exactly the polyomino's.

# Mathlib's Objects
%%%
tag := "diagram-mathlib"
%%%

The package `pilean-mathlib` binds each kind to Mathlib's object with a theorem stated in Mathlib's
own definitions: a simple graph's drawn pairs are its edges (`SimpleGraph.Adj`), a digraph's its
arcs, a partial order's drawn edges its covers (`CovBy`, `⋖`), a Young diagram's drawn cells its
cells (`YoungDiagram.cells`), a semistandard tableau's written entries its entries, a
permutation's arrows `a → σ a` and its crossings its inversions, a Dyck word's rising steps its
`U`s, and a finset's members are written inside its circle. Its gallery has a figure of each,
among them the Hasse diagram of the divisors of 60 with the theorem that an edge joins `a` to `b`
exactly when `b / a` is prime.

```lean -show
end PILeanManual.CombinatoricsGuide
```
