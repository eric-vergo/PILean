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

#doc (Manual) "Algebra and Categories" =>
%%%
tag := "algebra"
%%%

```lean -show
namespace PILeanManual.AlgebraGuide
open PILean PILean.Diagram
```

The modules `PILean.Diagram.CommDiagram`, `PILean.Diagram.Group` and `PILean.Diagram.Quiver`
draw commutative diagrams, Cayley tables and graphs of finite groups, and quivers from their
data, as the diagrams of {ref "combinatorics"}[Combinatorics and Order] do: exact marks tagged with
the part they depict, a decidable `Faithful` predicate, and a theorem that the builder satisfies
it. These kinds account for every mark *by class*: the predicate takes the marks of each class of
part (objects, arrows, 2-cells; cells, entries, headings, decorations), requires each list to be
exactly the builder's (shape, exact position and colour role), and refuses a mark of any other
part.

# Commutative Diagrams
%%%
tag := "algebra-commutative"
%%%

A {name}`PILean.Diagram.CommDiagram` has objects (labels at exact positions, one unit between
neighbours on a grid), arrows ({name}`PILean.Diagram.CDArrow`: source, target, label, style,
bend), optional 2-cells, and *claims*: pairs of paths of arrows from one object said to have the
same composite. The styles ({name}`PILean.Diagram.ArrowStyle`) are the conventions of the
subject: `↣` for a monomorphism (a second tip at the tail), `↠` for an epimorphism (two tips),
`≅` written beside an isomorphism, a hook `↪` for an inclusion, a dashed arrow, a double line for
an equality, a bar `↦`, and a line without a tip.

An arrow's body runs from where the segment between the objects' centres leaves the box of the
first label to where it enters the box of the second; a bent arrow is a quadratic Bézier curve and
a loop a cubic one, both sampled at exact rational parameters; parallel straight arrows stand
side by side. The label is written beside the middle of the body, on the arrow's left (or right,
`swap`).

* {name}`PILean.Diagram.CommDiagram.draw_faithful`: the drawn arrow bodies
  ({name}`PILean.Diagram.Diagram.arrows`) are exactly `(k, src, tgt)` for the data's arrows, in
  order; the texts of the arrows are exactly their labels; every tip, hook, bar, 2-cell and
  object label is the builder's, at its exact position.
* {name}`PILean.Diagram.FinMaps.Commutes`: for maps between finite sets given by their tables,
  whether they fit the arrows and the two paths of every claim agree at every element.
* {name}`PILean.Diagram.FinMaps.StylesHold`: whether the marks of the styles are true of the maps:
  an arrow drawn `↣` or `↪` is injective, `↠` surjective, `≅` bijective, `=` the identity.

That a diagram commutes is a statement about the object; the picture carries it only through the
claims, which these decide. The package `pilean-mathlib` states both for morphisms of a category:
the drawn square commutes exactly when it is a `CommSq`, and the drawing `0 → A ↣ B ↠ C → 0` of
a short complex has its marks justified and the complex exact exactly when the complex is
`ShortExact` ({ref "algebra-mathlib"}[below]).

```lean
/-- Reduction modulo `m` on `{0, …, n - 1}`, as a table. -/
def reduction (n m : Nat) : Array Nat := ((List.range n).map (· % m)).toArray

/-- The square of reductions of `ℤ/12`. -/
def square : CommDiagram where
  objects := #["ℤ/12", "ℤ/6", "ℤ/4", "ℤ/2"]
  pos := #[(0, 0), (1, 0), (0, -1), (1, -1)]
  arrows := [{ src := 0, tgt := 1, label := "π₆", style := .epi },
    { src := 0, tgt := 2, label := "π₄", style := .epi, swap := true },
    { src := 1, tgt := 3, label := "π₂", style := .epi },
    { src := 2, tgt := 3, label := "π₂", style := .epi, swap := true }]
  paths := [(0, [0, 2], [1, 3])]

/-- The reductions. -/
def maps : FinMaps where
  card := #[12, 6, 4, 2]
  fn := #[reduction 12 6, reduction 12 4, reduction 6 2, reduction 4 2]

/-- The square as a plane figure. -/
@[figure]
def squareFigure : Plane.Figure := square.figure.toPlane

/-- The figure is the square's diagram, whose arrows are written out; the reductions commute and
are surjective, as their tips say. -/
theorem squareFigure_spec :
    squareFigure = square.figure.toPlane ∧
    square.figure.arrows = [(0, 0, 1), (1, 0, 2), (2, 1, 3), (3, 2, 3)] ∧
    maps.Commutes square = true ∧ maps.StylesHold square = true :=
  ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩

figure_proves squareFigure squareFigure_spec
```

:::figure PILeanManual.AlgebraGuide.squareFigure (alt := "A square: ℤ/12 at the top left with two-headed arrows to ℤ/6 on its right and ℤ/4 below it, both with two-headed arrows to ℤ/2 at the bottom right; the arrows are labelled π₆, π₄, π₂ and π₂.")
:::

# Finite Groups
%%%
tag := "algebra-groups"
%%%

A {name}`PILean.Diagram.FinMagma` is a binary operation on `Fin n` given by its table. Whether it
is a group is checked, not assumed: {name}`PILean.Diagram.FinMagma.isGroup` decides associativity,
an identity and inverses on the table, and {name}`PILean.Diagram.FinMagma.isCommutative` and
{name}`PILean.Diagram.FinMagma.centre` decide the rest of what a table shows.

* The Cayley table ({name}`PILean.Diagram.FinMagma.table`) writes in cell `(a, b)` the name of
  `a * b`, tinted in the colour of `a * b` (one of twelve series colours, light and dark);
  {name}`PILean.Diagram.FinMagma.entries_table`: the entry of cell `(a, b)` is the name of
  `a * b`, and every cell has its entry; {name}`PILean.Diagram.FinMagma.FaithfulTable` accounts
  for the cells, their colours, the entries, the headings and the two rules.
* The Cayley graph ({name}`PILean.Diagram.FinMagma.cayley`) for a list of generators is a
  commutative diagram with an arrow `g → g * s` in the colour of each generator `s`, and one line
  without a tip for each pair `{g, g s}` of an involution;
  {name}`PILean.Diagram.FinMagma.mem_cayleyArrows` says which arrows the data has.

```lean
/-- `ℤ/5` under addition. -/
def z5 : FinMagma :=
  { n := 5, mul := fun a b => ⟨(a.val + b.val) % 5, Nat.mod_lt _ (by decide)⟩ }

/-- Its Cayley table. -/
@[figure]
def z5Table : Plane.Figure := z5.tableFigure.toPlane

/-- The table is a group, commutative, and its entries are the sums. -/
theorem z5Table_spec :
    z5Table = z5.tableFigure.toPlane ∧ z5.isGroup = true ∧ z5.isCommutative = true ∧
    z5.FaithfulTable z5.tableFigure :=
  ⟨rfl, by decide +kernel, by decide +kernel, z5.tableFigure_faithful (by decide)⟩

figure_proves z5Table z5Table_spec
```

:::figure PILeanManual.AlgebraGuide.z5Table (alt := "The addition table of the integers modulo 5: headings 0 to 4 along the top and the left, and in each cell the sum modulo 5, tinted in the colour of the sum, so that the colours run in diagonal bands.")
:::

A lattice of subgroups is a Hasse diagram ({ref "diagram-hasse"}[Hasse Diagrams]) whose order is
inclusion; a {name}`PILean.Diagram.FinPoset` can mark elements, whose dots are then drawn in an
accent colour ({name}`PILean.Diagram.FinGraph.ink_of_faithful`), and the package `pilean-mathlib`
ties that mark to `Subgroup.Normal`.

# Quivers
%%%
tag := "algebra-quivers"
%%%

A {name}`PILean.Diagram.FinQuiver` has vertices, arrows (several between two vertices, and loops)
and optionally a dimension vector, with which each vertex is labelled by its dimension. It is
drawn as a commutative diagram without claims: parallel arrows side by side with their labels
outside, loops growing in size, hanging down at vertices below the middle.
{name}`PILean.Diagram.FinQuiver.arrows_toCommDiagram`: the drawn arrows are the quiver's.

# Mathlib's Objects
%%%
tag := "algebra-mathlib"
%%%

The package `pilean-mathlib` realises a commutative diagram in a category (an object for each
object and, for each arrow, a morphism between the objects of its ends). For such a realisation
`Commutes` says that the composites of the two paths of every claim are equal, and `StylesHold`
that `↣` and `↪` are `Mono`, `↠` `Epi`, `≅` `IsIso` and `=` an identity. The drawn square of
`f`, `g`, `h`, `i` commutes exactly when `CommSq f g h i`, the triangle exactly when `f ≫ g = h`,
and the drawing `0 → A ↣ B ↠ C → 0` of a short complex `S` has its marks justified and `S`
exact exactly when `S.ShortExact`.

For a group enumerated by `e : Fin n ≃ G` the table's cell `(a, b)` holds `e a * e b`, the table
is a group, it is symmetric exactly when `G` is commutative, and its centre is
`Subgroup.center G`. The package's gallery draws the Cayley table, a Cayley graph and the lattice
of subgroups of the dihedral group of order 8, with the theorem that the ten drawn subgroups are
all its subgroups, each once, that the edges are the covers `⋖`, and that a dot is in colour
exactly when its subgroup is normal.

# What Is Proved and What Is Tested
%%%
tag := "algebra-proved"
%%%

Proved: which marks are drawn, of which part, in which order, at which exact rational positions,
with which colour role; that the texts are the labels and the names of the products; on finite
data, commutation, the marks of the arrows' styles and the group axioms; in `pilean-mathlib`,
the same for Mathlib's morphisms and groups. Tested: that the pictures are good (arrows clear of
the labels, parallel arrows apart, the layout checks of plane figures in both themes), the
estimate of a label's box from its length, the text itself (lettering, or LeAnTeX's typesetting
with the package `pilean-leantex`), the colours' values, floating point and the pixels.

```lean -show
end PILeanManual.AlgebraGuide
```
