/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILean
import PILean.Trust.Attr
import PILeanVersoManual
import PILeanManual.Meta
import PILeanManual.Pictures

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open PILeanVerso.Manual
open PILeanManual

#doc (Manual) "The Canvas and Paths" =>
%%%
tag := "canvas"
%%%

```lean -show
namespace PILeanManual.CanvasGuide
open PILean
```

# Geometry
%%%
tag := "geometry"
%%%

Coordinates are those of SVG and of raster images: `x` grows to the right, `y` downwards, one
unit a pixel at the identity transform. {api}`PILean.Geometry` has the
{name}`PILean.Point`, the affine transform {name}`PILean.Affine` (SVG's
`matrix(a b c d e f)`) and the axis-aligned {name}`PILean.Box`.

```lean (name := geomEx)
#eval (Affine.rotate (3.141592653589793 / 2)).apply ⟨1, 0⟩
#eval ((Affine.translate 10 0).comp (Affine.scale 2 2)).apply ⟨1, 1⟩
#eval (Box.ofSize 0 0 40 20).contains ⟨10, 10⟩
```

```leanResult geomEx
```

# Paths
%%%
tag := "paths"
%%%

A {name}`PILean.Path` is a list of commands: move, line, quadratic and cubic Bézier, close. It is
a value, built with {name}`PILean.Path.moveTo`, {name}`PILean.Path.lineTo`,
{name}`PILean.Path.quadTo`, {name}`PILean.Path.cubicTo` and {name}`PILean.Path.close`, or taken
from the common shapes ({name}`PILean.Path.rect`, {name}`PILean.Path.roundedRect`,
{name}`PILean.Path.ellipse`, {name}`PILean.Path.polyline`, and the circular arcs
{name}`PILean.Path.arc` and {name}`PILean.Path.arcTo`: cubic pieces of at most a quarter turn,
within {name}`PILean.Path.arcError` of the circle, at most 0.0273 % of the radius). A path can be
transformed ({name}`PILean.Path.transform`; Béziers are affine invariant, so only the points
move), bounded and flattened:

```lean (name := pathEx)
def wave : Path :=
  Path.empty |>.moveTo ⟨0, 50⟩ |>.cubicTo ⟨30, 0⟩ ⟨70, 100⟩ ⟨100, 50⟩

#eval wave.controlBounds.map fun b => (b.x0, b.y0, b.x1, b.y1)
#eval wave.bounds.map fun b => (b.y0, b.y1)
#eval (wave.flatten 0.1).map (·.points.size)
#eval (wave.flatten 0.001).map (·.points.size)
```

```leanResult pathEx
```

{name}`PILean.Path.controlBounds` is the box of every point, control points included;
{name}`PILean.Path.bounds` is the tight box, with the extrema of the curves. Flattening cuts each
curve into equal steps of its parameter, as few as keep every point of the polyline within the
tolerance of the curve (the step count follows from the curve's second differences), and never
more than {name}`PILean.Path.maxPieces` per curve, so that a huge or non-finite curve costs a
bounded amount of work.

# Drawings
%%%
tag := "shapes"
%%%

The vector canvas ({api}`PILean.Canvas`) is a small composable drawing model. A
{name}`PILean.Canvas.Shape` is a path with a fill and a stroke, a line of text, or a group of
shapes under a transformation, at an opacity, clipped to a path. Fills are colours or gradients
({name}`PILean.Raster.Paint`: linear or radial, interpolated in linear light); strokes
({name}`PILean.Canvas.Line`) have a colour, a width, caps, joins and dashes.

A drawing is written as SVG ({name}`PILean.Canvas.Shape.toSvg`) or drawn as an image
({name}`PILean.Canvas.Shape.toImage`, {name}`PILean.Canvas.Shape.toPng`) from the same SVG nodes
({name}`PILean.Canvas.Shape.render`), so the two agree. Transformations are applied to the
geometry when the drawing is written: the SVG has no `transform` attributes (except to rotate
text), so every renderer draws it alike. Ids of clips and gradients are numbered in drawing order,
so the output is deterministic.

```lean
open PILean.Canvas in
/-- Paths, a gradient, a clipped group under a rotation, a dashed stroke and text. -/
@[figure]
def shapes : PILeanManual.Drawing where
  width := 480
  height := 200
  draw st :=
    let c0 := st.palette[0]!
    let c1 := st.palette[1]!
    let c2 := st.palette[2]!
    .group #[
      .path (rect 0 0 480 200) (some (.solid st.background)),
      .path (Path.roundedRect 20 30 120 120 14)
        (some (.paint (.linear ⟨20, 0⟩ ⟨140, 0⟩ #[⟨0, c0⟩, ⟨1, c2⟩]))),
      .group #[.path (circle ⟨240, 90⟩ 60) (some (.solid c1))]
        (transform := (Affine.translate 240 90).comp
          ((Affine.rotate 0.4).comp (Affine.translate (-240) (-90))))
        (clip := some (rect 180 60 120 60)),
      .path (wave.transform (Affine.translate 340 40))
        (line := some { ink := st.inkPrimary, width := 3, cap := "round", dash := #[8, 6] }),
      .text "a clipped, rotated disc" ⟨240, 180⟩ 12 st.inkSecondary .middle]
```

:::figure PILeanManual.CanvasGuide.shapes (alt := "From left to right: a rounded square filled with a gradient from blue to green, a band of an orange disc cut out by a rotated clip rectangle with the caption 'a clipped, rotated disc' under it, and a dashed S-shaped curve.")
:::

A shape can carry metadata ({name}`PILean.Canvas.ShapeInfo`, through
{name}`PILean.Canvas.Shape.tagged`): an accessible title and description, CSS classes, an id and
the name of a Lean declaration. SVG writes them as a `g` with `title` and `desc` children and
`class`, `id` and `data-lean-decl` attributes; an image draws the shape alone. Ids and classes
are reduced to ASCII letters, digits, `_`, `-` and `.`.

Text in a drawing is a placeholder that the output resolves ({name}`PILean.Canvas.TextMode`): SVG
text in a font family, or shapes from a text engine, which is how text reaches images
({ref "text"}[Text Engines]).

# SVG
%%%
tag := "svg"
%%%

Every SVG document PILean writes goes through one writer ({api}`PILean.Svg`): a typed tree of
elements ({name}`PILean.Svg.Node`), written by {name}`PILean.Svg.render` with every number
through one formatter ({name}`PILean.fmtNum`: a fixed number of decimals, no exponent,
magnitudes beyond 10¹² clamped, a non-finite value written `0`), so the output is byte for byte the
same on every run. Text and attribute values are escaped, and
characters XML cannot carry are dropped:

```lean (name := svgEx)
#eval escapeText "x < y & \"z\""
#eval fmtNum 1e21
#eval fmtNum (2 / 3)
#eval validName "on load"
```

```leanResult svgEx
```

{name}`PILean.Svg.isInert` answers whether an SVG document can be shown in a web page without
running script, loading anything from outside the document or carrying event handlers. It is a
strict, bounded scan of the text, not an XML parser: it accepts what PILean writes (figures,
graphs, animations, files with a source record) and refuses anything else that could be active
(the rules are in `docs/TRUST.md`, "Inert SVG"). It is tested against hand-written hostile
documents, not proved.

```lean (name := inertEx)
#eval Svg.isInert (shapes.svg Style.light)
#eval Svg.inertProblem? "<svg xmlns=\"http://www.w3.org/2000/svg\"><script/></svg>"
```

```leanResult inertEx
```
