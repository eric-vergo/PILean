/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plane.Render
import PILean.Plot.Figure
import PILean.Anim.Animation

/-!
# Families of frames

An `Explorer` is a finite family of pictures computed in Lean, for a reader to move through on a web
page: a *parameter axis* (an ordered list of values, each with its picture, shown with a slider), a
*step sequence* (ordered pictures with a short caption each, shown with previous, next and play
controls), or both (a picture for every value and step). Every picture (`ExplorerFrame`) is a
drawing on the vector canvas with its size and style: a plane figure (`ExplorerFrame.ofPlane`), a
plot (`ExplorerFrame.ofPlot`), or any drawing.

The frames are kept in axis-major order: the frame of value `i` and step `j` is
`frames[i * steps + j]`, with one value when there is no axis and one step when there are no
steps. The *poster* is the frame shown first and the one written as the explorer's files (its SVG
and PNG); a page that cannot run the explorer's script shows it with the other frames listed below.

`Explorer.toAnimation` plays a step sequence (at one value of the axis) as an `Animation`.

## Main definitions

* `ExplorerFrame`, `ExplorerFrame.ofPlane`, `ExplorerFrame.ofPlot`.
* `Explorer`, `Explorer.slider`, `Explorer.stepper`, `Explorer.grid`, `Explorer.valid`.
* `Explorer.frameAt`, `Explorer.posterFrame`, `Explorer.toAnimation`.
-/

namespace PILean

/-- One picture of an explorer: a drawing of `width × height` pixels and the style that writes
it (background, font family, text engine). -/
structure ExplorerFrame where
  /-- The drawing. -/
  drawing : Canvas.Shape
  /-- The width in pixels. -/
  width : Float
  /-- The height in pixels. -/
  height : Float
  /-- The style: `background`, `fontFamily` and `text` are used. -/
  style : Style := {}
  deriving Inhabited

namespace ExplorerFrame

/-- The frame of a plane figure (its `auto` labels placed). -/
def ofPlane (fig : Plane.Figure) : ExplorerFrame :=
  let g := fig.autoPlaced
  { drawing := g.draw, width := g.frame.width.round, height := g.frame.height.round,
    style := fig.style }

/-- The frame of a plot. -/
def ofPlot (fig : Plot.Figure) : ExplorerFrame :=
  { drawing := fig.draw, width := fig.width, height := fig.height, style := fig.style }

/-- The frame's SVG nodes, text as SVG text (or as shapes, see `TextMode.forSvg`). -/
def svgNodes (f : ExplorerFrame) (outlines : Bool := false) : Array Svg.Node :=
  f.drawing.render (.forSvg f.style.text f.style.fontFamily outlines)

/-- The frame as an SVG document. -/
def toSvg (f : ExplorerFrame) (outlines : Bool := false) : String :=
  Svg.document f.width f.height (f.svgNodes outlines)

/-- The frame as PNG bytes, text drawn by the style's engine; `none` for a frame of no pixels. -/
def toPng (f : ExplorerFrame) : Option ByteArray :=
  let w := f.width.round.toUInt64.toNat
  let h := f.height.round.toUInt64.toNat
  let im := (Raster.Svg.rasterize w h (f.drawing.render (.shapes f.style.text))
    f.style.background).toImage .rgb
  match im.writePng with
  | .ok b => some b
  | .error _ => none

end ExplorerFrame

/-- A family of frames (see the module docstring). -/
structure Explorer where
  /-- The name of the parameter axis (`r`, "the radius"); empty when there is none. -/
  axisName : String := ""
  /-- The labels of the axis's values, in order (none without an axis). -/
  axisValues : Array String := #[]
  /-- The captions of the steps, in order (none without steps). -/
  stepCaptions : Array String := #[]
  /-- The frames, axis-major: value `i`, step `j` at `i * steps + j`. -/
  frames : Array ExplorerFrame
  /-- The position in `frames` of the poster. -/
  poster : Nat := 0
  deriving Inhabited

namespace Explorer

/-- The number of values of the axis (1 without an axis). -/
def values (x : Explorer) : Nat := max 1 x.axisValues.size

/-- The number of steps (1 without steps). -/
def steps (x : Explorer) : Nat := max 1 x.stepCaptions.size

/-- Whether the explorer is well formed: a frame for every value and step, at least one, and the
poster among them. -/
def valid (x : Explorer) : Bool :=
  x.frames.size == x.values * x.steps && x.frames.size > 0 && x.poster < x.frames.size

/-- The frame of value `i` and step `j`, if there is one. -/
def frameAt (x : Explorer) (i j : Nat) : Option ExplorerFrame := x.frames[i * x.steps + j]?

/-- The poster frame (the first if the poster is out of range; a blank frame for none). -/
def posterFrame (x : Explorer) : ExplorerFrame :=
  x.frames[x.poster]?.getD (x.frames[0]?.getD { drawing := .group #[], width := 1, height := 1 })

/-- A parameter axis named `name`: one frame for each value label, in order; the poster is the
value at position `poster`. -/
def slider (name : String) (values : Array (String × ExplorerFrame)) (poster : Nat := 0) :
    Explorer :=
  { axisName := name, axisValues := values.map (·.1), frames := values.map (·.2), poster }

/-- A step sequence: one frame for each caption, in order; the poster is the first step. -/
def stepper (steps : Array (String × ExplorerFrame)) (poster : Nat := 0) : Explorer :=
  { stepCaptions := steps.map (·.1), frames := steps.map (·.2), poster }

/-- An axis and a step sequence together: `frame i j` for value `i` and step `j`. -/
def grid (name : String) (values stepCaptions : Array String)
    (frame : Nat → Nat → ExplorerFrame) (poster : Nat := 0) : Explorer :=
  { axisName := name, axisValues := values, stepCaptions,
    frames := (List.range (max 1 values.size)).toArray.flatMap fun i =>
      (List.range (max 1 stepCaptions.size)).toArray.map fun j => frame i j,
    poster }

/-- The steps at value `i` played as an animation, `secondsPerStep` each, looping, the first step
as poster; the size and style are the poster frame's. -/
def toAnimation (x : Explorer) (i : Nat := 0) (secondsPerStep : Float := 1) : Animation :=
  let p := x.posterFrame
  let n := x.steps
  let step := max 0.05 secondsPerStep
  { width := p.width.round.toUInt64.toNat, height := p.height.round.toUInt64.toNat,
    fps := max 1 (1 / step).ceil.toUInt64.toNat, duration := step * n.toFloat,
    frame := fun t =>
      let j := min (n - 1) (t / step).floor.toUInt64.toNat
      ((x.frameAt i j).getD p).drawing,
    posterTime := some 0, background := p.style.background, fontFamily := p.style.fontFamily,
    text := p.style.text }

end Explorer

end PILean
