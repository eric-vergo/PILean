/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plane.Render
import PILean.Plot.Check
import PILean.Anim.Animation

/-!
# Families of frames

An `Explorer` is a finite family of pictures computed in Lean, for a reader to move through on a web
page. It has up to two dimensions: a *parameter axis* (an ordered list of values, each with its
picture, shown with a slider) and *steps* (shown with previous, next and play controls). The steps
are either a sequence with a short caption each, or the values of a second parameter
(`Explorer.stepName` names it), which the page shows with a slider beside the controls. Every
picture (`ExplorerFrame`) is a drawing on the vector canvas with its size and style: a plane figure
(`ExplorerFrame.ofPlane`), a plot (`ExplorerFrame.ofPlot`), or any drawing.

A figure as a function of one or two parameters over a finite grid of values is
`Explorer.family` (one parameter, played or shown with a slider) or `Explorer.family₂` (two: the
first on the slider, the second played), from `ExplorerParam`s; every frame is the function's value
at its point of the grid (`family₂_frames`), computed when the explorer is built, so the page only
shows frames it was given.

The frames are kept in axis-major order: the frame of value `i` and step `j` is
`frames[i * steps + j]`, with one value when there is no axis and one step when there are no
steps. The *poster* is the frame shown first and the one written as the explorer's files (its SVG,
PNG and PDF); a page that cannot run the explorer's script shows it first, with the other frames
below.

**Caps.** An explorer has at most `Explorer.maxFrames` frames (`Explorer.valid`), and the SVG of
its frames together, which a page puts inline, at most `Explorer.maxBytes` bytes; one beyond
either is not rendered (`PILean.Trust`'s outputs fail with a message).

`Explorer.toAnimation` plays the steps (at one value of the axis) as an `Animation`, every step as
long as the others.

Every frame keeps the problems the checks of its figure report (`ExplorerFrame.problems`, with
the figure's checks level): a build reports them as warnings, frame by frame
(`Explorer.problems`), or refuses to render the explorer when a frame whose level is `fail` has
some (`Explorer.problemsFail`).

## Main definitions

* `ExplorerFrame`, `ExplorerFrame.ofPlane`, `ExplorerFrame.ofPlot`.
* `Explorer`, `Explorer.slider`, `Explorer.stepper`, `Explorer.grid`, `Explorer.valid`.
* `ExplorerParam`, `Explorer.family`, `Explorer.family₂`, `Explorer.family_frames`,
  `Explorer.family₂_frames`, `Explorer.mem_family_frames`, `Explorer.mem_family₂_frames`.
* `Explorer.maxFrames`, `Explorer.maxBytes`, `Explorer.svgBytes`.
* `Explorer.frameAt`, `Explorer.posterFrame`, `Explorer.toAnimation`, `Explorer.stepTiming`.
* `Explorer.problems`, `Explorer.problemsFail`, `Explorer.frameName`.
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
  /-- Whether the image is composited in sRGB (plane figures) rather than linear light (plots). -/
  srgb : Bool := false
  /-- Whether SVG text is drawn as shapes. -/
  textAsShapes : Bool := false
  /-- The problems the checks of the figure the frame is drawn from report (the layout checks of
  a plane figure, the labelling checks of a plot), unless its level is `ignore`. -/
  problems : Unit → Array String := fun _ => #[]
  /-- The checks level of that figure: whether its problems are warnings or stop the
  rendering. -/
  checks : CheckLevel := .warn
  deriving Inhabited

namespace ExplorerFrame

/-- The frame of a plane figure (its `auto` labels placed), with its layout problems. -/
def ofPlane (fig : Plane.Figure) : ExplorerFrame :=
  let g := fig.autoPlaced
  { drawing := g.draw, width := g.frame.width.round, height := g.frame.height.round,
    style := fig.style, srgb := true, textAsShapes := fig.textAsShapes,
    problems := fun _ => fig.checkMessages, checks := fig.checks }

/-- The frame of a plot, with its labelling problems. -/
def ofPlot (fig : Plot.Figure) : ExplorerFrame :=
  { drawing := fig.draw, width := fig.width, height := fig.height, style := fig.style,
    problems := fun _ => fig.checkMessages, checks := fig.checks }

/-- The frame's SVG nodes, text as SVG text (or as shapes, see `TextMode.forSvg`). -/
def svgNodes (f : ExplorerFrame) (outlines : Option Bool := none) : Array Svg.Node :=
  f.drawing.render (.forSvg f.style.text f.style.fontFamily (outlines.getD f.textAsShapes))

/-- The frame as an SVG document. -/
def toSvg (f : ExplorerFrame) (outlines : Option Bool := none) : String :=
  Svg.document f.width f.height (f.svgNodes outlines)

/-- The frame as PNG bytes, text drawn by the style's engine; `none` for a frame of no pixels. -/
def toPng (f : ExplorerFrame) : Option ByteArray :=
  let w := f.width.round.toUInt64.toNat
  let h := f.height.round.toUInt64.toNat
  let im := (Raster.Svg.rasterize w h (f.drawing.render (.shapes f.style.text))
    f.style.background (space := if f.srgb then .srgb else .linear)).toImage .rgb
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
  /-- The captions of the steps, in order (none without steps): a caption each, or the labels of
  the values of the parameter `stepName`. -/
  stepCaptions : Array String := #[]
  /-- The name of the parameter whose values the steps are (`n`, "the number of steps"); empty
  when the steps are a sequence with captions. -/
  stepName : String := ""
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

/-- The most frames an explorer may have. -/
def maxFrames : Nat := 400

/-- The most bytes the SVG of an explorer's frames may take together (8 MiB): what a page puts
inline for it. -/
def maxBytes : Nat := 8 * 1024 * 1024

/-- Whether the explorer is well formed: a frame for every value and step, at least one and at
most `maxFrames`, and the poster among them. -/
def valid (x : Explorer) : Bool :=
  x.frames.size == x.values * x.steps && x.frames.size > 0 && x.frames.size ≤ maxFrames &&
    x.poster < x.frames.size

/-- The size in bytes of the SVG of every frame together (`ExplorerFrame.toSvg`). -/
def svgBytes (x : Explorer) : Nat :=
  x.frames.foldl (fun n f => n + f.toSvg.utf8ByteSize) 0

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

/-- How frame `k` is named in a message: its position, its value and its step (or the value of
the second parameter). -/
def frameName (x : Explorer) (k : Nat) : String :=
  let i := k / x.steps
  let j := k % x.steps
  let value := match x.axisValues[i]? with
    | some v => s!", {x.axisName} = {v}"
    | none => ""
  let step := match x.stepCaptions[j]? with
    | some c => if x.stepName.isEmpty then s!", step {j + 1} “{c}”" else s!", {x.stepName} = {c}"
    | none => ""
  s!"frame {k}{value}{step}"

/-! ### Families over a grid of parameters -/

/-- A parameter of an explorer: its name, its values in order and how a value is written. -/
structure _root_.PILean.ExplorerParam (α : Type) where
  /-- The parameter's name, as the page writes it (`n`, `ω₂`). -/
  name : String
  /-- The values, in order. -/
  values : Array α
  /-- How a value is written on the page and in messages. -/
  label : α → String

/-- A figure as a function of one parameter: one frame `f v` for each value `v` of `p`, in
order. With `play` (the default) the values are steps, shown with a slider and previous, play and
next controls; without, they are a parameter axis with a slider alone. The poster is the value at
position `poster`. -/
def family {α : Type} (p : ExplorerParam α) (f : α → ExplorerFrame) (play : Bool := true)
    (poster : Nat := 0) : Explorer :=
  if play then
    { stepName := p.name, stepCaptions := p.values.map p.label, frames := p.values.map f, poster }
  else
    { axisName := p.name, axisValues := p.values.map p.label, frames := p.values.map f, poster }

/-- A figure as a function of two parameters: one frame `f a b` for every value `a` of `p` (the
slider) and `b` of `q` (played, and shown with a slider too), axis-major. The poster is the frame
at position `poster`. -/
def family₂ {α β : Type} (p : ExplorerParam α) (q : ExplorerParam β) (f : α → β → ExplorerFrame)
    (poster : Nat := 0) : Explorer :=
  { axisName := p.name, axisValues := p.values.map p.label, stepName := q.name,
    stepCaptions := q.values.map q.label,
    frames := p.values.flatMap fun a => q.values.map (f a), poster }

/-- The frames of a family of one parameter are its function at the values, in order. -/
theorem family_frames {α : Type} (p : ExplorerParam α) (f : α → ExplorerFrame) (play : Bool)
    (poster : Nat) : (family p f play poster).frames = p.values.map f := by
  unfold family; split <;> rfl

/-- The frames of a family of two parameters are its function at the points of the grid,
axis-major. -/
theorem family₂_frames {α β : Type} (p : ExplorerParam α) (q : ExplorerParam β)
    (f : α → β → ExplorerFrame) (poster : Nat) :
    (family₂ p q f poster).frames = p.values.flatMap fun a => q.values.map (f a) := rfl

/-- Every frame of a family of one parameter is its function at one of the values, and every
value has its frame. -/
theorem mem_family_frames {α : Type} (p : ExplorerParam α) (f : α → ExplorerFrame) (play : Bool)
    (poster : Nat) (fr : ExplorerFrame) :
    fr ∈ (family p f play poster).frames ↔ ∃ a ∈ p.values, f a = fr := by
  rw [family_frames, Array.mem_map]

/-- Every frame of a family of two parameters is its function at a point of the grid, and every
point of the grid has its frame. -/
theorem mem_family₂_frames {α β : Type} (p : ExplorerParam α) (q : ExplorerParam β)
    (f : α → β → ExplorerFrame) (poster : Nat) (fr : ExplorerFrame) :
    fr ∈ (family₂ p q f poster).frames ↔ ∃ a ∈ p.values, ∃ b ∈ q.values, f a b = fr := by
  rw [family₂_frames, Array.mem_flatMap]
  simp only [Array.mem_map]

/-- The problems of the frames (`ExplorerFrame.problems`) whose level is not `ignore`, each with
the frame's name, in frame order. -/
def problems (x : Explorer) : Array String :=
  x.frames.zipIdx.flatMap fun (f, k) =>
    if f.checks == .ignore then #[] else (f.problems ()).map (s!"{x.frameName k}: " ++ ·)

/-- Whether a frame whose checks level is `fail` has problems, which stops the explorer from
being rendered. -/
def problemsFail (x : Explorer) : Bool :=
  x.frames.any fun f => f.checks == .fail && !(f.problems ()).isEmpty

/-- The frame rate and the number of frames per step that play steps of `s` seconds (at least
0.05): for the first `k = 1, …, 10` frames per step whose rate `fps = round (k / s)` (between 1
and 60) makes a step of `k / fps` seconds within 2 % of `s`, `(fps, k)`; the closest of them
otherwise. Every step then lasts exactly `k / fps`, the same for all. -/
def stepTiming (s : Float) : Nat × Nat := Id.run do
  let s := max 0.05 s
  let mut best : Nat × Nat := (1, 1)
  let mut bestErr : Float := 1e300
  for k in [1:11] do
    let fps := max 1 (min 60 (k.toFloat / s).round.toUInt64.toNat)
    let err := ((k.toFloat / fps.toFloat) - s).abs / s
    if err ≤ 0.02 then return (fps, k)
    if err < bestErr then
      best := (fps, k)
      bestErr := err
  return best

/-- The steps at value `i` played as an animation, about `secondsPerStep` each and every step as
long as the others (`stepTiming`), looping, the first step as poster; the size, style,
compositing and lettering are the poster frame's, and the problems are those of the frames
played. -/
def toAnimation (x : Explorer) (i : Nat := 0) (secondsPerStep : Float := 1) : Animation :=
  let p := x.posterFrame
  let n := x.steps
  let (fps, k) := stepTiming secondsPerStep
  let played := (List.range n).toArray.filterMap fun j => (x.frameAt i j).map ((i * n + j), ·)
  { width := p.width.round.toUInt64.toNat, height := p.height.round.toUInt64.toNat,
    fps, duration := (n * k).toFloat / fps.toFloat,
    frame := fun t =>
      let f := (t * fps.toFloat).round.toUInt64.toNat
      ((x.frameAt i (min (n - 1) (f / k))).getD p).drawing,
    posterTime := some 0, background := p.style.background, fontFamily := p.style.fontFamily,
    text := p.style.text, srgb := p.srgb, textAsShapes := p.textAsShapes,
    problems := fun _ => played.flatMap fun (k, f) =>
      if f.checks == .ignore then #[] else (f.problems ()).map (s!"{x.frameName k}: " ++ ·),
    problemsFail := played.any fun (_, f) => f.checks == .fail && !(f.problems ()).isEmpty }

end Explorer

end PILean
