/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plot.Figure
import PILean.Plane
import PILean.Explorer
import PILean.Graph.Draw
import PILean.Anim.Animation

/-!
# Renderable figures

`ToOutputs α` says how a value of `α` becomes image files: a list of `Output`s, each with a file
name suffix, a format, the bytes (computed on demand) and the *specification encoding*, the bytes
a fingerprint covers (see `docs/TRUST.md`).

The specification of an output is the SVG document PILean's deterministic writer makes from the
drawing, before any source information is added: for a figure, a graph and an animation the SVG
output, the animation's APNG and GIF (the SVG of all frames) and its poster (the SVG of the poster
frame); for a PNG the SVG with text as shapes, which is the drawing the PNG is rasterised from.
It covers the values a function takes where the figure samples it, not the function's code.

## Main definitions

* `Format`, `Output`, `ToOutputs`
* `InlineSvg`, `FrameSet`: pictures and families of frames a web page puts inline
* instances for `Plot.Figure`, `Plane.Figure`, `Explorer`, `Graph`, `GraphFigure` and
  `Animation`
-/

namespace PILean.Trust

/-- The format of an output file. -/
inductive Format where
  /-- A Scalable Vector Graphics document. -/
  | svg
  /-- A PNG image. -/
  | png
  /-- An animated PNG. -/
  | apng
  /-- A GIF animation. -/
  | gif
deriving BEq, Repr, Inhabited

/-- The format's name, as written in a manifest: `svg`, `png`, `apng` or `gif`. -/
def Format.name : Format → String
  | .svg => "svg"
  | .png => "png"
  | .apng => "apng"
  | .gif => "gif"

/-- The extension of the files of a format (without the dot): an animated PNG is a `png` file. -/
def Format.ext : Format → String
  | .svg => "svg"
  | .png => "png"
  | .apng => "png"
  | .gif => "gif"

/-- The format with a given name, if there is one. -/
def Format.ofName? : String → Option Format
  | "svg" => some .svg
  | "png" => some .png
  | "apng" => some .apng
  | "gif" => some .gif
  | _ => none

/-- A picture a web page can put inline (as an `svg` element) instead of a file: its size in pixels
and the SVG nodes of its body, as `Svg.document` writes them. -/
structure InlineSvg where
  /-- The width in pixels. -/
  width : Float
  /-- The height in pixels. -/
  height : Float
  /-- The nodes of the document's body. -/
  nodes : Array Svg.Node
  deriving Inhabited

/-- The SVG document of an inline picture. -/
def InlineSvg.document (i : InlineSvg) : String := Svg.document i.width i.height i.nodes

/-- The inline frames of an `Explorer` for a web page: the axis, the steps, the frames
(axis-major, as in `Explorer`) and the poster's position. -/
structure FrameSet where
  /-- The name of the parameter axis; empty for none. -/
  axisName : String := ""
  /-- The labels of the axis's values. -/
  axisValues : Array String := #[]
  /-- The captions of the steps. -/
  stepCaptions : Array String := #[]
  /-- The frames. -/
  frames : Array InlineSvg
  /-- The poster's position in `frames`. -/
  poster : Nat := 0
  deriving Inhabited

/-- One file a figure is rendered to. -/
structure Output where
  /-- The suffix of the file's stem, for instance `""`, `"-dark"` or `"-poster"`. -/
  name : String
  /-- The file's format. -/
  format : Format
  /-- The file's bytes, without source information; an error message if it cannot be made. -/
  bytes : Unit → Except String ByteArray
  /-- The canonical encoding of what is drawn, which the fingerprint covers. -/
  spec : ByteArray
  /-- The identity of the text engine the output is drawn with (`TextEngine.id`), which the
  fingerprint covers through `rendererWith`; empty for the built-in lettering. -/
  textEngine : String := ""
  /-- For an SVG output: the same picture as nodes, for a page that puts it inline. -/
  inline : Unit → Option InlineSvg := fun _ => none
  /-- For the poster of a family of frames: every frame, for a page that shows them inline. -/
  frames : Unit → Option FrameSet := fun _ => none
  /-- Problems of the figure's layout a build should report as warnings (on one output of a
  figure, so that they are reported once). -/
  problems : Unit → Array String := fun _ => #[]

/-- An empty SVG output that cannot be rendered (for indexing arrays of outputs). -/
instance : Inhabited Output :=
  ⟨{ name := "", format := .svg, bytes := fun _ => .error "no output", spec := .empty }⟩

/-- Values that PILean can render to files. -/
class ToOutputs (α : Type) where
  /-- The files a value is rendered to, in a fixed order. -/
  outputs : α → Array Output

/-- Figures: the SVG, and the PNG when the figure has pixels. -/
instance : ToOutputs Plot.Figure where
  outputs fig :=
    #[{ name := "", format := .svg, bytes := fun _ => .ok fig.toSvg.toUTF8,
        spec := fig.toSvg.toUTF8, textEngine := fig.style.text.id,
        inline := fun _ => some
          { width := fig.width, height := fig.height,
            nodes := fig.draw.render (.forSvg fig.style.text fig.style.fontFamily) } },
      { name := "", format := .png,
        bytes := fun _ => match fig.toPng with
          | some b => .ok b
          | none => .error "the figure has no pixels",
        spec := (fig.toSvg (outlines := true)).toUTF8, textEngine := fig.style.text.id }]

/-- The bytes of a plane figure's output, or the figure's layout problems as an error when its
`checks` level is `fail` and it has some. -/
def planeBytes (fig : Plane.Figure) (bytes : Unit → Except String ByteArray) :
    Except String ByteArray :=
  let ps := if fig.checks == .fail then fig.checkMessages else #[]
  if ps.isEmpty then bytes () else .error ("layout problems: " ++ "; ".intercalate ps.toList)

/-- The SVG and PNG outputs of one plane figure, named with `suffix`; the SVG carries the
figure's layout warnings when `warn`. -/
def planeOutputs (fig : Plane.Figure) (suffix : String) (warn : Bool) : Array Output :=
  let g := fig.autoPlaced
  #[{ name := suffix, format := .svg, bytes := fun _ => planeBytes fig fun _ => .ok fig.toSvg.toUTF8,
      spec := fig.toSvg.toUTF8, textEngine := fig.style.text.id,
      inline := fun _ => some
        { width := g.frame.width.round, height := g.frame.height.round, nodes := fig.svgNodes },
      problems := fun _ => if warn && fig.checks == .warn then fig.checkMessages else #[] },
    { name := suffix, format := .png,
      bytes := fun _ => planeBytes fig fun _ => match fig.toPng with
        | some b => .ok b
        | none => .error "the figure has no pixels",
      spec := (fig.toSvg (outlines := true)).toUTF8, textEngine := fig.style.text.id }]

/-- Plane figures: the SVG (with the layout problems the figure's `checks` level reports as
warnings) and the PNG, and the same at the narrow width (suffix `-narrow`) when the figure has
one. A figure whose `checks` level is `fail` and that has layout problems cannot be rendered. -/
instance : ToOutputs Plane.Figure where
  outputs fig :=
    planeOutputs fig "" true ++ match fig.narrow with
      | some n => planeOutputs n "-narrow" true
      | none => #[]

/-- An explorer frame for a page. -/
def _root_.PILean.ExplorerFrame.inline (f : ExplorerFrame) : InlineSvg :=
  { width := f.width, height := f.height, nodes := f.svgNodes }

/-- Families of frames: the poster's SVG (carrying every frame for a page that shows them
inline) and PNG. An explorer that is not well formed (`Explorer.valid`) cannot be rendered. -/
instance : ToOutputs Explorer where
  outputs x :=
    let p := x.posterFrame
    let ok := fun (b : Unit → Except String ByteArray) =>
      if x.valid then b () else .error s!"the explorer has {x.frames.size} frames for         {x.values} values and {x.steps} steps, or its poster {x.poster} is not among them"
    #[{ name := "", format := .svg, bytes := fun _ => ok fun _ => .ok p.toSvg.toUTF8,
        spec := p.toSvg.toUTF8, textEngine := p.style.text.id,
        inline := fun _ => some p.inline,
        frames := fun _ => some
          { axisName := x.axisName, axisValues := x.axisValues,
            stepCaptions := x.stepCaptions, frames := x.frames.map (·.inline),
            poster := x.poster } },
      { name := "", format := .png,
        bytes := fun _ => ok fun _ => match p.toPng with
          | some b => .ok b
          | none => .error "the poster has no pixels",
        spec := (p.toSvg (outlines := true)).toUTF8, textEngine := p.style.text.id }]

/-- A graph with how it is laid out and drawn. -/
structure GraphFigure where
  /-- The graph. -/
  graph : Graph
  /-- The options of the layered layout. -/
  options : Graph.LayeredOptions := {}
  /-- The style. -/
  style : Style := {}
  /-- The scale of the PNG relative to the SVG. -/
  scale : Float := 1

/-- A graph with the layout and style of the default `GraphFigure`: the SVG and the PNG. -/
instance : ToOutputs GraphFigure where
  outputs f :=
    let g := f.graph
    #[{ name := "", format := .svg, bytes := fun _ => .ok (g.toSvg f.options f.style).toUTF8,
        spec := (g.toSvg f.options f.style).toUTF8, textEngine := f.style.text.id },
      { name := "", format := .png,
        bytes := fun _ => match g.toPng f.options f.style f.scale with
          | .ok b => .ok b
          | .error e => .error (toString e),
        spec := (g.toSvg f.options f.style (outlines := true)).toUTF8,
        textEngine := f.style.text.id }]

/-- A graph is rendered with the default layered layout and light style, scale 1. -/
instance : ToOutputs Graph where
  outputs g := ToOutputs.outputs ({ graph := g } : GraphFigure)

/-- Animations: the animated SVG, the APNG, the GIF and the poster frame (a PNG with the suffix
`-poster`). -/
instance : ToOutputs Animation where
  outputs a :=
    let svg := a.toSvg.toUTF8
    let toErr := fun {ε : Type} [ToString ε] (r : Except ε ByteArray) =>
      r.mapError toString
    let t := a.text.id
    #[{ name := "", format := .svg, bytes := fun _ => .ok svg, spec := svg, textEngine := t },
      { name := "", format := .apng, bytes := fun _ => toErr a.toApng, spec := svg,
        textEngine := t },
      { name := "", format := .gif, bytes := fun _ => toErr a.toGif, spec := svg,
        textEngine := t },
      { name := "-poster", format := .png, bytes := fun _ => toErr a.posterPng,
        spec := a.posterSvg.toUTF8, textEngine := t }]

end PILean.Trust
