/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plot.Figure
import PILean.Plane
import PILean.Explorer
import PILean.Graph.Draw
import PILean.Anim.Animation
import PILean.Diagram.Basic

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
* `Standing`: whether a figure is tied to its object by a theorem or is an illustration
* `InlineSvg`, `FrameSet`: pictures and families of frames a web page puts inline
* instances for `Plot.Figure`, `Plane.Figure`, `Explorer`, `Graph`, `GraphFigure`,
  `Animation` and `Diagram.Diagram`
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

/-- How a figure stands with respect to the object it shows. A figure is `proved` when at least
one theorem is linked to it by `figure_proves` and passed that command's rule
(`PILean.Trust.figureTheoremProblem?`) in the environment where the build's table of figures
(`figures%`) was elaborated; otherwise it is an `illustration`, openly marked as one by
`@[figure illustration]` or not. The standing says that such a theorem exists, not what it
states: the statement is still its reader's to judge (`docs/PROOFS.md`). -/
inductive Standing where
  /-- The theorems linked to the figure by `figure_proves`, by full name, each of which passed
  the rule when the table of figures was elaborated; never empty for a figure `figures%` makes. -/
  | proved (theorems : Array String)
  /-- No theorem is linked to the figure; `marked` says whether its declaration says so with
  `@[figure illustration]`. -/
  | illustration (marked : Bool)
deriving BEq, Repr, Inhabited

/-- The standing's word, as source records and manifests write it: `proved` or `illustration`. -/
def Standing.word : Standing → String
  | .proved _ => "proved"
  | .illustration _ => "illustration"

/-- The theorems of a proved standing, by full name; empty for an illustration. -/
def Standing.theorems : Standing → Array String
  | .proved ts => ts
  | .illustration _ => #[]

/-- Whether the standing is an illustration that its declaration does not mark as one: a figure
`pilean-build --require-standing` refuses. -/
def Standing.unmarked : Standing → Bool
  | .illustration false => true
  | _ => false

/-- A picture a web page can put inline (as an `svg` element) instead of a file: its size in pixels
and the SVG nodes of its body, as `Svg.document` writes them. -/
structure InlineSvg where
  /-- The width in pixels. -/
  width : Float
  /-- The height in pixels. -/
  height : Float
  /-- The nodes of the document's body. -/
  nodes : Array Svg.Node
  /-- The light colours (`#rrggbb`) of the picture paired with those of its dark twin, for a page
  that restyles it in its dark theme (`Style.darkColourPairs`); empty without a twin. -/
  darkColours : Array (String × String) := #[]
  /-- The fill opacities (as written) of the picture's tints paired with the dark twin's. -/
  darkOpacities : Array (String × String) := #[]
  deriving Inhabited

/-- The fill opacity attribute a tint of opacity `a` gets (`Svg.paint` of an opaque colour at
that alpha). -/
def tintOpacityText (a : Float) : String :=
  fmtNum ((max 0 (min 1 a) * 255).round / 255) 3

/-- The restyling of an inline picture in the dark theme of a page, for a picture in the style
`st`: its light colours paired with its dark twin's (`Style.darkColourPairs`) and its tint
opacity paired with the twin's when they differ; both empty without a twin. -/
def InlineSvg.themeOf (st : Style) : Array (String × String) × Array (String × String) :=
  (st.darkColourPairs, match st.darkTwin? with
    | some d =>
      if st.plane.fillOpacity == d.plane.fillOpacity then #[]
      else #[(tintOpacityText st.plane.fillOpacity, tintOpacityText d.plane.fillOpacity)]
    | none => #[])

/-- An inline picture in a style: its nodes, and its dark colours and tint opacities when the
style has a dark twin (`InlineSvg.themeOf`). -/
def InlineSvg.ofStyle (w h : Float) (nodes : Array Svg.Node) (st : Style) : InlineSvg :=
  let (darkColours, darkOpacities) := InlineSvg.themeOf st
  { width := w, height := h, nodes, darkColours, darkOpacities }

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
  /-- For an SVG output a page can put inline: the restyling of its dark theme, the
  `darkColours` and `darkOpacities` of `inline` (`InlineSvg.themeOf` of its style), which the
  manifest records so that a site check can tie the page's theme rules to it. -/
  theme : Unit → Array (String × String) × Array (String × String) := fun _ => (#[], #[])
  /-- For the poster of a family of frames: every frame, for a page that shows them inline. -/
  frames : Unit → Option FrameSet := fun _ => none
  /-- Problems of the figure's layout a build should report as warnings (on one output of a
  figure, so that they are reported once). -/
  problems : Unit → Array String := fun _ => #[]
  /-- The standing of the figure the output belongs to. `ToOutputs` instances leave it at an
  unmarked illustration; `figures%` sets it on every output of a figure from the links
  `figure_proves` recorded and the figure's `@[figure illustration]` marking. -/
  standing : Standing := .illustration false

/-- An empty SVG output that cannot be rendered (for indexing arrays of outputs). -/
instance : Inhabited Output :=
  ⟨{ name := "", format := .svg, bytes := fun _ => .error "no output", spec := .empty }⟩

/-- The outputs with the standing `s` set on each (`figures%` applies it to a figure's outputs). -/
def withStanding (s : Standing) (os : Array Output) : Array Output :=
  os.map ({ · with standing := s })

/-- Values that PILean can render to files. -/
class ToOutputs (α : Type) where
  /-- The files a value is rendered to, in a fixed order. -/
  outputs : α → Array Output

/-- The bytes of an output, or the problems as an error when `fail` and there are some. -/
def checkedBytes (fail : Bool) (problems : Unit → Array String)
    (bytes : Unit → Except String ByteArray) : Except String ByteArray :=
  let ps := if fail then problems () else #[]
  if ps.isEmpty then bytes () else .error ("problems: " ++ "; ".intercalate ps.toList)

/-- Figures: the SVG (with the problems of its checks, `PILean.Plot.Check`, which the figure's
`checks` level reports as warnings) and the PNG when the figure has pixels. A figure whose
`checks` level is `fail` and that has such problems cannot be rendered. -/
instance : ToOutputs Plot.Figure where
  outputs fig :=
    let ok := checkedBytes (fig.checks == .fail) fun _ => fig.checkMessages
    #[{ name := "", format := .svg, bytes := fun _ => ok fun _ => .ok fig.toSvg.toUTF8,
        spec := fig.toSvg.toUTF8, textEngine := fig.style.text.id,
        inline := fun _ => some (InlineSvg.ofStyle fig.width fig.height
          (fig.draw.render (.forSvg fig.style.text fig.style.fontFamily)) fig.style),
        theme := fun _ => InlineSvg.themeOf fig.style,
        problems := fun _ => if fig.checks == .warn then fig.checkMessages else #[] },
      { name := "", format := .png,
        bytes := fun _ => ok fun _ => match fig.toPng with
          | some b => .ok b
          | none => .error "the figure has no pixels",
        spec := (fig.toSvg (outlines := true)).toUTF8, textEngine := fig.style.text.id }]

/-- The bytes of a plane figure's output, or the figure's layout problems as an error when its
`checks` level is `fail` and it has some. -/
def planeBytes (fig : Plane.Figure) (bytes : Unit → Except String ByteArray) :
    Except String ByteArray :=
  checkedBytes (fig.checks == .fail) (fun _ => fig.checkMessages) bytes

/-- The SVG and PNG outputs of one plane figure, named with `suffix`; the SVG carries the
figure's layout warnings when `warn`. -/
def planeOutputs (fig : Plane.Figure) (suffix : String) (warn : Bool) : Array Output :=
  let g := fig.autoPlaced
  #[{ name := suffix, format := .svg,
      bytes := fun _ => planeBytes fig fun _ => .ok fig.toSvg.toUTF8,
      spec := fig.toSvg.toUTF8, textEngine := fig.style.text.id,
      inline := fun _ => some
        (InlineSvg.ofStyle g.frame.width.round g.frame.height.round fig.svgNodes fig.style),
      theme := fun _ => InlineSvg.themeOf fig.style,
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
  InlineSvg.ofStyle f.width f.height f.svgNodes f.style

/-- Families of frames: the poster's SVG (carrying every frame for a page that shows them
inline, and the frames' problems as warnings, `Explorer.problems`) and PNG, then each frame `k`
as an SVG of its own named `-frame-k` (`k` from 0, in the order of `Explorer.frames`), so that
every picture a page shows inline is a file with its fingerprint and its manifest entry. An
explorer that is not well formed (`Explorer.valid`) cannot be rendered, nor one with a frame whose
checks level is `fail` and that has problems (`Explorer.problemsFail`). -/
instance : ToOutputs Explorer where
  outputs x :=
    let p := x.posterFrame
    let ok := fun (b : Unit → Except String ByteArray) =>
      if !x.valid then .error s!"the explorer has {x.frames.size} frames for \
        {x.values} values and {x.steps} steps, or its poster {x.poster} is not among them"
      else checkedBytes x.problemsFail (fun _ => x.problems) b
    let frameOutputs := x.frames.zipIdx.map fun (f, k) =>
      ({ name := s!"-frame-{k}", format := .svg, bytes := fun _ => ok fun _ => .ok f.toSvg.toUTF8,
         spec := f.toSvg.toUTF8, textEngine := f.style.text.id,
         inline := fun _ => some f.inline, theme := fun _ => InlineSvg.themeOf f.style } :
        Output)
    #[{ name := "", format := .svg, bytes := fun _ => ok fun _ => .ok p.toSvg.toUTF8,
        spec := p.toSvg.toUTF8, textEngine := p.style.text.id,
        inline := fun _ => some p.inline, theme := fun _ => InlineSvg.themeOf p.style,
        frames := fun _ => some
          { axisName := x.axisName, axisValues := x.axisValues,
            stepCaptions := x.stepCaptions, frames := x.frames.map (·.inline),
            poster := x.poster },
        problems := fun _ => if x.problemsFail then #[] else x.problems },
      { name := "", format := .png,
        bytes := fun _ => ok fun _ => match p.toPng with
          | some b => .ok b
          | none => .error "the poster has no pixels",
        spec := (p.toSvg (outlines := true)).toUTF8, textEngine := p.style.text.id }] ++
      frameOutputs

/-- Diagrams: the outputs of their plane figure (`Diagram.toPlane`), so the SVG and PNG, and at a
narrow width the same with the suffix `-narrow`. -/
instance : ToOutputs Diagram.Diagram where
  outputs d := ToOutputs.outputs d.toPlane

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

/-- Animations: the animated SVG (with the animation's problems as warnings), the APNG, the GIF
and the poster frame (a PNG with the suffix `-poster`). An animation whose problems stop it
(`Animation.problemsFail`) cannot be rendered. -/
instance : ToOutputs Animation where
  outputs a :=
    let svg := a.toSvg.toUTF8
    let ok := checkedBytes a.problemsFail a.problems
    let toErr := fun {ε : Type} [ToString ε] (r : Except ε ByteArray) =>
      r.mapError toString
    let t := a.text.id
    #[{ name := "", format := .svg, bytes := fun _ => ok fun _ => .ok svg, spec := svg,
        textEngine := t, problems := fun _ => if a.problemsFail then #[] else a.problems () },
      { name := "", format := .apng, bytes := fun _ => ok fun _ => toErr a.toApng, spec := svg,
        textEngine := t },
      { name := "", format := .gif, bytes := fun _ => ok fun _ => toErr a.toGif, spec := svg,
        textEngine := t },
      { name := "-poster", format := .png, bytes := fun _ => ok fun _ => toErr a.posterPng,
        spec := a.posterSvg.toUTF8, textEngine := t }]

end PILean.Trust
