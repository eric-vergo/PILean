/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plot.Figure
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
* instances for `Plot.Figure`, `Graph`, `GraphFigure` and `Animation`
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

/-- Values that PILean can render to files. -/
class ToOutputs (α : Type) where
  /-- The files a value is rendered to, in a fixed order. -/
  outputs : α → Array Output

/-- Figures: the SVG, and the PNG when the figure has pixels. -/
instance : ToOutputs Plot.Figure where
  outputs fig :=
    #[{ name := "", format := .svg, bytes := fun _ => .ok fig.toSvg.toUTF8,
        spec := fig.toSvg.toUTF8, textEngine := fig.style.text.id },
      { name := "", format := .png,
        bytes := fun _ => match fig.toPng with
          | some b => .ok b
          | none => .error "the figure has no pixels",
        spec := (fig.toSvg (outlines := true)).toUTF8, textEngine := fig.style.text.id }]

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
