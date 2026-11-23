/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Raster.SvgRender
import PILean.Text.Engine

/-!
# The vector canvas

A small composable drawing model: shapes (paths with a fill and a stroke), text, and groups with
a transformation, an opacity and a clip. A drawing is a value (`Shape`); it is written as SVG
(`Shape.toSvg`) or drawn as an image (`Shape.toImage`) from the same SVG nodes
(`Shape.render`), so the two agree. Plots and graphs are built on it, and it can be used
directly.

* **Transformations** are applied to the geometry when the drawing is written: the output has
  no `transform` attributes (except the rotation of SVG text), so every renderer, PILean's own
  included, draws it the same way. A stroke's width is scaled by the transformation's largest
  scale.
* **Paints** are colours or gradients (`Raster.Paint`, linear or radial, interpolated in linear
  light); a gradient is written to SVG with stops sampled so that SVG's own interpolation shows
  the same colours (`Raster.gradientNode`).
* **Clips** are paths, transformed with their group and written as `clipPath` elements.
* **Text** is a placeholder the output resolves: SVG text in the style's font family
  (`TextMode.native`), or shapes from a `TextEngine` (`TextMode.shapes`), which is how text
  reaches images. Its position is its anchor point on the baseline.
* Ids of clips and gradients are numbered in drawing order, so the output is deterministic.
* **Metadata** (`ShapeInfo`, `Shape.tagged`): an accessible title and description, CSS classes, a
  stable id and the name of a Lean declaration, attached to a shape. SVG writes them as a `g`
  with `id`, `class` and `data-lean-decl` attributes and `title` and `desc` children; an image
  draws the shape alone (the rasteriser skips `title` and `desc`). Ids and classes are reduced to
  ASCII letters, digits, `_`, `-` and `.`, so that what a caller passes cannot become markup or a
  link; titles and descriptions are text, escaped by the writer.

## Main definitions

* `Fill`, `Line`, `ShapeInfo`, `Shape`, `TextMode`.
* `Shape.render`, `Shape.toSvg`, `Shape.toImage`, `Shape.toPng`.
-/

namespace PILean.Canvas

open PILean Svg

/-- How a shape is filled. -/
inductive Fill where
  /-- A colour. -/
  | solid (c : Rgba)
  /-- A gradient. -/
  | paint (p : Raster.Paint)
  deriving Inhabited

/-- How a shape's outline is stroked. -/
structure Line where
  /-- The colour. -/
  ink : Rgba
  /-- The width. -/
  width : Float := 1
  /-- `butt`, `round` or `square`. -/
  cap : String := "butt"
  /-- `miter`, `round` or `bevel`. -/
  join : String := "miter"
  /-- The dash pattern (empty for solid). -/
  dash : Array Float := #[]
  deriving Inhabited

/-- Metadata of a shape, all optional (empty strings are left out): an accessible title and
description, CSS classes separated by spaces, a stable id, and the name of the Lean declaration
the shape shows. -/
structure ShapeInfo where
  /-- The accessible name, written as a `title` child. -/
  title : String := ""
  /-- The accessible description, written as a `desc` child. -/
  description : String := ""
  /-- CSS classes, separated by spaces. -/
  cssClass : String := ""
  /-- A stable id, unique within the document if the page refers to it. -/
  id : String := ""
  /-- The full name of a Lean declaration, written as `data-lean-decl`. -/
  leanDecl : String := ""
  deriving BEq, Inhabited, Repr

/-- Whether every field of the metadata is empty. -/
def ShapeInfo.isEmpty (i : ShapeInfo) : Bool :=
  i.title.isEmpty && i.description.isEmpty && i.cssClass.isEmpty && i.id.isEmpty &&
    i.leanDecl.isEmpty

/-- The metadata of `j` where it has a field, else that of `i`; classes are joined. -/
def ShapeInfo.merge (i j : ShapeInfo) : ShapeInfo where
  title := if j.title.isEmpty then i.title else j.title
  description := if j.description.isEmpty then i.description else j.description
  cssClass := if i.cssClass.isEmpty then j.cssClass else if j.cssClass.isEmpty then i.cssClass
    else i.cssClass ++ " " ++ j.cssClass
  id := if j.id.isEmpty then i.id else j.id
  leanDecl := if j.leanDecl.isEmpty then i.leanDecl else j.leanDecl

/-- An identifier reduced to ASCII letters, digits, `_`, `-` and `.`: every other character
becomes `_`. -/
def safeToken (s : String) : String :=
  s.map fun c => if (c.isAlphanum && c.val < 128) || c == '_' || c == '-' || c == '.' then c
    else '_'

/-- The attributes and children of the metadata in SVG: `id`, `class` (each class through
`safeToken`) and `data-lean-decl`, and the `title` and `desc` elements; empty fields are left
out. -/
def ShapeInfo.svgParts (i : ShapeInfo) : Array (String × String) × Array Svg.Node :=
  let classes := (i.cssClass.split (· == ' ')).toList.map (·.toString) |>.filter (!·.isEmpty)
  let attrs := (if i.id.isEmpty then #[] else #[("id", safeToken i.id)]) ++
    (if classes.isEmpty then #[] else #[("class", " ".intercalate (classes.map safeToken))]) ++
    (if i.leanDecl.isEmpty then #[] else #[("data-lean-decl", i.leanDecl)])
  let kids := (if i.title.isEmpty then #[] else #[Svg.el "title" #[] #[.text i.title]]) ++
    (if i.description.isEmpty then #[] else #[Svg.el "desc" #[] #[.text i.description]])
  (attrs, kids)

/-- A drawing. -/
inductive Shape where
  /-- A path with an optional fill and stroke, at an opacity. -/
  | path (p : Path) (fill : Option Fill := none) (line : Option Line := none)
      (opacity : Float := 1)
  /-- A line of text: its anchor point on the baseline, size, colour, anchor, weight (1 is
  regular) and rotation (radians, clockwise on screen, about the anchor point). -/
  | text (s : String) (at_ : Point) (size : Float) (ink : Rgba) (anchor : Anchor := .start)
      (weight : Float := 1) (rotation : Float := 0)
  /-- Shapes drawn together under a transformation, at an opacity, clipped to a path (in the
  group's coordinates). -/
  | group (children : Array Shape) (transform : Affine := Affine.id) (opacity : Float := 1)
      (clip : Option Path := none)
  /-- A shape with metadata (see `ShapeInfo`): in SVG a `g` carrying it around the shape's
  nodes, in an image the shape alone. -/
  | tagged (info : ShapeInfo) (child : Shape)
  deriving Inhabited

/-- How text is written. -/
inductive TextMode where
  /-- SVG `text` elements in a font family. -/
  | native (family : String)
  /-- Shapes from a text engine. -/
  | shapes (engine : TextEngine)

/-- How an SVG document writes the text of `engine`: as `text` elements in `family`, unless the
caller asks for `outlines` or the engine's strings are not plain text (`TextEngine.native`). -/
def TextMode.forSvg (engine : TextEngine) (family : String) (outlines : Bool := false) :
    TextMode :=
  if outlines || !engine.native then .shapes engine else .native family

/-- The state of rendering: the definitions written so far and the next id. -/
structure RenderState where
  /-- `clipPath` and gradient definitions. -/
  defs : Array Node := #[]
  /-- The next id's number. -/
  next : Nat := 0

/-- A text's horizontal offset for its anchor, given its width. -/
def anchorOffset (a : Anchor) (w : Float) : Float :=
  match a with
  | .start => 0 | .middle => -w / 2 | .finish => -w

/-- The attributes of a stroke at a scale. -/
def lineAttrs (l : Line) (k : Float) : Array (String × String) :=
  paint "stroke" (some l.ink) ++ #[("stroke-width", fmtNum (l.width * k))] ++
    (if l.cap != "butt" then #[("stroke-linecap", l.cap)] else #[]) ++
    (if l.join != "miter" then #[("stroke-linejoin", l.join)] else #[]) ++
    (if l.dash.isEmpty then #[] else
      #[("stroke-dasharray", " ".intercalate (l.dash.toList.map fun d => fmtNum (d * k)))])

/-- The nodes of a shape under transformation `m`, nested at most `fuel` deep. -/
def renderAt (mode : TextMode) : Nat → Affine → Shape → StateM RenderState (Array Node)
  | 0, _, _ => pure #[]
  | fuel + 1, m, s => match s with
    | .path p fill line opacity => do
      let q := p.transform m
      let k := m.maxScale
      let fillAttrs ← match fill with
        | none => pure (paint "fill" none)
        | some (.solid c) => pure (paint "fill" (some c))
        | some (.paint g) =>
          let st ← get
          let id := s!"p{st.next}"
          match (Raster.gradientNode id (transformPaint m g)) with
          | some n => set { st with defs := st.defs.push n, next := st.next + 1 }
                      pure #[("fill", s!"url(#{id})")]
          | none => match g with
            | .solid c => pure (paint "fill" (some c))
            | _ => pure (paint "fill" none)
      let strokeAttrs := match line with
        | some l => lineAttrs l k
        | none => #[]
      let op := if opacity < 1 then #[("opacity", fmtNum (max 0 opacity) 3)] else #[]
      let node := el "path" (#[("d", pathData q)] ++ fillAttrs ++ strokeAttrs)
      return #[if op.isEmpty then node else el "g" op #[node]]
    | .text str at_ size ink anchor weight rot => do
      let p := m.apply at_
      let k := m.maxScale
      match mode with
      | .native family =>
        let rotAttr := if rot == 0 then #[] else
          #[("transform", s!"rotate({fmtNum (rot * 180 / 3.141592653589793)} \
            {fmtNum p.x} {fmtNum p.y})")]
        let weightAttr := if weight > 1.15 then #[("font-weight", "600")] else #[]
        return #[Svg.text p.x p.y str (size * k) ink anchor
          (#[("font-family", family)] ++ weightAttr ++ rotAttr)]
      | .shapes eng =>
        let sz := size * k
        let shp := eng.shape str sz weight
        let dx := anchorOffset anchor (eng.measure str sz)
        let place := ((Affine.translate p.x p.y).comp (Affine.rotate rot)).comp
          (Affine.translate dx 0)
        let mut out := #[]
        if !shp.fill.cmds.isEmpty then
          out := out.push (el "path" (#[("d", pathData (shp.fill.transform place) 3)] ++
            paint "fill" (some ink)))
        if !shp.strokes.cmds.isEmpty then
          out := out.push (el "path" (#[("d", pathData (shp.strokes.transform place) 3)] ++
            paint "fill" none ++ paint "stroke" (some ink) ++
            #[("stroke-width", fmtNum shp.strokeWidth 3), ("stroke-linecap", "round"),
              ("stroke-linejoin", "round")]))
        return out
    | .group children t opacity clip => do
      let m' := m.comp t
      let mut inner : Array Node := #[]
      for c in children do inner := inner ++ (← renderAt mode fuel m' c)
      let mut attrs : Array (String × String) := #[]
      if let some cp := clip then
        let st ← get
        let id := s!"c{st.next}"
        set { st with defs := st.defs.push (el "clipPath" #[("id", id)]
          #[el "path" #[("d", pathData (cp.transform m'))]]), next := st.next + 1 }
        attrs := attrs.push ("clip-path", s!"url(#{id})")
      if opacity < 1 then attrs := attrs.push ("opacity", fmtNum (max 0 opacity) 3)
      return if attrs.isEmpty then inner else #[el "g" attrs inner]
    | .tagged info child => do
      let inner ← renderAt mode fuel m child
      if info.isEmpty then return inner
      let (attrs, kids) := info.svgParts
      return #[el "g" attrs (kids ++ inner)]
where
  /-- A gradient's geometry under a transformation. -/
  transformPaint (m : Affine) : Raster.Paint → Raster.Paint
    | .solid c => .solid c
    | .linear a b stops => .linear (m.apply a) (m.apply b) stops
    | .radial c r stops => .radial (m.apply c) (r * m.maxScale) stops

/-- A shape's nodes: its definitions (in a `defs` element) and its body. -/
def Shape.render (s : Shape) (mode : TextMode) : Array Node :=
  let (body, st) := (renderAt mode 256 Affine.id s).run {}
  (if st.defs.isEmpty then #[] else #[el "defs" #[] st.defs]) ++ body

/-- A shape as an SVG document of `width × height`, text in `family` (or as shapes from
`engine` when given). -/
def Shape.toSvg (s : Shape) (width height : Float) (family : String)
    (engine : Option TextEngine := none) : String :=
  document width height (s.render (match engine with
    | some e => .shapes e
    | none => .native family))

/-- A shape drawn as an RGBA image of `w × h` pixels on `bg`, text as shapes from `engine`. -/
def Shape.toImage (s : Shape) (w h : Nat) (engine : TextEngine) (bg : Rgba := ⟨0, 0, 0, 0⟩) :
    Image :=
  (Raster.Svg.rasterize w h (s.render (.shapes engine)) bg).toImage .rgba

/-- A shape as PNG bytes (see `Shape.toImage`). -/
def Shape.toPng (s : Shape) (w h : Nat) (engine : TextEngine) (bg : Rgba := ⟨0, 0, 0, 0⟩)
    (md : Png.Metadata := {}) : Except Png.PngError ByteArray :=
  (s.toImage w h engine bg).writePng md

/-- A rectangle path. -/
def rect (x y w h : Float) : Path := Path.rect x y w h

/-- A circle path. -/
def circle (c : Point) (r : Float) : Path := Path.ellipse c r r

end PILean.Canvas
