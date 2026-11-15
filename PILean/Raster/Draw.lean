/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Raster.Canvas
import PILean.Raster.Stroke

/-!
# Drawing

A drawing surface in the spirit of Pillow's `ImageDraw`, over the rasteriser: fill and stroke
paths, lines, rectangles, rounded rectangles, ellipses, arcs and polygons, with paints, an
opacity, a clip rectangle and a clip path. A `Draw` is a value; each operation returns the
drawing with the shape painted, and `Draw.toImage` gives the picture.

Coordinates are in pixels, `x` to the right and `y` down, with pixel `(i, j)` the unit square
from `(i, j)`: a one-pixel line along `y = 10.5` covers row 10 exactly (`crisp` puts a
coordinate there).

## Main definitions

* `Draw`, `Draw.new`, `Draw.toImage`.
* `Draw.fill`, `Draw.stroke`: a path filled or stroked.
* `Draw.line`, `Draw.rectangle`, `Draw.roundedRectangle`, `Draw.ellipse`, `Draw.arc`,
  `Draw.polygon`: Pillow's shapes.
* `Draw.withClip`, `Draw.withClipPath`, `Draw.group`.
-/

namespace PILean.Raster

/-- A drawing: the canvas, the clip rectangle and the clip mask in force. -/
structure Draw where
  /-- The surface. -/
  canvas : Canvas
  /-- Drawing is clipped to this rectangle. -/
  clip : IRect
  /-- And through this mask, if any. -/
  mask : Option Mask := none

namespace Draw

/-- A drawing of `w × h` pixels on a background, mixing colours in `space` (linear light by
default). -/
def new (w h : Nat) (bg : Rgba := ⟨255, 255, 255, 255⟩) (space : Space := .linear) : Draw :=
  { canvas := Canvas.new w h bg space, clip := ⟨0, 0, w, h⟩ }

/-- The picture, in a mode (RGBA by default). -/
def toImage (d : Draw) (mode : Mode := .rgba) : Image := d.canvas.toImage mode

/-- The polygons filled with a paint under a rule, at an opacity. -/
def fillPolygons (d : Draw) (polys : Array (Array Point)) (paint : Paint)
    (rule : FillRule := .nonZero) (opacity : Float := 1) : Draw :=
  match coverage polys rule d.canvas.width d.canvas.height d.clip with
  | some spans => { d with canvas := d.canvas.fillSpans spans paint opacity d.mask }
  | none => d

/-- A path filled (curves flattened to `tol` pixels). -/
def fill (d : Draw) (p : Path) (paint : Paint) (rule : FillRule := .nonZero)
    (opacity : Float := 1) (tol : Float := 0.1) : Draw :=
  d.fillPolygons ((p.flatten tol).map (·.points)) paint rule opacity

/-- A path stroked. -/
def stroke (d : Draw) (p : Path) (st : Stroke) (paint : Paint) (opacity : Float := 1) : Draw :=
  d.fillPolygons (strokePolygons p st) paint .nonZero opacity

/-- A line through points (Pillow's `line`), `width` wide, with butt caps and miter joins by
default. -/
def line (d : Draw) (pts : Array Point) (paint : Paint) (width : Float := 1)
    (cap : Cap := .butt) (join : Join := .miter) : Draw :=
  d.stroke (Path.polyline pts) { width, cap, join } paint

/-- A rectangle from `(x0, y0)` to `(x1, y1)` (Pillow's `rectangle`), filled, outlined, or
both; the outline is drawn inside the rectangle, as Pillow draws it. -/
def rectangle (d : Draw) (x0 y0 x1 y1 : Float) (fill : Option Paint := none)
    (outline : Option Paint := none) (width : Float := 1) : Draw :=
  let d := match fill with
    | some f => d.fill (Path.rect x0 y0 (x1 - x0) (y1 - y0)) f
    | none => d
  match outline with
  | some o =>
    let h := width / 2
    d.stroke (Path.rect (x0 + h) (y0 + h) (x1 - x0 - width) (y1 - y0 - width)) { width } o
  | none => d

/-- A rectangle with corners rounded to radius `r` (Pillow's `rounded_rectangle`). -/
def roundedRectPath (x0 y0 x1 y1 r : Float) : Path :=
  let r := max 0 (min r (min ((x1 - x0) / 2) ((y1 - y0) / 2)))
  -- a quarter circle as one cubic: control points at the standard distance 0.5523 r
  let k := 0.5522847498 * r
  Path.empty
    |>.moveTo ⟨x0 + r, y0⟩ |>.lineTo ⟨x1 - r, y0⟩
    |>.cubicTo ⟨x1 - r + k, y0⟩ ⟨x1, y0 + r - k⟩ ⟨x1, y0 + r⟩ |>.lineTo ⟨x1, y1 - r⟩
    |>.cubicTo ⟨x1, y1 - r + k⟩ ⟨x1 - r + k, y1⟩ ⟨x1 - r, y1⟩ |>.lineTo ⟨x0 + r, y1⟩
    |>.cubicTo ⟨x0 + r - k, y1⟩ ⟨x0, y1 - r + k⟩ ⟨x0, y1 - r⟩ |>.lineTo ⟨x0, y0 + r⟩
    |>.cubicTo ⟨x0, y0 + r - k⟩ ⟨x0 + r - k, y0⟩ ⟨x0 + r, y0⟩ |>.close

/-- A rounded rectangle, filled, outlined (inside), or both. -/
def roundedRectangle (d : Draw) (x0 y0 x1 y1 r : Float) (fill : Option Paint := none)
    (outline : Option Paint := none) (width : Float := 1) : Draw :=
  let d := match fill with
    | some f => d.fill (roundedRectPath x0 y0 x1 y1 r) f
    | none => d
  match outline with
  | some o =>
    let h := width / 2
    d.stroke (roundedRectPath (x0 + h) (y0 + h) (x1 - h) (y1 - h) (r - h)) { width } o
  | none => d

/-- The ellipse inscribed in the box `(x0, y0)`–`(x1, y1)` (Pillow's `ellipse`). -/
def ellipse (d : Draw) (x0 y0 x1 y1 : Float) (fill : Option Paint := none)
    (outline : Option Paint := none) (width : Float := 1) : Draw :=
  let c : Point := ⟨(x0 + x1) / 2, (y0 + y1) / 2⟩
  let (rx, ry) := ((x1 - x0) / 2, (y1 - y0) / 2)
  let d := match fill with
    | some f => d.fill (Path.ellipse c rx ry) f
    | none => d
  match outline with
  | some o => d.stroke (Path.ellipse c (rx - width / 2) (ry - width / 2)) { width } o
  | none => d

/-- The points of the arc of the ellipse in the box from angle `start` to `stop` (degrees,
clockwise from the positive x axis, as in Pillow), at most `tol` from the curve. -/
def arcPoints (x0 y0 x1 y1 start stop : Float) (tol : Float := 0.1) : Array Point :=
  let c : Point := ⟨(x0 + x1) / 2, (y0 + y1) / 2⟩
  let (rx, ry) := ((x1 - x0) / 2, (y1 - y0) / 2)
  let r := max (max rx ry) 0.01
  let sweep := if stop < start then stop + 360 - start else stop - start
  let sweep := min sweep 360
  let step := 2 * Float.acos (max (-1) (min 1 (1 - max tol 0.01 / r)))
  let n : Nat := max 2 (min 4096 ((sweep / 57.29577951308232 / max step 1e-3).ceil.toUInt64.toNat
    + 1))
  (Array.range n).map fun i =>
    let t := (start + sweep * i.toFloat / (n - 1).toFloat) / 57.29577951308232
    ⟨c.x + rx * Float.cos t, c.y + ry * Float.sin t⟩

/-- An arc (Pillow's `arc`): the stroke of part of an ellipse's outline. -/
def arc (d : Draw) (x0 y0 x1 y1 start stop : Float) (paint : Paint) (width : Float := 1) :
    Draw :=
  let h := width / 2
  d.stroke (Path.polyline (arcPoints (x0 + h) (y0 + h) (x1 - h) (y1 - h) start stop))
    { width } paint

/-- A polygon (Pillow's `polygon`), filled, outlined, or both. -/
def polygon (d : Draw) (pts : Array Point) (fill : Option Paint := none)
    (outline : Option Paint := none) (width : Float := 1) (rule : FillRule := .nonZero) :
    Draw :=
  let p := (Path.polyline pts).close
  let d := match fill with
    | some f => d.fill p f rule
    | none => d
  match outline with
  | some o => d.stroke p { width } o
  | none => d

/-- Drawing clipped to a rectangle (as well as to the clip in force). -/
def withClip (d : Draw) (r : IRect) : Draw := { d with clip := d.clip.inter r }

/-- Drawing clipped to a path's fill (replacing any clip path in force). -/
def withClipPath (d : Draw) (p : Path) (rule : FillRule := .nonZero) : Draw :=
  let w := d.canvas.width
  let h := d.canvas.height
  match coverage ((p.flatten 0.1).map (·.points)) rule w h ⟨0, 0, w, h⟩ with
  | some spans => { d with mask := some (Mask.ofSpans w h spans) }
  | none => d

/-- A group: `body` drawn on a transparent layer of the same size and clip, then composited
at `opacity`. -/
def group (d : Draw) (opacity : Float) (body : Draw → Draw) : Draw :=
  let layer := body
    { d with canvas := Canvas.new d.canvas.width d.canvas.height ⟨0, 0, 0, 0⟩ d.canvas.space }
  { d with canvas := d.canvas.compositeOver layer.canvas opacity }

end Draw

end PILean.Raster
