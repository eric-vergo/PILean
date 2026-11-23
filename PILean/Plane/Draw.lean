/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plane.Frame

/-!
# Plane figures: drawing

A `Figure` is a list of `Item`s, a page width (and optionally a height), a padding, a `Style` and
metadata. `Figure.frame` fits the items into the page (`Frame.fit`, every item's reaches: its
world points with the pixel extents of markers, strokes, arrowheads, angle marks and label boxes),
or fits a given world box; `Figure.draw` draws every item through that frame on the vector canvas,
the drawing `Figure.toSvg` and `Figure.toPng` (`PILean.Plane.Render`) write.

Every element is drawn in page coordinates: its world points go through `Frame.toScreen` and its
radii are multiplied by the scale, while stroke widths, markers, arrowheads, label sizes and
offsets stay in pixels. Colours come from `Style.plane` by role (`Tone`), so the same figure in
`Style.dark` is its dark twin.

* A point is a disc of the marker radius on a ring of the background colour.
* Lines, rays, segments, polylines, outlines, arcs and angle marks are stroked with round caps and
  joins; an arrowhead is a filled triangle whose tip is the end point, the stroke stopping at its
  base.
* A disk, a filled sector and a filled polygon are tinted with their colour at
  `PlaneStyle.fillOpacity` and outlined in it.
* A label is set by the style's text engine (`Style.text`; with `pilean-leantex`, LaTeX), its box
  `offset` pixels from its point in the direction of its placement, the text centred in the box.
* An item's metadata becomes a `Canvas.Shape.tagged` around its shapes.

## Main definitions

* `Env`, `drawGeom`, `drawItem`, `labelBox`, `geomReaches`, `itemReaches`.
* `Figure`, `Figure.frame`, `Figure.draw` (the outputs are in `PILean.Plane.Render`).
-/

namespace PILean.Plane

open Canvas

/-- What drawing needs: the frame and the style. -/
structure Env where
  /-- The map from world to page. -/
  frame : Frame
  /-- The style; plane figures use its `plane` colours and sizes, `background` and `text`. -/
  style : Style

/-- The box of a label relative to its point's page position (`y` down): `size` pixels high
text whose width the style's text engine measures, `offset` pixels away in the direction of
`place`; and the offset of the text's baseline middle from the point. -/
def labelBox (st : Style) (s : String) (size offset : Float) (place : Placement) : Box × Point :=
  let w := st.text.measure s size
  let asc := size * st.text.ascent
  let desc := size * st.text.descent
  let d := place.screenDir
  let reach := d.x.abs * w / 2 + d.y.abs * (asc + desc) / 2
  let c : Point := ⟨d.x * (offset + reach), d.y * (offset + reach)⟩
  (⟨c.x - w / 2, c.y - (asc + desc) / 2, c.x + w / 2, c.y + (asc + desc) / 2⟩,
    ⟨c.x, c.y + (asc - desc) / 2⟩)

/-- The angle (radians) of the vector `v` on the page. -/
def angleOf (v : Point) : Float := Float.atan2 v.y v.x

/-- The page points of an arc of the circle with page centre `c` and page radius `r` from world
angle `θ₀` to `θ₁`: the page angles are the world angles negated, since the page's `y` points
down. -/
def screenArc (c : Point) (r θ₀ θ₁ : Float) : Path := Path.arc c r (-θ₀) (-θ₁)

/-- A filled arrowhead with its tip at `tip`, pointing along the unit page vector `u`, `len`
pixels long and `2 hw` wide at its base. -/
def arrowHead (tip u : Point) (len hw : Float) (c : Rgba) : Shape :=
  let n : Point := ⟨-u.y, u.x⟩
  let base := tip - len * u
  .path ((((Path.empty.moveTo tip).lineTo (base + hw * n)).lineTo (base - hw * n)).close)
    (some (.solid c))

/-- The unit vector of `v`, or `(1, 0)` for a zero vector. -/
def unitOf (v : Point) : Point :=
  let n := v.norm
  if n > 0 then (1 / n) * v else ⟨1, 0⟩

namespace Env

/-- The plane colours and sizes. -/
def ps (e : Env) : PlaneStyle := e.style.plane

/-- The colour of a look. -/
def ink (e : Env) (l : Look) : Rgba := l.tone.resolve e.ps

/-- The stroke width of a look. -/
def width (e : Env) (l : Look) : Float := l.width.getD e.ps.lineWidth

/-- The stroke of a look. -/
def stroke (e : Env) (l : Look) : Line :=
  { ink := e.ink l, width := e.width l, cap := "round", join := "round", dash := l.dash }

/-- The tint of a look: its colour at the style's fill opacity. -/
def tint (e : Env) (l : Look) : Fill :=
  let c := e.ink l
  let a := (max 0 (min 1 e.ps.fillOpacity) * c.a.toFloat).round.toUInt8
  .solid { c with a }

/-- The marker of a point at a page position. -/
def marker (e : Env) (l : Look) (q : Point) : Array Shape :=
  let r := l.size.getD e.ps.markerRadius
  #[.path (Canvas.circle q (r + e.ps.markerRing)) (some (.solid e.style.background)),
    .path (Canvas.circle q r) (some (.solid (e.ink l)))]

/-- A stroked page path. -/
def strokePath (e : Env) (l : Look) (p : Path) : Shape := .path p none (some (e.stroke l))

/-- The page segment from `a` to `b` with an arrowhead at `b`: the stroke stops at the base of
the head. -/
def arrowTo (e : Env) (l : Look) (a b : Point) : Array Shape :=
  let u := unitOf (b - a)
  let len := e.ps.arrowLength
  let shaft := max 0 ((b - a).norm - len * 0.8)
  #[e.strokePath l (Path.polyline #[a, a + shaft * u]),
    arrowHead b u len e.ps.arrowHalfWidth (e.ink l)]

/-- An arc on the page with centre `c` and radius `r` (pixels) from world angle `θ₀` to `θ₁`,
with an arrowhead at `θ₁` when `head`: the arc stops at the head's base, and the head points along
the arc's direction there. -/
def arcShapes (e : Env) (l : Look) (c : Point) (r θ₀ θ₁ : Float) (head : Bool) : Array Shape :=
  if !head || r ≤ 0 then #[e.strokePath l (screenArc c r θ₀ θ₁)]
  else
    let len := e.ps.arrowLength
    let sign : Float := if θ₁ ≥ θ₀ then 1 else -1
    let back := min ((θ₁ - θ₀).abs) (len * 0.8 / r)
    let tip : Point := ⟨c.x + r * θ₁.cos, c.y - r * θ₁.sin⟩
    -- the direction of travel on the page at the end: the world tangent `sign (-sin, cos)`,
    -- its `y` negated; the head's axis is the chord from its base on the circle to the tip
    let baseθ := θ₁ - sign * len / r
    let base : Point := ⟨c.x + r * baseθ.cos, c.y - r * baseθ.sin⟩
    #[e.strokePath l (screenArc c r θ₀ (θ₁ - sign * back)),
      arrowHead tip (unitOf (tip - base)) len e.ps.arrowHalfWidth (e.ink l)]

end Env

/-- The shapes of an element with a look, drawn through the environment's frame. -/
def drawGeom (e : Env) (l : Look) : Geom → Array Shape
  | .point p => e.marker l (e.frame.toScreen p)
  | .segment a b =>
    if l.arrowHead then e.arrowTo l (e.frame.toScreen a) (e.frame.toScreen b)
    else #[e.strokePath l (Path.polyline #[e.frame.toScreen a, e.frame.toScreen b])]
  | .line a b =>
    match clipLine (e.frame.toScreen a) (e.frame.toScreen b)
        ⟨0, 0, e.frame.width, e.frame.height⟩ with
    | some (p, q) => #[e.strokePath l (Path.polyline #[p, q])]
    | none => #[]
  | .ray a b =>
    match clipLine (e.frame.toScreen a) (e.frame.toScreen b)
        ⟨0, 0, e.frame.width, e.frame.height⟩ (ray := true) with
    | some (p, q) =>
      if l.arrowHead then e.arrowTo l p q else #[e.strokePath l (Path.polyline #[p, q])]
    | none => #[]
  | .arrow a b => e.arrowTo l (e.frame.toScreen a) (e.frame.toScreen b)
  | .circle c r => #[e.strokePath l (Canvas.circle (e.frame.toScreen c) (e.frame.scale * r))]
  | .disk c r =>
    #[.path (Canvas.circle (e.frame.toScreen c) (e.frame.scale * r)) (some (e.tint l))
      (some (e.stroke l))]
  | .arc c r θ₀ θ₁ => e.arcShapes l (e.frame.toScreen c) (e.frame.scale * r) θ₀ θ₁ l.arrowHead
  | .sector c r θ₀ θ₁ =>
    let q := e.frame.toScreen c
    let r := e.frame.scale * r
    let p := ((Path.empty.moveTo q).arcTo q r (-θ₀) (-θ₁)).close
    #[.path p (if l.filled then some (e.tint l) else none) (some (e.stroke l))]
  | .polygon vs =>
    #[.path (Path.polyline (vs.map e.frame.toScreen)).close
      (if l.filled then some (e.tint l) else none) (some (e.stroke l))]
  | .polyline vs =>
    if l.arrowHead && vs.size ≥ 2 then
      let qs := vs.map e.frame.toScreen
      #[e.strokePath l (Path.polyline qs.pop)] ++
        e.arrowTo l (qs[qs.size - 2]!) (qs[qs.size - 1]!)
    else #[e.strokePath l (Path.polyline (vs.map e.frame.toScreen))]
  | .angleMark c θ₀ θ₁ radius =>
    e.arcShapes l (e.frame.toScreen c) (radius.getD e.ps.angleRadius) θ₀ θ₁ true
  | .label s p place offset =>
    let size := l.size.getD e.ps.labelSize
    let (_, base) := labelBox e.style s size (offset.getD e.ps.labelOffset) place
    let q := e.frame.toScreen p
    #[.text s (q + base) size (e.ink l) .middle]

/-- An item's shapes: its element's (`drawGeom`) or its items' in order, inside a
`Shape.tagged` when it has metadata. -/
def drawItem (e : Env) : Item → Array Shape
  | .shape g l i => if i.isEmpty then drawGeom e l g else #[.tagged i (.group (drawGeom e l g))]
  | .group xs i =>
    let inner := xs.attach.flatMap fun ⟨x, _⟩ => drawItem e x
    if i.isEmpty then inner else #[.tagged i (.group inner)]

/-- The world points of an angle range of a circle where it reaches farthest along an axis:
its ends and the points at the multiples of a quarter turn inside the range. -/
def arcExtremes (c : Point) (r θ₀ θ₁ : Float) : Array Point := Id.run do
  let lo := min θ₀ θ₁
  let hi := max θ₀ θ₁
  let mut out := #[c + polar r θ₀, c + polar r θ₁]
  if hi - lo ≥ 2 * pi then
    return out ++ #[c + polar r 0, c + polar r (pi / 2), c + polar r pi, c + polar r (3 * pi / 2)]
  let k0 := (lo / (pi / 2)).ceil
  for i in [0:5] do
    let a := (k0 + i.toFloat) * (pi / 2)
    if a ≤ hi then out := out.push (c + polar r a)
  return out

/-- The reaches of an element with a look (see `Reach`): what the frame must hold for it to be
seen whole. Lines and rays reach their two given points. -/
def geomReaches (st : Style) (l : Look) : Geom → Array Reach
  | .point p =>
    #[Reach.around p (l.size.getD st.plane.markerRadius + st.plane.markerRing)]
  | .segment a b | .line a b | .ray a b | .arrow a b =>
    let w := max (l.width.getD st.plane.lineWidth / 2) st.plane.arrowHalfWidth
    #[Reach.around a w, Reach.around b w]
  | .circle c r | .disk c r =>
    let w := l.width.getD st.plane.lineWidth / 2
    #[Reach.around ⟨c.x - r, c.y⟩ w, Reach.around ⟨c.x + r, c.y⟩ w,
      Reach.around ⟨c.x, c.y - r⟩ w, Reach.around ⟨c.x, c.y + r⟩ w]
  | .arc c r θ₀ θ₁ =>
    let w := max (l.width.getD st.plane.lineWidth / 2)
      (if l.arrowHead then st.plane.arrowHalfWidth else 0)
    (arcExtremes c r θ₀ θ₁).map (Reach.around · w)
  | .sector c r θ₀ θ₁ =>
    let w := l.width.getD st.plane.lineWidth / 2
    ((arcExtremes c r θ₀ θ₁).push c).map (Reach.around · w)
  | .polygon vs | .polyline vs =>
    let w := max (l.width.getD st.plane.lineWidth / 2)
      (if l.arrowHead then st.plane.arrowHalfWidth else 0)
    vs.map (Reach.around · w)
  | .angleMark c _ _ radius =>
    #[Reach.around c (radius.getD st.plane.angleRadius + st.plane.arrowHalfWidth)]
  | .label s p place offset =>
    let size := l.size.getD st.plane.labelSize
    #[⟨p, (labelBox st s size (offset.getD st.plane.labelOffset) place).1⟩]

/-- The reaches of an item and of every item in it. -/
def itemReaches (st : Style) : Item → Array Reach
  | .shape g l _ => geomReaches st l g
  | .group xs _ => xs.attach.flatMap fun ⟨x, _⟩ => itemReaches st x

/-- A figure of plane geometry (see the module docstring). -/
structure Figure where
  /-- The items, drawn in order (later ones on top). -/
  items : Array Item
  /-- The width of the page in pixels. -/
  width : Float := 480
  /-- The height of the page in pixels; `none` makes it as tall as the items need. -/
  height : Option Float := none
  /-- The room in pixels between what is drawn and the edge of the page. -/
  padding : Float := 12
  /-- The world box to show (`y0` the lowest ordinate); `none` fits the items. -/
  view : Option Box := none
  /-- The style: `plane` colours and sizes, `background`, `text` and `fontFamily`. -/
  style : Style := {}
  /-- Metadata of the whole drawing (its title and description). -/
  info : ShapeInfo := {}
  /-- How the layout checks are applied when the figure is rendered (`PILean.Plane.Check`). -/
  checks : CheckLevel := .warn
  deriving Inhabited

namespace Figure

/-- The frame: the items' reaches fitted into the page, or the world box `view` fitted with no
pixel extents. -/
def frame (fig : Figure) : Frame :=
  let reaches := match fig.view with
    | some b => #[Reach.around ⟨b.x0, b.y0⟩ 0, Reach.around ⟨b.x1, b.y1⟩ 0]
    | none => fig.items.flatMap (itemReaches fig.style)
  Frame.fit reaches fig.width fig.height fig.padding

/-- The drawing environment: the frame and the style. -/
def env (fig : Figure) : Env := { frame := fig.frame, style := fig.style }

/-- The background: the page filled with the style's background colour. -/
def background (fig : Figure) : Shape :=
  .path (Canvas.rect 0 0 fig.frame.width fig.frame.height) (some (.solid fig.style.background))

/-- The figure on the canvas: the background, then every item in order, inside the figure's
metadata. -/
def draw (fig : Figure) : Shape :=
  .tagged fig.info (.group (#[fig.background] ++ fig.items.flatMap (drawItem fig.env)))

/-- The page size in whole pixels. -/
def pixelSize (fig : Figure) : Nat × Nat :=
  (fig.frame.width.round.toUInt64.toNat, fig.frame.height.round.toUInt64.toNat)

/-- The drawing is the background and then each item's shapes, in order, inside the figure's
metadata. -/
theorem draw_eq (fig : Figure) :
    fig.draw = .tagged fig.info (.group (#[fig.background] ++
      fig.items.flatMap (drawItem fig.env))) := rfl

end Figure

end PILean.Plane
