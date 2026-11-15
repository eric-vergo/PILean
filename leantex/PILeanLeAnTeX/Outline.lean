/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import LeAnTeX
import PILean

/-!
# Display lists as outlines

LeAnTeX's display list (glyphs, rules and path pictures at TeX's positions) as one PILean `Path`
to fill: the shapes its SVG back end draws, in pixels, with the baseline origin of the first
line at `(0, 0)` and `y` down.

* **Glyphs** are their outlines from the fonts of the `FontSet`, scaled to their size, slanted,
  mirrored and offset (`\pmb`'s shadow) as `LeAnTeX.Backend.pictureParts` places them; a
  character no font has, and a glyph whose outline cannot be read, is the missing-glyph box.
* **Rules** are rectangles.
* **Path pictures** (KaTeX's radicals, wide accents and arrows) are read from their SVG path
  data, mapped into their rectangle by their `viewBox` and `preserveAspectRatio`, flattened and
  clipped to the rectangle and to the item's own clip, as the nested `svg` elements of the SVG
  back end clip them.
* **Colours and images** are not drawn apart: the shape is filled with one paint, and a label
  carries no images.

## Main definitions

* `outline`: a display list as a path, given the size of its em in pixels.
-/

namespace PILeanLeAnTeX

open PILean
open LeAnTeX LeAnTeX.Backend

/-- An axis-aligned rectangle: left, top, right, bottom. -/
structure Rect where
  /-- Left. -/
  x0 : Float
  /-- Top. -/
  y0 : Float
  /-- Right. -/
  x1 : Float
  /-- Bottom. -/
  y1 : Float
  deriving Inhabited, Repr

/-- The intersection of two rectangles (possibly empty: `x1 ≤ x0` or `y1 ≤ y0`). -/
def Rect.inter (a b : Rect) : Rect :=
  ⟨max a.x0 b.x0, max a.y0 b.y0, min a.x1 b.x1, min a.y1 b.y1⟩

/-- One step of Sutherland and Hodgman's clipping of a closed polygon: the part of `ps` where
`inside` holds, with the crossings of the boundary found by `cross`. -/
def clipEdge (ps : Array Point) (inside : Point → Bool) (cross : Point → Point → Point) :
    Array Point := Id.run do
  let mut out := #[]
  for h : i in [0:ps.size] do
    let cur := ps[i]
    let prev := ps[(i + ps.size - 1) % ps.size]!
    if inside cur then
      if !inside prev then out := out.push (cross prev cur)
      out := out.push cur
    else if inside prev then out := out.push (cross prev cur)
  return out

/-- The point where the segment from `p` to `q` meets the vertical line at `x`. -/
def atX (x : Float) (p q : Point) : Point :=
  let t := if q.x == p.x then 0 else (x - p.x) / (q.x - p.x)
  ⟨x, p.y + t * (q.y - p.y)⟩

/-- The point where the segment from `p` to `q` meets the horizontal line at `y`. -/
def atY (y : Float) (p q : Point) : Point :=
  let t := if q.y == p.y then 0 else (y - p.y) / (q.y - p.y)
  ⟨p.x + t * (q.x - p.x), y⟩

/-- A closed polygon clipped to a rectangle. Clipping each contour of a filled path to a convex
region keeps the winding number of every point inside the region, so the clipped contours fill
what the path fills inside it. -/
def clipPolygon (ps : Array Point) (r : Rect) : Array Point :=
  let a := clipEdge ps (·.x ≥ r.x0) (atX r.x0)
  let b := clipEdge a (·.x ≤ r.x1) (atX r.x1)
  let c := clipEdge b (·.y ≥ r.y0) (atY r.y0)
  clipEdge c (·.y ≤ r.y1) (atY r.y1)

/-- A path flattened (to `tol` pixels) and clipped to a rectangle, as closed polygons. -/
def clipPath (p : Path) (r : Rect) (tol : Float := 0.05) : Path := Id.run do
  if r.x1 ≤ r.x0 || r.y1 ≤ r.y0 then return {}
  let mut out : Path := {}
  for pl in p.flatten tol do
    let q := clipPolygon pl.points r
    if q.size < 3 then continue
    out := (q.toList.drop 1).foldl (fun acc pt => acc.lineTo pt) (out.moveTo q[0]!) |>.close
  return out

/-- A glyph outline (in 1/65536 font units, `y` up) as a PILean path in font units, `y` down. -/
def glyphPath (p : LeAnTeX.Path Int) : PILean.Path :=
  let pt := fun (q : LeAnTeX.Point Int) => (⟨Float.ofInt q.x / 65536, -Float.ofInt q.y / 65536⟩ :
    PILean.Point)
  ⟨p.cmds.map fun
    | .move q => .move (pt q)
    | .line q => .line (pt q)
    | .quad a q => .quad (pt a) (pt q)
    | .cubic a b q => .cubic (pt a) (pt b) (pt q)
    | .close => .close⟩

/-- The missing-glyph box in thousandths of an em, `y` down (`LeAnTeX.Backend.notdefPath`). -/
def notdefPath : PILean.Path :=
  (PILean.Path.rect 50 (-700) 500 700).append <|
    PILean.Path.empty.moveTo ⟨110, -60⟩ |>.lineTo ⟨110, -640⟩ |>.lineTo ⟨490, -640⟩
      |>.lineTo ⟨490, -60⟩ |>.close

/-- The alignment of `preserveAspectRatio` on one axis: 0 for `Min`, ½ for `Mid`, 1 for `Max`. -/
def alignOf (par : String) (axis : String) : Float :=
  if (par.splitOn (axis ++ "Mid")).length > 1 then 0.5
  else if (par.splitOn (axis ++ "Max")).length > 1 then 1 else 0

/-- The numbers of a `viewBox`: `min-x min-y width height`. -/
def viewBoxOf (vb : String) : Option (Float × Float × Float × Float) :=
  let ns := ((vb.splitOn " ").filter (!·.isEmpty)).filterMap Raster.parseNumber?
  match ns with
  | [x, y, w, h] => if w > 0 && h > 0 then some (x, y, w, h) else none
  | _ => none

/-- The transformation that maps a `viewBox` into the rectangle `(px, py, w, h)` as
`preserveAspectRatio` says. -/
def viewBoxMap (vb : Float × Float × Float × Float) (par : String) (px py w h : Float) :
    Affine :=
  let (vx, vy, vw, vh) := vb
  let (sx, sy) := (w / vw, h / vh)
  if par.trimAscii.toString == "none" then
    { a := sx, d := sy, e := px - vx * sx, f := py - vy * sy }
  else
    let s := if (par.splitOn "slice").length > 1 then max sx sy else min sx sy
    let ox := (w - vw * s) * alignOf par "x"
    let oy := (h - vh * s) * alignOf par "Y"
    { a := s, d := s, e := px + ox - vx * s, f := py + oy - vy * s }

/-- Whether item `i` is drawn mirrored. -/
def mirroredAt (dl : DisplayList) (i : Nat) : Bool :=
  dl.mirrored.any fun (a, b) => a ≤ i && i < b

/-- The display list `dl`, whose em is `em` sp, as one path to fill, in pixels for `k` pixels
per sp (see the module docstring). -/
def outline (fs : FontSet) (dl : DisplayList) (em : Int) (k : Float) : PILean.Path := Id.run do
  let sp := fun (e : Em) => Float.ofInt (spOf em e)
  let mut out : PILean.Path := {}
  for (line, lxI, lyI) in linePlacement dl em do
    let (lx, ly) := (Float.ofInt lxI, Float.ofInt lyI)
    for i in [line.start:line.stop] do
      let some it := dl.items[i]? | continue
      match it with
      | .glyph face c x y size _ shadow _ _ =>
        let s := sp size
        let (dx, dy) := if shadow then (s * 0.02, s * 0.01) else (0, 0)
        let ox := lx + sp x + dx
        let oy := ly + sp y + dy
        let drawn : Option (PILean.Path × Float) := do
          let r ← fs.resolve face c
          let f ← fs.fonts[r.font]?
          let p ← match f.outline r.glyph with
            | .ok p => some p
            | .error _ => none
          return (glyphPath p, Float.ofNat f.unitsPerEm)
        let (shape, upem) := drawn.getD (notdefPath, 1000)
        let ks := s / upem
        let a := if mirroredAt dl i then -ks else ks
        -- the back end's placement of glyphs New Computer Modern draws elsewhere than KaTeX
        let pl := if drawn.isSome then fs.placement face c else {}
        let m : Affine := { a := a * k, c := -(Float.ofInt face.slant / 1000) * ks * k,
                            d := ks * k * Float.ofNat pl.yScale / 1000,
                            e := (ox + Float.ofInt pl.dx * ks) * k,
                            f := (oy - Float.ofInt pl.dy * ks) * k }
        out := out.append (shape.transform m)
      | .rule x y w h _ _ =>
        out := out.append (PILean.Path.rect ((lx + sp x) * k) ((ly + sp y) * k) (sp w * k)
          (sp h * k))
      | .path data vb par x y w h clip _ _ =>
        let some box := viewBoxOf vb | continue
        let (px, py, pw, ph) := ((lx + sp x) * k, (ly + sp y) * k, sp w * k, sp h * k)
        let m := viewBoxMap box par px py pw ph
        let m := if mirroredAt dl i then
            (({ a := -1, e := 2 * px + pw } : Affine)).comp m else m
        let mut r : Rect := ⟨px, py, px + pw, py + ph⟩
        if let some (cx, cy, cw, ch) := clip then
          let c0x := (lx + sp cx) * k
          let c0y := (ly + sp cy) * k
          r := r.inter ⟨c0x, c0y, c0x + sp cw * k, c0y + sp ch * k⟩
        out := out.append (clipPath ((Raster.parsePathData data).transform m) r)
      | .image .. => pure ()
  return out

end PILeanLeAnTeX
