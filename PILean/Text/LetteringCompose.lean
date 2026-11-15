/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Text.LetteringGlyphs

/-!
# Lettering glyph data: building designs from designs

Transformations of a glyph design (scale, shift, mirror, turn, flip) and the diacritical marks of
the built-in single-stroke typeface. The scripts, the accented letters and the composed signs are
generated from the regular designs with these, so that they keep the regular stroke width and
shapes. All coordinates are centre-line coordinates in em units of 1000, `y` up.

## Main definitions

* `Lettering.Piece.affine`, `Spec.scaled`, `Spec.shifted`, `Spec.mirrored`, `Spec.turned`,
  `Spec.flipped`: the transformations (the stroke width is not changed by any of them).
* `Lettering.Spec.centreX`: the horizontal centre of a design's centre lines.
* `Lettering.Mark`, `Lettering.Mark.strokes`: the diacritics and their strokes.
-/

namespace PILean.Lettering

open Piece

/-- The piece scaled by `sx`, `sy` (both positive) and then shifted by `dx`, `dy`. -/
def Piece.affine (sx sy dx dy : Float) : Piece → Piece
  | .pt x y => .pt (sx * x + dx) (sy * y + dy)
  | .arc cx cy rx ry a0 a1 => .arc (sx * cx + dx) (sy * cy + dy) (sx * rx) (sy * ry) a0 a1

/-- The piece mirrored at the vertical line `x = w / 2` (that is, `x ↦ w - x`). -/
def Piece.mirror (w : Float) : Piece → Piece
  | .pt x y => .pt (w - x) y
  | .arc cx cy rx ry a0 a1 => .arc (w - cx) cy rx ry (180 - a0) (180 - a1)

/-- The piece turned by half a revolution about `(w / 2, h / 2)` (`(x, y) ↦ (w - x, h - y)`). -/
def Piece.turn (w h : Float) : Piece → Piece
  | .pt x y => .pt (w - x) (h - y)
  | .arc cx cy rx ry a0 a1 => .arc (w - cx) (h - cy) rx ry (a0 + 180) (a1 + 180)

/-- The piece mirrored at the horizontal line `y = h / 2` (that is, `y ↦ h - y`). -/
def Piece.flip (h : Float) : Piece → Piece
  | .pt x y => .pt x (h - y)
  | .arc cx cy rx ry a0 a1 => .arc cx (h - cy) rx ry (-a0) (-a1)

/-- The stroke with `f` applied to every piece. -/
def Stroke.map (f : Piece → Piece) (s : Stroke) : Stroke := { s with pieces := s.pieces.map f }

/-- The design with `f` applied to every piece of every stroke; the bearings are kept. -/
def Spec.map (f : Piece → Piece) (g : Spec) : Spec := { g with strokes := g.strokes.map (·.map f) }

/-- The design scaled by `k > 0` and shifted by `(dx, dy)`. The stroke width is not scaled; the
bearings are scaled and widened by `10` units, and a fixed advance by `50`, so that the smaller
forms keep room for their strokes. -/
def Spec.scaled (g : Spec) (k dx dy : Float) : Spec :=
  { (g.map (Piece.affine k k dx dy)) with
    lsb := k * g.lsb + 10, rsb := k * g.rsb + 10, fixed := g.fixed.map (k * · + 50) }

/-- The design shifted by `(dx, dy)`. -/
def Spec.shifted (g : Spec) (dx dy : Float) : Spec := g.map (Piece.affine 1 1 dx dy)

/-- The design mirrored left to right within the width `w` (the bearings are swapped). -/
def Spec.mirrored (g : Spec) (w : Float) : Spec :=
  { (g.map (Piece.mirror w)) with lsb := g.rsb, rsb := g.lsb }

/-- The design turned by half a revolution within `w × h` (the bearings are swapped). -/
def Spec.turned (g : Spec) (w h : Float) : Spec :=
  { (g.map (Piece.turn w h)) with lsb := g.rsb, rsb := g.lsb }

/-- The design mirrored top to bottom within the height `h`. -/
def Spec.flipped (g : Spec) (h : Float) : Spec := g.map (Piece.flip h)

/-- The design with more strokes. -/
def Spec.withStrokes (g : Spec) (ss : List Stroke) : Spec := { g with strokes := g.strokes ++ ss }

/-- The design with the strokes of another design (the bearings are the first design's). -/
def Spec.append (g h : Spec) : Spec := { g with strokes := g.strokes ++ h.strokes }

/-- The horizontal centre of the design's centre lines (`0` for an empty design). -/
def Spec.centreX (g : Spec) : Float :=
  match g.rawPath.bounds with
  | some b => (b.x0 + b.x1) / 2
  | none => 0

/-- The diacritical marks. -/
inductive Mark where
  /-- The grave accent. -/
  | grave
  /-- The acute accent. -/
  | acute
  /-- The circumflex. -/
  | circumflex
  /-- The tilde. -/
  | tilde
  /-- The diaeresis. -/
  | diaeresis
  /-- The ring above. -/
  | ringAbove
  /-- The cedilla. -/
  | cedilla
  deriving DecidableEq

/-- The strokes of a mark centred at `x = cx`: above the x-height of a lowercase letter, or
(`cap`) above the cap height; the cedilla hangs below the baseline either way. The ring above a
capital sits on the stroke ends of the letter, so that it stays within `900` units. -/
def Mark.strokes (m : Mark) (cx : Float) (cap : Bool) : List Stroke :=
  let u : Float := if cap then 175 else 0
  match m with
  | .grave => [stroke [pt (cx - 40) (685 + u), pt (cx + 40) (600 + u)]]
  | .acute => [stroke [pt (cx - 40) (600 + u), pt (cx + 40) (685 + u)]]
  | .circumflex => [stroke [pt (cx - 65) (600 + u), pt cx (685 + u), pt (cx + 65) (600 + u)]]
  | .tilde => [stroke [arc (cx - 50) (640 + u) 50 35 180 0, arc (cx + 50) (640 + u) 50 35 180 360]]
  | .diaeresis => [dot (cx - 85) (625 + u), dot (cx + 85) (625 + u)]
  | .ringAbove => if cap then [ring cx 790 55 55] else [ring cx 648 58 58]
  | .cedilla => [stroke [pt cx 20, pt cx (-30), arc cx (-85) 50 55 90 (-150)]]

end PILean.Lettering
