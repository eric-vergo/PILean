/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Path

/-!
# Lettering glyph data: the building blocks and the Latin letters

The glyph shapes of the built-in single-stroke typeface are the authors' own design; no existing
font's data was used. A glyph is a few strokes, each a centre line made of straight segments and
elliptical arcs, in em units of 1000 with `y` up and the baseline at `y = 0`. The renderer strokes
the centre lines with round caps and round joins at `78` units, so a flat cap-height stroke runs
at `y = 661` (ink to `700`), a flat x-height stroke at `471` (ink to `510`), and round letters
overshoot by about ten units.

## Main definitions

* `Lettering.Piece`, `Lettering.Stroke`, `Lettering.Spec`: the data model: points and arcs,
  strokes of them, and a glyph's strokes with its side bearings.
* `Lettering.Stroke.toPath`: the stroke as a path (arcs as cubic Béziers of at most 90°).
* `Lettering.Spec.toGlyph`: the strokes placed by their side bearings, with the advance.
* `Lettering.latinSpec`: the specifications of the Latin letters and the digits.

## Implementation notes

The side bearings are measured to the edge of the ink, so the centre lines start `39` units
inside them. A glyph's coordinates need not start at zero: the glyph is shifted so that its ink has
the bearing on each side. Digits are centred in a fixed advance of `560` so that columns of
numbers align.
-/

namespace PILean.Lettering

/-- A piece of a stroke: a point (joined to the previous one by a straight segment) or an
elliptical arc about `(cx, cy)` with radii `rx`, `ry`, from angle `a0` to `a1` in degrees
(counter-clockwise for `a1 > a0`, `y` up), joined to the previous piece by a straight segment
when it does not start at the current point. -/
inductive Piece where
  /-- A point. -/
  | pt (x y : Float)
  /-- An elliptical arc. -/
  | arc (cx cy rx ry a0 a1 : Float)
  deriving Inhabited

/-- A stroke: a centre line, open or closed. -/
structure Stroke where
  /-- The pieces in order. -/
  pieces : List Piece
  /-- Whether the last piece joins back to the first. -/
  closed : Bool := false

/-- An open stroke. -/
def stroke (ps : List Piece) : Stroke := ⟨ps, false⟩

/-- A closed stroke. -/
def loop (ps : List Piece) : Stroke := ⟨ps, true⟩

/-- A glyph's design: strokes, the ink bearings, and a fixed advance if the glyph is centred in
one. -/
structure Spec where
  /-- The strokes. -/
  strokes : List Stroke
  /-- The space from the advance's left edge to the ink. -/
  lsb : Float := 70
  /-- The space from the ink to the advance's right edge. -/
  rsb : Float := 70
  /-- The advance, for glyphs centred in a fixed one (otherwise from the ink and bearings). -/
  fixed : Option Float := none

/-- A glyph design with the bearings. -/
def spec (strokes : List Stroke) (lsb rsb : Float := 70) : Spec := { strokes, lsb, rsb }

/-- A glyph design centred in the advance `adv`. -/
def centred (adv : Float) (strokes : List Stroke) : Spec := { strokes, fixed := some adv }

open Piece

/-- The ratio `π / 180`. -/
def degToRad : Float := 0.017453292519943295

/-- The cubic arcs of an elliptical arc (`cx`, `cy`, `rx`, `ry`, from `a0` to `a1` degrees) added
to a path whose current point is the arc's start. At most 90° per cubic. -/
def addArc (path : Path) (cx cy rx ry a0 a1 : Float) : Path := Id.run do
  let sweep := a1 - a0
  let c := (sweep.abs / 90 - 1e-9).ceil
  let n := if c < 1 then 1 else c
  let step := sweep / n * degToRad
  let k := 4 / 3 * (step / 4).tan
  let mut path := path
  for i in List.range n.toUInt64.toNat do
    let t0 := a0 * degToRad + step * i.toFloat
    let t1 := t0 + step
    let c0 := t0.cos
    let s0 := t0.sin
    let c1 := t1.cos
    let s1 := t1.sin
    path := path.cubicTo ⟨cx + rx * (c0 - k * s0), cy + ry * (s0 + k * c0)⟩
      ⟨cx + rx * (c1 + k * s1), cy + ry * (s1 - k * c1)⟩ ⟨cx + rx * c1, cy + ry * s1⟩
  return path

/-- The start of an arc. -/
def arcStart (cx cy rx ry a0 : Float) : Point :=
  ⟨cx + rx * (a0 * degToRad).cos, cy + ry * (a0 * degToRad).sin⟩

/-- The end of an arc. -/
def arcEnd (cx cy rx ry a1 : Float) : Point := arcStart cx cy rx ry a1

/-- The stroke as a path (a `move` and then lines and cubic arcs; closed if the stroke is). -/
def Stroke.toPath (s : Stroke) : Path := Id.run do
  let mut path : Path := {}
  let mut cur : Option Point := none
  for p in s.pieces do
    match p with
    | .pt x y =>
      path := if cur.isNone then path.moveTo ⟨x, y⟩ else path.lineTo ⟨x, y⟩
      cur := some ⟨x, y⟩
    | .arc cx cy rx ry a0 a1 =>
      let st := arcStart cx cy rx ry a0
      match cur with
      | none => path := path.moveTo st
      | some q => if q.dist st > 0.5 then path := path.lineTo st
      path := addArc path cx cy rx ry a0 a1
      cur := some (arcEnd cx cy rx ry a1)
  return if s.closed then path.close else path

/-- The centre lines of the design's strokes as one path, unshifted. -/
def Spec.rawPath (g : Spec) : Path :=
  g.strokes.foldl (fun acc s => acc.append s.toPath) {}

/-- The ellipse as a closed stroke. -/
def ring (cx cy rx ry : Float) : Stroke := loop [arc cx cy rx ry 90 (-270)]

/-- A dot: a very short stroke, drawn as a round cap. -/
def dot (x y : Float) : Stroke := stroke [pt x y, pt x (y + 1)]

/-- The Latin capitals. -/
def capitals : Char → Option Spec
  | 'A' => some (spec [stroke [pt 0 39, pt 280 661, pt 560 39],
      stroke [pt 80 215, pt 480 215]] 25 25)
  | 'B' => some (spec [stroke [pt 0 39, pt 0 661, pt 200 661, arc 200 506 150 155 90 (-90),
      pt 0 351], stroke [pt 0 351, pt 215 351, arc 215 195 170 156 90 (-90), pt 0 39]] 70 50)
  | 'C' => some (spec [stroke [arc 305 350 300 321 40 320]] 45 45)
  | 'D' => some (spec [loop [pt 0 39, pt 0 661, pt 245 661, arc 245 350 300 311 90 (-90)]] 70 45)
  | 'E' => some (spec [stroke [pt 330 661, pt 0 661, pt 0 39, pt 330 39],
      stroke [pt 0 350, pt 290 350]] 70 40)
  | 'F' => some (spec [stroke [pt 310 661, pt 0 661, pt 0 39], stroke [pt 0 350, pt 280 350]] 70 40)
  | 'G' => some (spec [stroke [arc 305 350 300 321 40 360, pt 330 350]] 45 60)
  | 'H' => some (spec [stroke [pt 0 39, pt 0 661], stroke [pt 440 39, pt 440 661],
      stroke [pt 0 350, pt 440 350]])
  | 'I' => some (spec [stroke [pt 0 39, pt 0 661]] 80 80)
  | 'J' => some (spec [stroke [pt 310 661, pt 310 190, arc 160 190 150 161 0 (-180)]] 50 70)
  | 'K' => some (spec [stroke [pt 0 39, pt 0 661], stroke [pt 400 661, pt 0 245],
      stroke [pt 120 370, pt 420 39]] 70 25)
  | 'L' => some (spec [stroke [pt 0 661, pt 0 39, pt 320 39]] 70 30)
  | 'M' => some (spec [stroke [pt 0 39, pt 0 661, pt 270 39, pt 540 661, pt 540 39]])
  | 'N' => some (spec [stroke [pt 0 39, pt 0 661, pt 430 39, pt 430 661]])
  | 'O' => some (spec [ring 305 350 305 321] 45 45)
  | 'P' => some (spec [stroke [pt 0 39, pt 0 661], stroke [pt 0 661, pt 210 661,
      arc 210 475 160 186 90 (-90), pt 0 289]] 70 45)
  | 'Q' => some (spec [ring 305 350 305 321, stroke [pt 390 170, pt 520 30]] 45 45)
  | 'R' => some (spec [stroke [pt 0 39, pt 0 661], stroke [pt 0 661, pt 210 661,
      arc 210 475 160 186 90 (-90), pt 0 289], stroke [pt 190 289, pt 400 39]] 70 40)
  | 'S' => some (spec [stroke [arc 160 521 140 150 30 270, arc 160 200 160 171 90 (-150)]] 45 45)
  | 'T' => some (spec [stroke [pt 0 661, pt 440 661], stroke [pt 220 661, pt 220 39]] 20 20)
  | 'U' => some (spec [stroke [pt 0 661, pt 0 220, arc 215 220 215 191 180 360, pt 430 661]])
  | 'V' => some (spec [stroke [pt 0 661, pt 270 39, pt 540 661]] 25 25)
  | 'W' => some (spec [stroke [pt 0 661, pt 195 39, pt 390 661, pt 585 39, pt 780 661]] 25 25)
  | 'X' => some (spec [stroke [pt 0 661, pt 430 39], stroke [pt 430 661, pt 0 39]] 30 30)
  | 'Y' => some (spec [stroke [pt 0 661, pt 240 330, pt 480 661], stroke [pt 240 330, pt 240 39]]
      25 25)
  | 'Z' => some (spec [stroke [pt 0 661, pt 400 661, pt 0 39, pt 400 39]] 45 45)
  | _ => none

end PILean.Lettering
