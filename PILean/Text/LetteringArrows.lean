/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Text.LetteringCompose

/-!
# Lettering glyph data: arrows

The designs of the arrows of the built-in single-stroke typeface (the glyph shapes are the
authors' own design): the single arrows, the double arrows, the maps-to arrow and the diagonal
arrows. The heads are open chevrons at 45°.

## Main definitions

* `Lettering.arrows`: `← → ↑ ↓ ↔ ↕ ⇐ ⇒ ⇔ ↦ ↗ ↘`.
-/

namespace PILean.Lettering

open Piece

/-- The head of a single arrow pointing right with its tip at `(x, y)`. -/
def headRight (x y : Float) : Stroke :=
  stroke [pt (x - 170) (y + 170), pt x y, pt (x - 170) (y - 170)]

/-- The head of a vertical arrow with its tip at `(x, y)`, pointing up (`up`) or down. -/
def headVertical (x y : Float) (up : Bool) : Stroke :=
  let d : Float := if up then -170 else 170
  stroke [pt (x - 170) (y + d), pt x y, pt (x + 170) (y + d)]

/-- A double arrow pointing right: two bars and a head with its tip at `(w, 330)`; `x0` is where
the bars start. -/
def doubleRight (x0 w : Float) : List Stroke :=
  [stroke [pt x0 410, pt (w - 70) 410], stroke [pt x0 250, pt (w - 70) 250],
   stroke [pt (w - 220) 580, pt w 330, pt (w - 220) 80]]

/-- The arrows. -/
def arrows : Char → Option Spec
  | '→' => some (spec [stroke [pt 0 330, pt 560 330], headRight 560 330] 50 50)
  | '←' => some ((spec [stroke [pt 0 330, pt 560 330], headRight 560 330] 50 50).mirrored 560)
  | '↔' => some (spec [stroke [pt 0 330, pt 700 330], headRight 700 330,
      stroke [pt 170 500, pt 0 330, pt 170 160]] 50 50)
  | '↑' => some (spec [stroke [pt 0 (-10), pt 0 650], headVertical 0 650 true] 50 50)
  | '↓' => some (spec [stroke [pt 0 (-10), pt 0 650], headVertical 0 (-10) false] 50 50)
  | '↕' => some (spec [stroke [pt 0 (-10), pt 0 650], headVertical 0 650 true,
      headVertical 0 (-10) false] 50 50)
  | '⇒' => some (spec (doubleRight 0 450) 50 50)
  | '⇐' => some ((spec (doubleRight 0 450) 50 50).mirrored 450)
  | '⇔' => some (spec [stroke [pt 75 410, pt 605 410], stroke [pt 75 250, pt 605 250],
      stroke [pt 460 580, pt 680 330, pt 460 80], stroke [pt 220 580, pt 0 330, pt 220 80]] 50 50)
  | '↦' => some (spec [stroke [pt 0 330, pt 560 330], headRight 560 330,
      stroke [pt 0 170, pt 0 490]] 50 50)
  | '↗' => some (spec [stroke [pt 0 60, pt 440 500], stroke [pt 150 500, pt 440 500, pt 440 210]]
      50 50)
  | '↘' => some (spec [stroke [pt 0 600, pt 440 160], stroke [pt 150 160, pt 440 160, pt 440 450]]
      50 50)
  | _ => none

end PILean.Lettering
