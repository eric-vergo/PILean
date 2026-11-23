/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Text.LetteringGlyphs

/-!
# Lettering glyph data: punctuation and basic mathematical signs

The designs of the ASCII punctuation, the quotes and dashes, the signs of arithmetic and the
basic relations of the built-in single-stroke typeface (the glyph shapes are the authors' own
design).

## Main definitions

* `Lettering.punctuation`: the ASCII punctuation, the quotes, dashes and the signs of arithmetic.
* `Lettering.mathSigns`: `≤ ≥ ≈ ≠ ∞ √`.
-/

namespace PILean.Lettering

open Piece

/-- The ASCII punctuation, quotes, dashes and the signs of arithmetic. -/
def punctuation : Char → Option Spec
  | ' ' => some (centred 260 [])
  | '!' => some (spec [stroke [pt 0 661, pt 0 220], dot 0 39] 80 80)
  | '"' => some (spec [stroke [pt 0 661, pt 0 520], stroke [pt 150 661, pt 150 520]] 70 70)
  | '\'' => some (spec [stroke [pt 0 661, pt 0 520]] 80 80)
  | '#' => some (spec [stroke [pt 130 80, pt 200 620], stroke [pt 290 80, pt 360 620],
      stroke [pt 40 240, pt 440 240], stroke [pt 40 460, pt 440 460]] 40 40)
  | '$' => some (spec [stroke [arc 160 475 125 115 30 270, arc 160 235 135 125 90 (-150)],
      stroke [pt 160 661, pt 160 39]] 60 60)
  | '%' => some (spec [ring 85 575 85 85, ring 355 125 85 85, stroke [pt 40 39, pt 400 661]] 40 40)
  | '&' => some (spec [ring 190 525 100 136, stroke [pt 450 39, pt 190 389],
      stroke [arc 215 215 200 176 115 340]] 40 40)
  | '(' => some (spec [stroke [arc 250 270 250 470 125 235]] 60 60)
  | ')' => some (spec [stroke [arc 0 270 250 470 55 (-55)]] 60 60)
  | '*' => some (spec [stroke [pt 0 630, pt 0 370], stroke [pt 113 565, pt (-113) 435],
      stroke [pt (-113) 565, pt 113 435]] 50 50)
  | '+' => some (spec [stroke [pt 0 330, pt 380 330], stroke [pt 190 140, pt 190 520]] 60 60)
  | ',' => some (spec [stroke [pt 40 60, pt (-10) (-120)]] 60 60)
  | '-' => some (spec [stroke [pt 0 290, pt 220 290]] 60 60)
  | '.' => some (spec [dot 0 39] 80 80)
  | '/' => some (spec [stroke [pt 0 0, pt 300 700]] 20 20)
  | ':' => some (spec [dot 0 39, dot 0 471] 80 80)
  | ';' => some (spec [stroke [pt 40 60, pt (-10) (-120)], dot 40 471] 60 60)
  | '<' => some (spec [stroke [pt 330 520, pt 0 330, pt 330 140]] 60 60)
  | '=' => some (spec [stroke [pt 0 250, pt 380 250], stroke [pt 0 410, pt 380 410]] 60 60)
  | '>' => some (spec [stroke [pt 0 520, pt 330 330, pt 0 140]] 60 60)
  | '?' => some (spec [stroke [arc 185 490 175 181 165 (-90), pt 185 215], dot 185 39] 50 50)
  | '@' => some (spec [ring 310 280 110 125,
      stroke [pt 420 405, pt 420 190, arc 510 190 90 100 180 360,
        arc 320 270 290 330 (-15) 260]] 40 40)
  | '[' => some (spec [stroke [pt 120 700, pt 0 700, pt 0 (-160), pt 120 (-160)]] 70 50)
  | '\\' => some (spec [stroke [pt 0 700, pt 300 0]] 20 20)
  | ']' => some (spec [stroke [pt 0 700, pt 120 700, pt 120 (-160), pt 0 (-160)]] 50 70)
  | '^' => some (spec [stroke [pt 0 440, pt 170 661, pt 340 440]] 50 50)
  | '_' => some (spec [stroke [pt 0 (-80), pt 560 (-80)]] 20 20)
  | '`' => some (spec [stroke [pt 0 661, pt 120 540]] 50 50)
  | '{' => some (spec [stroke [arc 200 600 100 100 90 180, pt 100 420, arc 0 420 100 100 0 (-90),
      arc 0 220 100 100 90 0, pt 100 40, arc 200 40 100 100 180 270]] 60 50)
  | '|' => some (spec [stroke [pt 0 (-100), pt 0 700]] 80 80)
  | '}' => some (spec [stroke [arc 0 600 100 100 90 0, pt 100 420, arc 200 420 100 100 180 270,
      arc 200 220 100 100 90 180, pt 100 40, arc 0 40 100 100 0 (-90)]] 50 60)
  | '~' => some (spec [stroke [arc 95 340 95 60 180 0, arc 285 340 95 60 180 360]] 60 60)
  | '−' => some (spec [stroke [pt 0 330, pt 380 330]] 60 60)
  | '–' => some (spec [stroke [pt 0 290, pt 460 290]] 50 50)
  | '—' => some (spec [stroke [pt 0 290, pt 900 290]] 50 50)
  | '’' => some (spec [stroke [pt 50 665, pt 10 505]] 70 70)
  | '‘' => some (spec [stroke [pt 0 665, pt 40 505]] 70 70)
  | '“' => some (spec [stroke [pt 0 665, pt 40 505], stroke [pt 150 665, pt 190 505]] 70 70)
  | '”' => some (spec [stroke [pt 50 665, pt 10 505], stroke [pt 200 665, pt 160 505]] 70 70)
  | '…' => some (spec [dot 0 39, dot 238 39, dot 476 39] 80 80)
  | '·' => some (spec [dot 0 300] 80 80)
  | '×' => some (spec [stroke [pt 0 180, pt 300 480], stroke [pt 0 480, pt 300 180]] 60 60)
  | '÷' => some (spec [stroke [pt 0 330, pt 380 330], dot 190 500, dot 190 160] 60 60)
  | '±' => some (spec [stroke [pt 0 400, pt 380 400], stroke [pt 190 230, pt 190 570],
      stroke [pt 0 150, pt 380 150]] 60 60)
  | '°' => some (spec [ring 0 560 90 90] 60 60)
  | _ => none

/-- The mathematical signs `≤ ≥ ≈ ≠ ∞ √`. -/
def mathSigns : Char → Option Spec
  | '≤' => some (spec [stroke [pt 340 600, pt 0 470, pt 340 340],
      stroke [pt 0 190, pt 340 190]] 60 60)
  | '≥' => some (spec [stroke [pt 0 600, pt 340 470, pt 0 340],
      stroke [pt 0 190, pt 340 190]] 60 60)
  | '≈' => some (spec [stroke [arc 95 490 95 55 180 0, arc 285 490 95 55 180 360],
      stroke [arc 95 210 95 55 180 0, arc 285 210 95 55 180 360]] 60 60)
  | '≠' => some (spec [stroke [pt 0 250, pt 380 250], stroke [pt 0 410, pt 380 410],
      stroke [pt 290 570, pt 90 90]] 60 60)
  | '∞' => some (spec [loop [arc 170 330 170 150 50 310, pt 381 445,
      arc 490 330 170 150 130 (-130), pt 279 445]] 50 50)
  | '√' => some (spec [stroke [pt 0 330, pt 80 390, pt 215 (-20), pt 390 760, pt 660 760]] 50 30)
  | _ => none

end PILean.Lettering
