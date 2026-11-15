/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Text.LetteringGlyphs

/-!
# Lettering glyph data: punctuation, mathematical signs and Greek

The designs of the punctuation, the mathematical signs and the Greek letters of the built-in
single-stroke typeface (the glyph shapes are the authors' own design).

## Main definitions

* `Lettering.punctuation`: the ASCII punctuation, the quotes, dashes and the signs of arithmetic.
* `Lettering.mathSigns`: `≤ ≥ ≈ ≠ ∞ √` and their kin.
* `Lettering.greek`: the Greek letters.
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
  | '…' => some (spec [dot 0 39, dot 230 39, dot 460 39] 80 80)
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
  | '√' => some (spec [stroke [pt 0 290, pt 55 330, pt 175 39, pt 350 661, pt 600 661]] 50 30)
  | _ => none

/-- The Greek letters. -/
def greek : Char → Option Spec
  | 'α' => some (spec [stroke [arc 200 255 200 226 50 360, pt 400 100, arc 460 100 60 61 180 270]]
      45 40)
  | 'β' => some (spec [stroke [pt 0 (-161), pt 0 541, arc 170 541 170 160 180 (-90)],
      stroke [arc 190 205 190 176 90 (-180)]] 70 45)
  | 'γ' => some (spec [stroke [pt 0 471, pt 0 300, arc 210 300 210 171 180 270, pt 210 (-161)],
      stroke [pt 420 471, pt 210 129]] 30 30)
  | 'δ' => some (spec [ring 200 225 200 196, stroke [pt 200 421, pt 200 540,
      arc 300 540 100 131 180 60]] 45 45)
  | 'ε' => some (spec [stroke [arc 226 255 200 226 40 320], stroke [pt 60 255, pt 230 255]]
      45 40)
  | 'θ' => some (spec [ring 175 350 175 321, stroke [pt 70 350, pt 280 350]] 45 45)
  | 'λ' => some (spec [stroke [pt 10 701, pt 410 39], stroke [pt 210 370, pt 0 39]] 20 20)
  | 'μ' | 'µ' => some (spec [stroke [pt 0 471, pt 0 (-161)],
      stroke [pt 0 471, pt 0 240, arc 205 240 205 211 180 360], stroke [pt 410 471, pt 410 39]])
  | 'π' => some (spec [stroke [pt 0 471, pt 490 471], stroke [pt 130 471, pt 130 39],
      stroke [pt 350 471, pt 350 120, arc 420 120 70 81 180 270]] 40 40)
  | 'σ' => some (spec [ring 200 255 200 226, stroke [pt 200 475, pt 450 475]] 45 30)
  | 'τ' => some (spec [stroke [pt 0 471, pt 370 471],
      stroke [pt 185 471, pt 185 130, arc 280 130 95 91 180 270]] 30 30)
  | 'φ' => some (spec [ring 215 255 215 226, stroke [pt 215 611, pt 215 (-161)]] 45 45)
  | 'ω' => some (spec [stroke [pt 0 471, pt 0 255, arc 150 255 150 226 180 360, pt 300 340,
      arc 450 255 150 226 180 360, pt 600 471]] 45 45)
  | 'Δ' => some (spec [loop [pt 0 39, pt 240 661, pt 480 39]] 25 25)
  | 'Σ' => some (spec [stroke [pt 380 661, pt 0 661, pt 230 350, pt 0 39, pt 400 39]] 40 30)
  | 'Ω' => some (spec [stroke [pt 0 39, pt 150 39, pt 115 140, arc 240 380 240 281 239 (-59),
      pt 330 39, pt 480 39]] 40 40)
  | _ => none

end PILean.Lettering
