/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Text.LetteringGlyphs

/-!
# Lettering glyph data: lowercase letters and digits

The designs of the lowercase Latin letters and the ten digits of the built-in single-stroke
typeface (the glyph shapes are the authors' own design). The digits are centred in one advance of
`560` units so that columns of numbers align.

## Main definitions

* `Lettering.lowercase`: the designs of `a` to `z`.
* `Lettering.digits`: the designs of `0` to `9`.
-/

namespace PILean.Lettering

open Piece

/-- The lowercase Latin letters. -/
def lowercase : Char → Option Spec
  | 'a' => some (spec [stroke [arc 195 331 165 150 180 0, pt 360 39],
      stroke [pt 360 291, pt 175 291, arc 175 160 185 131 90 360]] 45 70)
  | 'b' => some (spec [stroke [pt 0 701, pt 0 39], ring 215 255 215 226] 70 45)
  | 'c' => some (spec [stroke [arc 226 255 216 226 40 320]] 45 40)
  | 'd' => some (spec [stroke [pt 430 701, pt 430 39], ring 215 255 215 226] 45 70)
  | 'e' => some (spec [stroke [pt 0 255, arc 218 255 218 226 0 320]] 45 40)
  | 'f' => some (spec [stroke [pt 130 39, pt 130 560, arc 270 560 140 141 180 90],
      stroke [pt 0 471, pt 270 471]] 40 20)
  | 'g' => some (spec [stroke [pt 430 471, pt 430 (-30), arc 215 (-30) 215 131 0 (-155)],
      ring 215 255 215 226] 45 70)
  | 'h' => some (spec [stroke [pt 0 39, pt 0 701], stroke [arc 205 270 205 211 180 0, pt 410 39]])
  | 'i' => some (spec [stroke [pt 0 39, pt 0 471], dot 0 640] 80 80)
  | 'j' => some (spec [stroke [pt 130 471, pt 130 (-40), arc 10 (-40) 120 121 0 (-105)],
      dot 130 640] 20 80)
  | 'k' => some (spec [stroke [pt 0 39, pt 0 701], stroke [pt 330 471, pt 0 190],
      stroke [pt 105 280, pt 350 39]] 70 25)
  | 'l' => some (spec [stroke [pt 0 39, pt 0 701]] 80 80)
  | 'm' => some (spec [stroke [pt 0 39, pt 0 471], stroke [arc 170 270 170 211 180 0, pt 340 39],
      stroke [pt 340 270, arc 510 270 170 211 180 0, pt 680 39]])
  | 'n' => some (spec [stroke [pt 0 39, pt 0 471], stroke [arc 205 270 205 211 180 0, pt 410 39]])
  | 'o' => some (spec [ring 215 255 215 226] 45 45)
  | 'p' => some (spec [stroke [pt 0 471, pt 0 (-161)], ring 215 255 215 226] 70 45)
  | 'q' => some (spec [stroke [pt 430 471, pt 430 (-161)], ring 215 255 215 226] 45 70)
  | 'r' => some (spec [stroke [pt 0 39, pt 0 471], stroke [arc 200 270 200 211 180 60]] 70 20)
  | 's' => some (spec [stroke [arc 185 372 145 109 30 270, arc 185 146 155 117 90 (-150)]] 45 45)
  | 't' => some (spec [stroke [pt 120 640, pt 120 130, arc 240 130 120 91 180 300],
      stroke [pt 0 471, pt 260 471]] 25 25)
  | 'u' => some (spec [stroke [pt 0 471, arc 205 240 205 211 180 360],
      stroke [pt 410 471, pt 410 39]])
  | 'v' => some (spec [stroke [pt 0 471, pt 230 39, pt 460 471]] 25 25)
  | 'w' => some (spec [stroke [pt 0 471, pt 165 39, pt 330 471, pt 495 39, pt 660 471]] 25 25)
  | 'x' => some (spec [stroke [pt 0 471, pt 400 39], stroke [pt 400 471, pt 0 39]] 30 30)
  | 'y' => some (spec [stroke [pt 0 471, pt 215 39], stroke [pt 430 471, pt 115 (-161)]] 25 25)
  | 'z' => some (spec [stroke [pt 0 471, pt 360 471, pt 0 39, pt 360 39]] 45 45)
  | _ => none

/-- The digits, centred in an advance of `560`. -/
def digits : Char → Option Spec
  | '0' => some (centred 560 [ring 190 350 190 321])
  | '1' => some (centred 560 [stroke [pt 0 500, pt 190 661, pt 190 39]])
  | '2' => some (centred 560 [stroke [arc 190 480 190 191 160 (-35), pt 0 39, pt 390 39]])
  | '3' => some (centred 560 [stroke [arc 190 510 170 161 150 (-90),
      arc 190 190 190 161 90 (-150)]])
  | '4' => some (centred 560 [stroke [pt 340 39, pt 340 661, pt 0 195, pt 430 195]])
  | '5' => some (centred 560 [stroke [pt 340 661, pt 66 661, pt 66 347,
      arc 190 215 175 186 135 (-145)]])
  | '6' => some (centred 560 [stroke [pt 0 225, pt 0 400, arc 240 400 240 271 180 55],
      ring 190 225 190 196])
  | '7' => some (centred 560 [stroke [pt 0 661, pt 380 661, pt 140 39]])
  | '8' => some (centred 560 [ring 190 515 160 156, ring 190 195 185 166])
  | '9' => some (centred 560 [stroke [pt 380 475, pt 380 300, arc 140 300 240 271 0 (-125)],
      ring 190 475 190 196])
  | _ => none

end PILean.Lettering
