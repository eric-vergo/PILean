/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Text.LetteringGlyphs
import PILean.Text.LetteringLower

/-!
# Lettering glyph data: Greek

The designs of the Greek alphabet of the built-in single-stroke typeface (the glyph shapes are
the authors' own design): the capitals and small letters, the final sigma and the variant forms
`ϑ ϕ ϵ ϱ ϖ`. Capitals that look like Latin capitals use the Latin design.

## Main definitions

* `Lettering.greek`: the designs of the Greek letters.
-/

namespace PILean.Lettering

open Piece

/-- The Greek letters. -/
def greek : Char → Option Spec
  | 'Α' => capitals 'A'
  | 'Β' => capitals 'B'
  | 'Γ' => some (spec [stroke [pt 0 39, pt 0 661, pt 330 661]] 70 40)
  | 'Δ' | '∆' => some (spec [loop [pt 0 39, pt 240 661, pt 480 39]] 25 25)
  | 'Ε' => capitals 'E'
  | 'Ζ' => capitals 'Z'
  | 'Η' => capitals 'H'
  | 'Θ' => some (spec [ring 305 350 305 321, stroke [pt 190 350, pt 420 350]] 45 45)
  | 'Ι' => capitals 'I'
  | 'Κ' => capitals 'K'
  | 'Λ' => some (spec [stroke [pt 0 39, pt 280 661, pt 560 39]] 25 25)
  | 'Μ' => capitals 'M'
  | 'Ν' => capitals 'N'
  | 'Ξ' => some (spec [stroke [pt 0 661, pt 420 661], stroke [pt 70 350, pt 350 350],
      stroke [pt 0 39, pt 420 39]] 50 50)
  | 'Ο' => capitals 'O'
  | 'Π' => some (spec [stroke [pt 0 39, pt 0 661, pt 440 661, pt 440 39]])
  | 'Ρ' => capitals 'P'
  | 'Σ' => some (spec [stroke [pt 380 661, pt 0 661, pt 230 350, pt 0 39, pt 400 39]] 40 30)
  | 'Τ' => capitals 'T'
  | 'Υ' => capitals 'Y'
  | 'Φ' => some (spec [ring 250 350 250 220, stroke [pt 250 661, pt 250 39]] 45 45)
  | 'Χ' => capitals 'X'
  | 'Ψ' => some (spec [stroke [pt 0 661, pt 0 340, arc 215 340 215 260 180 360, pt 430 661],
      stroke [pt 215 661, pt 215 39]])
  | 'Ω' => some (spec [stroke [pt 0 39, pt 150 39, pt 115 140, arc 240 380 240 281 239 (-59),
      pt 330 39, pt 480 39]] 40 40)
  | 'α' => some (spec [stroke [arc 190 255 190 226 40 320, pt 445 440],
      stroke [pt 335 400, pt 445 70]] 45 25)
  | 'β' => some (spec [stroke [pt 0 (-161), pt 0 541, arc 170 541 170 160 180 (-90)],
      stroke [arc 190 205 190 176 90 (-180)]] 70 45)
  | 'γ' => some (spec [stroke [pt 0 471, pt 0 300, arc 210 300 210 171 180 270, pt 210 (-161)],
      stroke [pt 420 471, pt 210 129]] 30 30)
  | 'δ' => some (spec [ring 200 225 200 196, stroke [pt 200 421, pt 200 540,
      arc 300 540 100 131 180 60]] 45 45)
  | 'ε' => some (spec [stroke [arc 226 255 200 226 40 320], stroke [pt 60 255, pt 230 255]]
      45 40)
  | 'ζ' => some (spec [stroke [pt 110 701, pt 370 701, pt 160 351,
      arc 290 210 170 220 140 270, arc 290 (-90) 110 80 90 (-40)]] 60 50)
  | 'η' => some (spec [stroke [pt 0 39, pt 0 471],
      stroke [arc 205 270 205 211 180 0, pt 410 (-161)]])
  | 'θ' => some (spec [ring 175 350 175 321, stroke [pt 70 350, pt 280 350]] 45 45)
  | 'ι' => some (spec [stroke [pt 0 471, pt 0 120, arc 90 120 90 81 180 270]] 70 40)
  | 'κ' => some (spec [stroke [pt 0 39, pt 0 471], stroke [pt 330 471, pt 0 190],
      stroke [pt 105 280, pt 350 39]] 70 25)
  | 'λ' => some (spec [stroke [pt 10 701, pt 410 39], stroke [pt 210 370, pt 0 39]] 20 20)
  | 'μ' | 'µ' => some (spec [stroke [pt 0 471, pt 0 (-161)],
      stroke [pt 0 471, pt 0 240, arc 205 240 205 211 180 360], stroke [pt 410 471, pt 410 39]])
  | 'ν' => some (spec [stroke [pt 0 471, pt 150 39, pt 400 471]] 25 25)
  | 'ξ' => some (spec [stroke [pt 330 701, pt 170 701, arc 170 586 130 115 90 270,
      arc 190 363 160 108 90 (-90), arc 190 147 150 108 90 270]] 60 50)
  | 'ο' => lowercase 'o'
  | 'π' => some (spec [stroke [pt 0 471, pt 490 471], stroke [pt 130 471, pt 130 39],
      stroke [pt 350 471, pt 350 120, arc 420 120 70 81 180 270]] 40 40)
  | 'ρ' => some (spec [stroke [pt 0 (-161), pt 0 255, arc 215 255 215 226 180 (-180)]] 70 45)
  | 'σ' => some (spec [ring 200 255 200 226, stroke [pt 200 475, pt 450 475]] 45 30)
  | 'ς' => some (spec [stroke [pt 380 471, pt 220 471, arc 220 265 190 206 90 270,
      pt 250 59, arc 250 (-20) 80 79 90 (-60)]] 45 40)
  | 'τ' => some (spec [stroke [pt 0 471, pt 370 471],
      stroke [pt 185 471, pt 185 130, arc 280 130 95 91 180 270]] 30 30)
  | 'υ' => some (spec [stroke [pt 0 471, pt 0 270, arc 200 270 200 231 180 360, pt 400 471]]
      45 45)
  | 'φ' => some (spec [ring 215 255 215 226, stroke [pt 215 611, pt 215 (-161)]] 45 45)
  | 'χ' => some (spec [stroke [pt 0 471, pt 380 (-161)], stroke [pt 380 471, pt 0 (-161)]] 30 30)
  | 'ψ' => some (spec [stroke [pt 0 471, pt 0 255, arc 205 255 205 226 180 360, pt 410 471],
      stroke [pt 205 701, pt 205 (-161)]] 45 45)
  | 'ω' => some (spec [stroke [pt 0 471, pt 0 255, arc 150 255 150 226 180 360, pt 300 340,
      arc 450 255 150 226 180 360, pt 600 471]] 45 45)
  | 'ϑ' => some (spec [ring 175 290 175 251, stroke [pt 65 290, pt 285 290],
      stroke [pt 255 515, pt 330 640, pt 420 665]] 45 45)
  | 'ϕ' => some (spec [ring 190 255 190 226, stroke [pt 190 701, pt 190 (-161)]] 45 45)
  | 'ϵ' => some (spec [stroke [arc 205 365 145 106 40 270, arc 205 150 165 114 90 320]] 40 45)
  | 'ϱ' => some (spec [ring 215 290 215 191, stroke [pt 0 290, pt 0 (-70),
      arc 90 (-70) 90 81 180 270]] 70 45)
  | 'ϖ' => some (spec [stroke [pt 0 471, pt 0 255, arc 150 255 150 226 180 360, pt 300 340,
      arc 450 255 150 226 180 360, pt 600 471], stroke [pt (-20) 471, pt 620 471]] 45 45)
  | _ => none

end PILean.Lettering
