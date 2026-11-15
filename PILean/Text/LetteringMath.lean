/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Text.LetteringCompose
import PILean.Text.LetteringSymbols
import PILean.Text.LetteringGreek

/-!
# Lettering glyph data: mathematical operators, relations and brackets

The designs of the mathematical signs of the built-in single-stroke typeface that plot labels
use beyond the basic ones: floor and ceiling brackets, angle brackets, big operators, set and
logic signs, relations, blackboard-bold letters and primes (the glyph shapes are the authors' own
design). Signs that stand beside letters are centred about `y = 330`.

## Main definitions

* `Lettering.operators`: brackets, big operators, set and logic signs, relations and the small
  operator dots and rings.
* `Lettering.doubleStruck`: `ℕ ℤ ℚ ℝ ℂ` and `ℓ`.
-/

namespace PILean.Lettering

open Piece

/-- The element sign `∈`, opening to the right. -/
def elementSign : Spec :=
  spec [stroke [pt 340 600, pt 130 600, arc 130 330 130 270 90 270, pt 340 60],
    stroke [pt 0 330, pt 340 330]] 60 60

/-- The subset sign `⊂`, opening to the right. -/
def subsetSign : Spec :=
  spec [stroke [pt 340 600, pt 130 600, arc 130 330 130 270 90 270, pt 340 60]] 60 60

/-- The brackets, big operators, set and logic signs and relations. -/
def operators : Char → Option Spec
  | '⌊' => some (spec [stroke [pt 0 700, pt 0 (-160), pt 120 (-160)]] 70 50)
  | '⌋' => some (spec [stroke [pt 120 700, pt 120 (-160), pt 0 (-160)]] 50 70)
  | '⌈' => some (spec [stroke [pt 0 (-160), pt 0 700, pt 120 700]] 70 50)
  | '⌉' => some (spec [stroke [pt 0 700, pt 120 700, pt 120 (-160)]] 50 70)
  | '⟨' => some (spec [stroke [pt 150 700, pt 0 270, pt 150 (-160)]] 60 50)
  | '⟩' => some (spec [stroke [pt 0 700, pt 150 270, pt 0 (-160)]] 50 60)
  | '∑' => some (spec [stroke [pt 400 700, pt 0 700, pt 220 300, pt 0 (-100), pt 400 (-100)]] 50 40)
  | '∏' => some (spec [stroke [pt (-40) 700, pt 460 700], stroke [pt 0 700, pt 0 (-100)],
      stroke [pt 420 700, pt 420 (-100)]] 50 50)
  | '∫' => some (spec [stroke [arc 330 610 90 90 0 150, pt 110 (-80), arc 20 (-80) 90 90 0 (-150)]]
      60 50)
  | '∂' => some (spec [ring 205 250 195 216, stroke [pt 400 250, pt 400 480,
      arc 300 480 100 180 0 120]] 45 45)
  | '∇' => some (spec [loop [pt 0 661, pt 240 39, pt 480 661]] 25 25)
  | '∈' => some elementSign
  | '∉' => some (elementSign.withStrokes [stroke [pt 40 40, pt 300 620]])
  | '∋' => some (elementSign.mirrored 340)
  | '⊂' => some subsetSign
  | '⊃' => some (subsetSign.mirrored 340)
  | '⊆' => some (subsetSign.withStrokes [stroke [pt 0 (-90), pt 340 (-90)]])
  | '⊇' => some ((subsetSign.withStrokes [stroke [pt 0 (-90), pt 340 (-90)]]).mirrored 340)
  | '∪' => some (spec [stroke [pt 0 600, pt 0 290, arc 190 290 190 250 180 360, pt 380 600]] 60 60)
  | '∩' => some (spec [stroke [pt 0 60, pt 0 370, arc 190 370 190 250 180 0, pt 380 60]] 60 60)
  | '∧' => some (spec [stroke [pt 0 100, pt 190 600, pt 380 100]] 60 60)
  | '∨' => some (spec [stroke [pt 0 600, pt 190 100, pt 380 600]] 60 60)
  | '¬' => some (spec [stroke [pt 0 400, pt 380 400, pt 380 190]] 60 60)
  | '∀' => some (spec [stroke [pt 0 661, pt 240 39, pt 480 661],
      stroke [pt 80 485, pt 400 485]] 25 25)
  | '∃' => some (spec [stroke [pt 0 661, pt 330 661, pt 330 39, pt 0 39],
      stroke [pt 330 350, pt 40 350]] 70 40)
  | '∅' => some (spec [ring 240 330 240 270, stroke [pt 60 70, pt 420 590]] 50 50)
  | '≡' => some (spec [stroke [pt 0 180, pt 380 180], stroke [pt 0 330, pt 380 330],
      stroke [pt 0 480, pt 380 480]] 60 60)
  | '≅' => some (spec [stroke [arc 95 560 95 50 180 0, arc 285 560 95 50 180 360],
      stroke [pt 0 340, pt 380 340], stroke [pt 0 170, pt 380 170]] 60 60)
  | '∼' => some (spec [stroke [arc 95 330 95 60 180 0, arc 285 330 95 60 180 360]] 60 60)
  | '≃' => some (spec [stroke [arc 95 470 95 55 180 0, arc 285 470 95 55 180 360],
      stroke [pt 0 200, pt 380 200]] 60 60)
  | '≪' => some (spec [stroke [pt 190 500, pt 0 330, pt 190 160],
      stroke [pt 380 500, pt 190 330, pt 380 160]] 60 60)
  | '≫' => some (spec [stroke [pt 0 500, pt 190 330, pt 0 160],
      stroke [pt 190 500, pt 380 330, pt 190 160]] 60 60)
  | '∝' => (greek 'α').map (·.shifted 0 75 |>.mirrored 445)
  | '∘' => some (spec [ring 0 330 100 100] 60 60)
  | '◦' => some (spec [ring 0 330 60 60] 60 60)
  | '⋅' => some (spec [dot 0 330] 80 80)
  | '∙' => some (spec [ring 0 330 26 26] 80 80)
  | '∓' => some (spec [stroke [pt 0 260, pt 380 260], stroke [pt 190 90, pt 190 430],
      stroke [pt 0 510, pt 380 510]] 60 60)
  | '⊕' => some (spec [ring 200 330 200 200, stroke [pt 0 330, pt 400 330],
      stroke [pt 200 130, pt 200 530]] 50 50)
  | '⊗' => some (spec [ring 200 330 200 200, stroke [pt 59 189, pt 341 471],
      stroke [pt 59 471, pt 341 189]] 50 50)
  | '⊥' => some (spec [stroke [pt 0 39, pt 420 39], stroke [pt 210 39, pt 210 580]] 50 50)
  | '∥' => some (spec [stroke [pt 0 700, pt 0 (-100)], stroke [pt 150 700, pt 150 (-100)]] 80 80)
  | '∠' => some (spec [stroke [pt 380 530, pt 0 39, pt 440 39]] 50 50)
  | '△' => some (spec [loop [pt 0 90, pt 230 600, pt 460 90]] 50 50)
  | '□' => some (spec [loop [pt 0 90, pt 0 570, pt 450 570, pt 450 90]] 50 50)
  | '∗' => some (spec [stroke [pt 0 460, pt 0 200], stroke [pt 113 395, pt (-113) 265],
      stroke [pt (-113) 395, pt 113 265]] 50 50)
  | '′' => some (spec [stroke [pt 40 661, pt 0 470]] 70 70)
  | '″' => some (spec [stroke [pt 40 661, pt 0 470], stroke [pt 170 661, pt 130 470]] 70 70)
  | '‰' => some (spec [ring 85 575 85 85, ring 345 125 85 85, ring 605 125 85 85,
      stroke [pt 40 39, pt 390 661]] 40 40)
  | _ => none

/-- The blackboard-bold letters `ℕ ℤ ℚ ℝ ℂ` and the script `ℓ`. -/
def doubleStruck : Char → Option Spec
  | 'ℕ' => (capitals 'N').map (·.withStrokes [stroke [pt (-105) 39, pt (-105) 661]])
  | 'ℤ' => (capitals 'Z').map (·.withStrokes [stroke [pt 0 272, pt 150 506]])
  | 'ℚ' => (capitals 'Q').map (·.withStrokes [stroke [arc 305 350 160 190 110 250]])
  | 'ℝ' => (capitals 'R').map (·.withStrokes [stroke [pt (-105) 39, pt (-105) 661]])
  | 'ℂ' => (capitals 'C').map (·.withStrokes [stroke [arc 305 350 170 190 110 250]])
  | 'ℓ' => some (spec [stroke [pt 280 150, arc 150 150 130 111 0 (-180), pt 130 640,
      arc 200 640 70 61 180 0]] 40 40)
  | _ => none

end PILean.Lettering
