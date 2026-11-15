/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Text.LetteringCompose
import PILean.Text.LetteringSymbols

/-!
# Lettering glyph data: typographic punctuation, currency and signs

The designs of the typographic punctuation, spaces, currency signs and other signs of the
Latin-1 block of the built-in single-stroke typeface (the glyph shapes are the authors' own
design).

## Main definitions

* `Lettering.typographic`: `« » ‹ › „ ‚ ¡ ¿ § ¶ † ‡ • ‣ € £ ¥ ¢ © ® ¤ ¦ ¨ ¯ ´ ¸ ‐ ‑ ‒ ― ‖ ⁄` and
  the no-break, en, em, thin and narrow no-break spaces.
-/

namespace PILean.Lettering

open Piece

/-- The upper half of `§`: an `S` curve. -/
def sectionCurve : Spec :=
  spec [stroke [arc 160 530 130 120 30 270, arc 160 300 150 120 90 (-150)]] 60 60

/-- The typographic punctuation, spaces, currency signs and other signs. -/
def typographic : Char → Option Spec
  | ' ' => some (centred 260 [])
  | ' ' => some (centred 500 [])
  | ' ' => some (centred 1000 [])
  | ' ' | ' ' => some (centred 150 [])
  | '«' => some (spec [stroke [pt 150 480, pt 0 330, pt 150 180],
      stroke [pt 310 480, pt 160 330, pt 310 180]] 60 60)
  | '»' => some (spec [stroke [pt 0 480, pt 150 330, pt 0 180],
      stroke [pt 160 480, pt 310 330, pt 160 180]] 60 60)
  | '‹' => some (spec [stroke [pt 150 480, pt 0 330, pt 150 180]] 60 60)
  | '›' => some (spec [stroke [pt 0 480, pt 150 330, pt 0 180]] 60 60)
  | '‚' => some (spec [stroke [pt 40 60, pt (-10) (-120)]] 60 60)
  | '„' => some (spec [stroke [pt 40 60, pt (-10) (-120)], stroke [pt 190 60, pt 140 (-120)]] 60 60)
  | '¡' => (punctuation '!').map (·.turned 0 700)
  | '¿' => (punctuation '?').map (·.turned 370 700)
  | '§' => some ((sectionCurve.turned 320 560).append sectionCurve)
  | '¶' => some (spec [stroke [pt 380 661, pt 380 39], stroke [pt 250 661, pt 250 39],
      stroke [pt 380 661, pt 220 661, arc 220 495 150 166 90 270, pt 250 329]] 50 50)
  | '†' => some (spec [stroke [pt 130 700, pt 130 (-100)], stroke [pt 20 520, pt 240 520]] 60 60)
  | '‡' => some (spec [stroke [pt 130 700, pt 130 (-100)], stroke [pt 20 520, pt 240 520],
      stroke [pt 20 90, pt 240 90]] 60 60)
  | '•' => some (spec [ring 0 330 36 36] 80 80)
  | '‣' => some (spec [loop [pt 0 270, pt 0 450, pt 150 360]] 80 80)
  | '€' => some (spec [stroke [arc 300 350 280 321 40 320], stroke [pt 0 440, pt 360 440],
      stroke [pt 0 260, pt 360 260]] 50 40)
  | '£' => some (spec [stroke [arc 220 500 150 161 25 180, pt 70 39, pt 380 39],
      stroke [pt 0 300, pt 250 300]] 50 40)
  | '¥' => some (spec [stroke [pt 0 661, pt 240 330, pt 480 661], stroke [pt 240 330, pt 240 39],
      stroke [pt 100 290, pt 380 290], stroke [pt 100 160, pt 380 160]] 25 25)
  | '¢' => some (spec [stroke [arc 226 255 216 226 40 320], stroke [pt 226 600, pt 226 (-30)]]
      45 40)
  | '©' => some (spec [ring 300 350 300 321, stroke [arc 300 350 140 150 40 320]] 45 45)
  | '®' => (capitals 'R').map fun r =>
      spec ([ring 300 350 300 321] ++ (r.scaled 0.5 200 175).strokes) 45 45
  | '¤' => some (spec [ring 0 350 100 100, stroke [pt 71 421, pt 120 470],
      stroke [pt (-71) 421, pt (-120) 470], stroke [pt 71 279, pt 120 230],
      stroke [pt (-71) 279, pt (-120) 230]] 70 70)
  | '¦' => some (spec [stroke [pt 0 700, pt 0 380], stroke [pt 0 220, pt 0 (-160)]] 80 80)
  | '¨' => some (spec [dot 0 625, dot 170 625] 60 60)
  | '¯' => some (spec [stroke [pt 0 640, pt 280 640]] 50 50)
  | '´' => some (spec [stroke [pt 0 540, pt 120 661]] 50 50)
  | '¸' => some (spec (Mark.cedilla.strokes 0 false) 50 50)
  | '‐' | '‑' => punctuation '-'
  | '‒' => some (spec [stroke [pt 0 290, pt 400 290]] 50 50)
  | '―' => some (spec [stroke [pt 0 290, pt 1000 290]] 50 50)
  | '‖' => some (spec [stroke [pt 0 700, pt 0 (-100)], stroke [pt 150 700, pt 150 (-100)]] 80 80)
  | '⁄' => some (spec [stroke [pt 0 100, pt 300 640]] 20 20)
  | _ => none

end PILean.Lettering
