/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Text.LetteringCompose
import PILean.Text.LetteringGreek
import PILean.Text.LetteringSymbols

/-!
# Lettering glyph data: superscripts, subscripts and composed signs

The superscript and subscript digits, signs and letters of the built-in single-stroke typeface,
and the vulgar fractions, the ordinal indicators and the trade mark sign, all generated from the
regular designs: the strokes are scaled to `0.62` and moved, and the stroke width stays the same,
so the small forms are heavier in proportion and stay legible at small sizes.

## Main definitions

* `Lettering.superscripts`: `⁰ … ⁹ ⁺ ⁻ ⁼ ⁽ ⁾` and the raised letters; their ink lies between about
  `110` units and the cap height.
* `Lettering.subscripts`: `₀ … ₉ ₊ ₋ ₌ ₍ ₎` and the lowered letters; their ink lies around the
  baseline and below `380` units.
* `Lettering.composed`: `¹ ² ³ ¼ ½ ¾ ª º ™`.
-/

namespace PILean.Lettering

open Piece

/-- The scale of the script forms. -/
def scriptScale : Float := 0.62

/-- The upward shift of the centre lines of the superscripts. -/
def superShift : Float := 250

/-- The shift (downward, so negative) of the centre lines of the subscripts. -/
def subShift : Float := -100

/-- The design of a character that the scripts are drawn from: a digit, a sign, a Latin or a
Greek letter. -/
def scriptBase (c : Char) : Option Spec :=
  (digits c).orElse fun _ => (lowercase c).orElse fun _ => (punctuation c).orElse fun _ =>
    (mathSigns c).orElse fun _ => greek c

/-- The character a superscript is drawn from. -/
def superBase : Char → Option Char
  | '⁰' => some '0' | '¹' => some '1' | '²' => some '2' | '³' => some '3' | '⁴' => some '4'
  | '⁵' => some '5' | '⁶' => some '6' | '⁷' => some '7' | '⁸' => some '8' | '⁹' => some '9'
  | '⁺' => some '+' | '⁻' => some '−' | '⁼' => some '=' | '⁽' => some '(' | '⁾' => some ')'
  | 'ᵃ' => some 'a' | 'ᵇ' => some 'b' | 'ᶜ' => some 'c' | 'ᵈ' => some 'd' | 'ᵉ' => some 'e'
  | 'ᶠ' => some 'f' | 'ᵍ' => some 'g' | 'ʰ' => some 'h' | 'ⁱ' => some 'i' | 'ʲ' => some 'j'
  | 'ᵏ' => some 'k' | 'ˡ' => some 'l' | 'ᵐ' => some 'm' | 'ⁿ' => some 'n' | 'ᵒ' => some 'o'
  | 'ᵖ' => some 'p' | 'ʳ' => some 'r' | 'ˢ' => some 's' | 'ᵗ' => some 't' | 'ᵘ' => some 'u'
  | 'ᵛ' => some 'v' | 'ʷ' => some 'w' | 'ˣ' => some 'x' | 'ʸ' => some 'y' | 'ᶻ' => some 'z'
  | 'ᵅ' => some 'α' | 'ᵝ' => some 'β' | 'ᵞ' => some 'γ' | 'ᵟ' => some 'δ' | 'ᵋ' => some 'ε'
  | 'ᶿ' => some 'θ' | 'ᵠ' => some 'φ' | 'ᵡ' => some 'χ'
  | _ => none

/-- The character a subscript is drawn from. -/
def subBase : Char → Option Char
  | '₀' => some '0' | '₁' => some '1' | '₂' => some '2' | '₃' => some '3' | '₄' => some '4'
  | '₅' => some '5' | '₆' => some '6' | '₇' => some '7' | '₈' => some '8' | '₉' => some '9'
  | '₊' => some '+' | '₋' => some '−' | '₌' => some '=' | '₍' => some '(' | '₎' => some ')'
  | 'ₐ' => some 'a' | 'ₑ' => some 'e' | 'ₒ' => some 'o' | 'ₓ' => some 'x' | 'ₕ' => some 'h'
  | 'ₖ' => some 'k' | 'ₗ' => some 'l' | 'ₘ' => some 'm' | 'ₙ' => some 'n' | 'ₚ' => some 'p'
  | 'ₛ' => some 's' | 'ₜ' => some 't' | 'ᵢ' => some 'i' | 'ⱼ' => some 'j' | 'ᵣ' => some 'r'
  | 'ᵤ' => some 'u' | 'ᵥ' => some 'v' | 'ᵦ' => some 'β' | 'ᵧ' => some 'γ' | 'ᵨ' => some 'ρ'
  | 'ᵩ' => some 'φ' | 'ᵪ' => some 'χ'
  | _ => none

/-- The superscript digits, signs and letters. -/
def superscripts (c : Char) : Option Spec :=
  ((superBase c).bind scriptBase).map (·.scaled scriptScale 0 superShift)

/-- The subscript digits, signs and letters. -/
def subscripts (c : Char) : Option Spec :=
  ((subBase c).bind scriptBase).map (·.scaled scriptScale 0 subShift)

/-- The vulgar fraction with the numerator `n` and the denominator `d` (digits): a raised and a
lowered digit on either side of a fraction slash. -/
def fraction (n d : Char) : Option Spec := do
  let a ← (digits n).map (·.scaled scriptScale 0 superShift)
  let b ← (digits d).map (·.scaled scriptScale 360 subShift)
  return spec (a.strokes ++ [stroke [pt 265 (-30), pt 425 730]] ++ b.strokes) 60 60

/-- `¹ ² ³ ¼ ½ ¾ ª º ™`: the signs composed of script forms. -/
def composed : Char → Option Spec
  | '¹' => superscripts '¹'
  | '²' => superscripts '²'
  | '³' => superscripts '³'
  | '¼' => fraction '1' '4'
  | '½' => fraction '1' '2'
  | '¾' => fraction '3' '4'
  | 'ª' => (superscripts 'ᵃ').map (·.withStrokes [stroke [pt 20 150, pt 225 150]])
  | 'º' => (superscripts 'ᵒ').map (·.withStrokes [stroke [pt 0 150, pt 267 150]])
  | '™' =>
    (capitals 'T').bind fun t => (capitals 'M').map fun m =>
      spec ((t.scaled scriptScale 0 superShift).strokes ++
        (m.scaled scriptScale 390 superShift).strokes) 40 40
  | _ => none

end PILean.Lettering
