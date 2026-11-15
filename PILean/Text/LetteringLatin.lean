/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Text.LetteringCompose
import PILean.Text.LetteringLower

/-!
# Lettering glyph data: the Latin-1 letters

The accented letters and the other letters of the Latin-1 block `À`–`ÿ` of the built-in
single-stroke typeface (the glyph shapes are the authors' own design). An accented letter is the
base letter with a mark (`Lettering.Mark`) placed above the x-height or the cap height; `ı` stands
in for `i` under a mark.

## Main definitions

* `Lettering.latin`: the designs of `À`–`ÿ` except `×` and `÷`, and of `Œ œ ı`.
-/

namespace PILean.Lettering

open Piece

/-- The design of a plain Latin letter, with the dotless `ı` for `i` (the base of marks). -/
def markBase (c : Char) : Option Spec :=
  if c == 'i' then some (spec [stroke [pt 0 39, pt 0 471]] 80 80)
  else (capitals c).orElse fun _ => lowercase c

/-- The base letter and the mark of an accented Latin-1 letter. -/
def accentedParts : Char → Option (Char × Mark)
  | 'À' => some ('A', .grave) | 'Á' => some ('A', .acute) | 'Â' => some ('A', .circumflex)
  | 'Ã' => some ('A', .tilde) | 'Ä' => some ('A', .diaeresis) | 'Å' => some ('A', .ringAbove)
  | 'Ç' => some ('C', .cedilla)
  | 'È' => some ('E', .grave) | 'É' => some ('E', .acute) | 'Ê' => some ('E', .circumflex)
  | 'Ë' => some ('E', .diaeresis)
  | 'Ì' => some ('I', .grave) | 'Í' => some ('I', .acute) | 'Î' => some ('I', .circumflex)
  | 'Ï' => some ('I', .diaeresis) | 'Ñ' => some ('N', .tilde)
  | 'Ò' => some ('O', .grave) | 'Ó' => some ('O', .acute) | 'Ô' => some ('O', .circumflex)
  | 'Õ' => some ('O', .tilde) | 'Ö' => some ('O', .diaeresis)
  | 'Ù' => some ('U', .grave) | 'Ú' => some ('U', .acute) | 'Û' => some ('U', .circumflex)
  | 'Ü' => some ('U', .diaeresis) | 'Ý' => some ('Y', .acute)
  | 'à' => some ('a', .grave) | 'á' => some ('a', .acute) | 'â' => some ('a', .circumflex)
  | 'ã' => some ('a', .tilde) | 'ä' => some ('a', .diaeresis) | 'å' => some ('a', .ringAbove)
  | 'ç' => some ('c', .cedilla)
  | 'è' => some ('e', .grave) | 'é' => some ('e', .acute) | 'ê' => some ('e', .circumflex)
  | 'ë' => some ('e', .diaeresis)
  | 'ì' => some ('i', .grave) | 'í' => some ('i', .acute) | 'î' => some ('i', .circumflex)
  | 'ï' => some ('i', .diaeresis) | 'ñ' => some ('n', .tilde)
  | 'ò' => some ('o', .grave) | 'ó' => some ('o', .acute) | 'ô' => some ('o', .circumflex)
  | 'õ' => some ('o', .tilde) | 'ö' => some ('o', .diaeresis)
  | 'ù' => some ('u', .grave) | 'ú' => some ('u', .acute) | 'û' => some ('u', .circumflex)
  | 'ü' => some ('u', .diaeresis) | 'ý' => some ('y', .acute) | 'ÿ' => some ('y', .diaeresis)
  | _ => none

/-- The base design with the mark above it, centred on the letter's centre lines (the cedilla on
the centre of the round letters `C` and `c`). -/
def withMark (base : Char) (m : Mark) : Option Spec :=
  (markBase base).map fun g =>
    let cx := match base, m with
      | 'C', .cedilla => 305
      | 'c', .cedilla => 226
      | _, _ => g.centreX
    g.withStrokes (m.strokes cx base.isUpper)

/-- The designs of the Latin-1 letters `À`–`ÿ` (except `×` and `÷`), of `Œ œ`, and of `ı`. -/
def latin : Char → Option Spec
  | 'Æ' => some (spec [stroke [pt 0 39, pt 330 661, pt 330 39, pt 700 39],
      stroke [pt 330 661, pt 700 661], stroke [pt 138 300, pt 640 300]] 25 40)
  | 'æ' => some (spec [stroke [arc 150 331 140 150 180 0, pt 290 39],
      stroke [pt 290 255, pt 150 255, arc 150 149 150 106 90 360],
      stroke [pt 290 255, pt 726 255, arc 508 255 218 226 0 320]] 45 40)
  | 'Œ' => some (spec [ring 260 350 260 321, stroke [pt 880 661, pt 520 661, pt 520 39, pt 880 39],
      stroke [pt 520 350, pt 820 350]] 45 40)
  | 'œ' => some (spec [ring 200 255 200 226,
      stroke [pt 400 255, pt 836 255, arc 618 255 218 226 0 320]] 45 40)
  | 'ß' => some (spec [stroke [pt 0 39, pt 0 520, arc 170 520 170 181 180 (-60),
      arc 220 200 180 163 90 (-150)]] 70 45)
  | 'Ð' => some (spec [loop [pt 0 39, pt 0 661, pt 245 661, arc 245 350 300 311 90 (-90)],
      stroke [pt (-90) 350, pt 200 350]] 70 45)
  | 'ð' => some (spec [ring 200 255 200 226, stroke [pt 400 255, pt 400 650,
      arc 310 650 90 51 0 90], stroke [pt 250 580, pt 520 580]] 45 45)
  | 'Þ' => some (spec [stroke [pt 0 39, pt 0 661], stroke [pt 0 540, pt 190 540,
      arc 190 380 160 160 90 (-90), pt 0 220]] 70 45)
  | 'þ' => some (spec [stroke [pt 0 701, pt 0 (-161)], ring 215 255 215 226] 70 45)
  | 'Ø' => some (spec [ring 305 350 305 321, stroke [pt 40 20, pt 570 680]] 45 45)
  | 'ø' => some (spec [ring 215 255 215 226, stroke [pt 50 40, pt 380 470]] 45 45)
  | 'ı' => markBase 'i'
  | c => (accentedParts c).bind fun (b, m) => withMark b m

end PILean.Lettering
