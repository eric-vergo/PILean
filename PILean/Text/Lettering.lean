/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Text.LetteringGlyphs
import PILean.Text.LetteringLower
import PILean.Text.LetteringSymbols

/-!
# Single-stroke lettering

A small built-in typeface drawn from centre lines, for tick labels, legends, axis labels and
titles of plots. A glyph is a few strokes (straight segments and elliptical arcs, the arcs as cubic
Béziers of at most 90°); the renderer strokes them with round caps and round joins. The letter
shapes are the authors' own design: a calm geometric sans in the spirit of technical lettering,
with an even stroke, generous counters, round letters close to circles, and no ornament; no
existing font's data was used.

The em is 1000 units with `y` up and the baseline at `y = 0`. Metrics (ink, in units): cap height
`700`, x-height `510`, ascender `740`, descender `-200`, stroke width `78`; round letters overshoot
the cap height, the x-height and the baseline by about `10`. The digits are tabular (advance `560`).

## Main definitions

* `Lettering.Glyph`, `Lettering.glyph`: a glyph's centre lines and advance; a character outside
  the typeface is a rectangle of advance `600`.
* `Lettering.charset`: the characters the typeface draws.
* `Lettering.measure`: the width of a string at a size.
* `Lettering.shape`: the centre lines of a string at a size, `y` down, and the stroke width.
* `Lettering.ascent`, `descent`, `capHeight`, `xHeight`: the metrics as fractions of the size.

## Implementation notes

A size that is not finite, not positive or above `maxSize` gives no shape and no width, so a
caller's arithmetic that went wrong draws nothing instead of a huge path.
-/

namespace PILean.Lettering

/-- One glyph: its strokes (centre lines in em units of 1000, `y` up, baseline at `y = 0`) and
its advance. -/
structure Glyph where
  /-- The centre lines. -/
  strokes : Path
  /-- The advance in em units. -/
  advance : Float
  deriving Inhabited

/-- The stroke width in em units at weight 1. -/
def strokeUnits : Float := 78

/-- The ascent as a fraction of the size: the ascender height. -/
def ascent : Float := 0.74

/-- The descent as a fraction of the size, positive: the descender depth. -/
def descent : Float := 0.2

/-- The cap height as a fraction of the size. -/
def capHeight : Float := 0.7

/-- The x-height as a fraction of the size. -/
def xHeight : Float := 0.51

/-- The advance of the box drawn for a character the typeface lacks. -/
def missingAdvance : Float := 600

/-- The largest size, in pixels, at which text is shaped. -/
def maxSize : Float := 1e5

/-- A design as a glyph: the strokes shifted so that the ink has the design's bearings on both
sides (or centred in the fixed advance), and the advance. -/
def Spec.toGlyph (g : Spec) : Glyph :=
  let raw := g.rawPath
  match raw.bounds with
  | none => { strokes := {}, advance := g.fixed.getD 0 }
  | some b =>
    let half := strokeUnits / 2
    let (dx, adv) := match g.fixed with
      | some a => ((a - (b.x0 + b.x1)) / 2, a)
      | none => (g.lsb + half - b.x0, (b.x1 - b.x0) + strokeUnits + g.lsb + g.rsb)
    { strokes := raw.transform (Affine.translate dx 0), advance := adv }

/-- The design of a character, if the typeface has it. -/
def spec? (c : Char) : Option Spec :=
  (capitals c).orElse fun _ => (lowercase c).orElse fun _ => (digits c).orElse fun _ =>
    (punctuation c).orElse fun _ => (mathSigns c).orElse fun _ => greek c

/-- The glyph box drawn for a character the typeface lacks: a rectangle of advance `600`. -/
def missingGlyph : Glyph :=
  { strokes := ((Path.rect 60 39 480 622)), advance := missingAdvance }

/-- The glyph of a character: its design, or the missing-glyph box. -/
def glyph (c : Char) : Glyph :=
  match spec? c with
  | some g => g.toGlyph
  | none => missingGlyph

/-- The characters the typeface draws: printable ASCII, the minus sign, dashes, quotes, the
ellipsis, the middle dot, `× ÷ ± °`, the micro sign, `≤ ≥ ≈ ≠ ∞ √` and the Greek
letters `α β γ δ ε θ λ μ π σ τ φ ω Δ Σ Ω`. -/
def charset : List Char :=
  (List.range 95).map (fun i => Char.ofNat (0x20 + i)) ++
  "−–—’‘“”…·×÷±°µ\
    ≤≥≈≠∞√\
    αβγδεθλμπστφω\
    ΔΣΩ".toList

/-- Whether a size is usable: finite, positive and at most `maxSize`. -/
def validSize (size : Float) : Bool := size > 0 && size ≤ maxSize

/-- The width of `s` at `size` pixels: the sum of the advances scaled by `size / 1000`, plus
`tracking` pixels between neighbouring characters. Zero for an unusable size. -/
def measure (s : String) (size : Float) (tracking : Float := 0) : Float :=
  if !validSize size then 0
  else
    let units := s.foldl (fun acc c => acc + (glyph c).advance) 0
    let gaps := (s.length - 1 : Nat).toFloat
    units * size / 1000 + (if tracking.isFinite then tracking * gaps else 0)

/-- The centre lines of `s` at `size` pixels, `y` down (screen coordinates) with the baseline
origin at `(0, 0)`, and the stroke width in pixels (`weight` times `78 / 1000` of the size).
`tracking` is extra space in pixels between neighbouring characters. The empty path for an
empty string or an unusable size. -/
def shape (s : String) (size : Float) (weight : Float := 1) (tracking : Float := 0) :
    Path × Float :=
  if !validSize size then ({}, 0)
  else
    let k := size / 1000
    let track := if tracking.isFinite then tracking else 0
    let (path, _) := s.foldl (init := (({} : Path), (0 : Float))) fun (acc, pen) c =>
      let g := glyph c
      let m : Affine := ⟨k, 0, 0, -k, pen, 0⟩
      (acc.append (g.strokes.transform m), pen + g.advance * k + track)
    let w := if weight.isFinite && weight > 0 then weight else 1
    (path, strokeUnits * k * w)

end PILean.Lettering
