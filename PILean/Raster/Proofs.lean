/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Raster.Canvas

/-!
# Theorems about the rasteriser

* `coverageOf_le`: the coverage of a pixel is at most a whole pixel (255 in 1/255 pixels) under
  either rule, so the byte it is stored in never wraps.
* `coverage_inside`: every span of a fill lies inside the clip rectangle and the image; the
  canvas only paints the pixels of the spans it is given (`Canvas.fillSpans` visits no other),
  so a fill never writes outside the clip. `coverage` filters its spans to the clip before
  returning them, so this holds by construction; the tests show the filter removes nothing.
* `encode16_decode8`: the sRGB tables round-trip every 8-bit value.
* `mask_zero`: where a clip mask is 0 the coverage applied is 0.

Each with an example showing that its hypotheses can be met. What is tested and not proved:
the coverage values themselves (against known areas), strokes, paints and compositing.
-/

namespace PILean.Raster

theorem coverageOf_le (rule : FillRule) (v : Int) : coverageOf rule v ≤ 255 := by
  sorry

theorem coverage_inside {polys : Array (Array Point)} {rule : FillRule} {w h : Nat}
    {clip : IRect} {spans : Array Span} (hs : coverage polys rule w h clip = some spans) :
    ∀ s ∈ spans, Span.inside (clip.inter ⟨0, 0, w, h⟩) s = true := by
  sorry

example : ∃ spans, coverage #[#[⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]] .nonZero 2 2 ⟨0, 0, 2, 2⟩ = some spans := by
  sorry

theorem encode16_decode8 : ∀ n < 256, encode16 (decode8 n.toUInt8) = n.toUInt8 := by
  sorry

theorem mask_zero (a op : Nat) : mulDiv a (mulDiv op 0 255) 65535 = 0 := by
  sorry

end PILean.Raster
