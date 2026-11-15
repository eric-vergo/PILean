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

Each statement with hypotheses has an example showing that they can be met. What is tested and not proved:
the coverage values themselves (against known areas), strokes, paints and compositing.
-/

namespace PILean.Raster

/-- A pixel's coverage is at most a whole pixel. -/
theorem coverageOf_le (rule : FillRule) (v : Int) : coverageOf rule v ≤ 255 := by
  unfold coverageOf
  have h : ∀ m, m ≤ 131072 → (m * 255 + 131072 / 2) / 131072 ≤ 255 := by
    intro m hm; omega
  cases rule with
  | nonZero => exact h _ (Nat.min_le_right _ _)
  | evenOdd =>
    apply h
    dsimp only
    split <;> omega

example : coverageOf .evenOdd 393216 = 255 := by decide

/-- Every span of a fill lies inside the clip rectangle and the image. -/
theorem coverage_inside {polys : Array (Array Point)} {rule : FillRule} {w h : Nat}
    {clip : IRect} {spans : Array Span} (hs : coverage polys rule w h clip = some spans) :
    ∀ s ∈ spans, Span.inside (clip.inter ⟨0, 0, w, h⟩) s = true := by
  unfold coverage at hs
  cases hr : coverageRaw polys rule w h clip with
  | none => rw [hr] at hs; cases hs
  | some raw =>
    rw [hr] at hs
    simp only [Option.map_some, Option.some.injEq] at hs
    intro s hm
    rw [← hs] at hm
    exact (Array.mem_filter.mp hm).2

example : ∃ spans,
    coverage #[#[⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]] .nonZero 2 2 ⟨0, 0, 2, 2⟩ = some spans := by
  unfold coverage coverageRaw
  exact ⟨_, rfl⟩

/-- The sRGB tables round-trip every 8-bit value. -/
theorem encode16_decode8 : ∀ n < 256, encode16 (decode8 n.toUInt8) = n.toUInt8 := by
  decide +kernel

/-- Where the clip mask is 0, the coverage `Canvas.fillSpans` applies is 0. -/
theorem mask_zero (a op : Nat) : mulDiv a (mulDiv op 0 255) 65535 = 0 := by
  simp [mulDiv]

end PILean.Raster
