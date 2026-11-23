/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Anim.Animation

/-!
# Theorems about animation frames

Frame `i` of an animation is the drawing at the time `i / fps`.

* `time_eq_exactTime`: the time the writers pass to the drawing function, `Animation.time i`, is
  the `Float` conversion (`Exact.toFloat`) of the exact rational `Animation.exactTime i = i / fps`.
* `frameSeq_size`, `frameSeq_getElem`: the frame sequence that the animated PNG and GIF writers
  receive has `frameCount` frames, and frame `i` is `Animation.image i`, the rasterised drawing
  `a.frame (a.time i)`.
* `frameTrees_size`, `frameTrees_getElem`: the same for the element trees of the animated SVG.

Not proved: `frameCount` (a rounding of the `Float` duration times the frame rate), the
rasteriser's output for a drawing, and the viewer's interpolation between keyframes in the
animated SVG. Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace PILean

open Canvas

namespace Animation

variable (a : Animation)

/-- The time of frame `i` is the conversion of the exact fraction `i / fps`. -/
theorem time_eq_exactTime (i : Nat) : a.time i = Exact.toFloat (a.exactTime i) := rfl

/-- The exact time of frame `i` is `i / fps` when the frame rate is positive. -/
theorem exactTime_eq (i : Nat) (h : 0 < a.fps) : a.exactTime i = (i : Rat) / a.fps := by
  rw [exactTime, Nat.max_eq_left h]

/-- The exact times of consecutive frames differ by one frame, `1 / fps` (a frame rate of zero
counts as one). -/
theorem exactTime_succ (i : Nat) :
    a.exactTime (i + 1) - a.exactTime i = 1 / (max a.fps 1 : Nat) := by
  simp only [exactTime]
  push_cast
  grind

/-- Frame `i` is the rasterised drawing at the time `time i`, composited in the animation's colour
space. -/
theorem image_eq (i : Nat) :
    a.image i = (a.frame (a.time i)).toImage a.width a.height a.text a.background a.space := rfl

/-- The frame sequence has one frame for each of the `frameCount` frames. -/
theorem frameSeq_size : a.frameSeq.frames.size = a.frameCount := by
  simp [frameSeq]

/-- Frame `i` of the frame sequence is the drawing at the time `time i`. -/
theorem frameSeq_getElem (i : Nat) (h : i < a.frameSeq.frames.size) :
    a.frameSeq.frames[i] =
      (a.frame (a.time i)).toImage a.width a.height a.text a.background a.space := by
  simp [frameSeq, image_eq]

/-- The animated PNG and the GIF are written from the frame sequence. -/
theorem toApng_eq : a.toApng = a.frameSeq.toApng := rfl

/-- The GIF is written from the frame sequence. -/
theorem toGif_eq (dither : Bool) : a.toGif dither = a.frameSeq.toGif dither := rfl

/-- The animated SVG has one tree for each of the `frameCount` frames. -/
theorem frameTrees_size (mode : TextMode) : (a.frameTrees mode).size = a.frameCount := by
  simp [frameTrees]

/-- Tree `i` of the animated SVG is the rendering of the drawing at the time `time i`. -/
theorem frameTrees_getElem (mode : TextMode) (i : Nat) (h : i < (a.frameTrees mode).size) :
    (a.frameTrees mode)[i] = Svg.el "g" #[] ((a.frame (a.time i)).render mode) := by
  simp [frameTrees]

/-- The hypotheses can be met: at 30 frames per second, frame 15 is at half a second. -/
example (a : Animation) (h : a.fps = 30) : a.exactTime 15 = 1 / 2 := by
  rw [a.exactTime_eq 15 (by omega), h]
  decide +kernel

end Animation

end PILean
