/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Trust.Attr
import PILeanTest.Motion

/-!
# Motions in the gallery's build

The three golden motions of `PILeanTest.Motion` as figures of the gallery's build
(`lake exe pilean-build`), each marked `@[figure illustration]`: a motion is an illustration (its
key frames are exact figures; the motion between them is declared moves checked to land on the
next key), so the build records it as one. `linkedTurn` is the quarter turn with a theorem linked
to it by `figure_links`, to show that a motion can be linked like any figure: the theorem's
statement names the motion.
-/

namespace PILeanTest.MotionFigures

open PILean PILean.Plane PILeanTest.MotionChecks

/-- One point turned a quarter about the origin, then an idle step. -/
@[figure illustration] def turn : Motion := turnMotion

/-- A point turned about two centres in turn, with a rigid body, a point that appears and one that
slides. -/
@[figure illustration] def twoCentres : Motion := twoCentresMotion

/-- A disk turned a fifth about an outside centre. -/
@[figure illustration] def fifth : Motion := fifthMotion

/-- The quarter turn, with a theorem linked to it. -/
@[figure] def linkedTurn : Motion := turnMotion

/-- The linked quarter turn has three key frames, and its first step turns `P` a quarter about the
origin. -/
theorem linkedTurn_steps : linkedTurn.keys.size = 3 ∧
    (linkedTurn.steps[0]?.map (·.moves.map (·.1))) = some #["P"] := by
  decide +kernel

figure_links linkedTurn linkedTurn_steps

end PILeanTest.MotionFigures
