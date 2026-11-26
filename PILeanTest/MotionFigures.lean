/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Trust.Attr
import PILeanTest.Motion
import PILeanTest.MotionPanels

/-!
# Motions in the gallery's build

The three golden motions of `PILeanTest.Motion` and the golden picture of panels of
`PILeanTest.MotionPanels` as figures of the gallery's build (`lake exe pilean-build`), each marked
`@[figure illustration]`: no theorem is linked to them. `linkedTurn` is a small motion with a
theorem linked to it by `figure_links` that writes it out whole (its key figures and its declared
moves), as every gallery figure's theorem does (`#assert_figures_pinned`).
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

/-- Two key frames of one point `P` turned a quarter about the origin `O`, written out with the
library's builders alone, so that its theorem can state it whole. -/
@[figure] def linkedTurn : Motion :=
  { keys := #[{ items := #[Plane.Exact.point ((0, 0) : Rat × Rat) |>.faint,
                  Plane.Exact.label "O" ((0, 0) : Rat × Rat) .belowLeft |>.faint,
                  (Plane.Exact.point ((1, 0) : Rat × Rat) |>.accent 0).actor "P"],
                width := 240 },
              { items := #[Plane.Exact.point ((0, 0) : Rat × Rat) |>.faint,
                  Plane.Exact.label "O" ((0, 0) : Rat × Rat) .belowLeft |>.faint,
                  (Plane.Exact.point ((0, 1) : Rat × Rat) |>.accent 0).actor "P"],
                width := 240 }]
    captions := #["Key 1 of 2: P at (1, 0).", "Key 2 of 2: P turned a quarter about O."]
    steps := #[{ moves := #[("P", Plane.Exact.turnAbout ((0, 0) : Rat × Rat) (1 / 4))] }]
    info := { title := "P turns a quarter", description := "The point P turns about O." } }

/-- The linked motion, written out: its two key figures (the origin `O` with its label, and the
point `P` at `(1, 0)`, then at `(0, 1)`), its captions, its title and description, and its one
step, which turns `P` about `(0, 0)` by `1/4` of a full turn. A theorem about a motion states its
key figures and its declared moves; the frames the browser draws between the keys are not part
of it. -/
theorem linkedTurn_spec : linkedTurn =
    { keys := #[{ items := #[Plane.Exact.point ((0, 0) : Rat × Rat) |>.faint,
                    Plane.Exact.label "O" ((0, 0) : Rat × Rat) .belowLeft |>.faint,
                    (Plane.Exact.point ((1, 0) : Rat × Rat) |>.accent 0).actor "P"],
                  width := 240 },
                { items := #[Plane.Exact.point ((0, 0) : Rat × Rat) |>.faint,
                    Plane.Exact.label "O" ((0, 0) : Rat × Rat) .belowLeft |>.faint,
                    (Plane.Exact.point ((0, 1) : Rat × Rat) |>.accent 0).actor "P"],
                  width := 240 }]
      captions := #["Key 1 of 2: P at (1, 0).", "Key 2 of 2: P turned a quarter about O."]
      steps := #[{ moves := #[("P", Plane.Exact.turnAbout ((0, 0) : Rat × Rat) (1 / 4))] }]
      info := { title := "P turns a quarter", description := "The point P turns about O." } } :=
  rfl

figure_links linkedTurn linkedTurn_spec

/-- The golden picture of two panels on one clock (`PILeanTest.MotionPanels`), with its narrow
rendition. -/
@[figure illustration] def panels : MotionPanels := PILeanTest.MotionPanelsChecks.framesPanels

end PILeanTest.MotionFigures
