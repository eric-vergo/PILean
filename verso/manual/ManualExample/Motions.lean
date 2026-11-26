/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Trust.Attr

/-!
# The example manual's motions

Motions of plane figures, shown inline with their key stills (the shapes of PILean's gallery of
motions), both illustrations:

* `quarterTurn`: a point turned a quarter about the origin, then held;
* `slidePanels`: two panels on one clock, a point turned a quarter about the origin beside a point
  slid along a line, with a narrow rendition stacked for small screens.
-/

namespace ManualExample

open PILean PILean.Plane

/-- A rational point. -/
abbrev Q := Rat × Rat

/-- A key figure of `quarterTurn`: the unit circle and the origin `O`, faint, and the point `P`
on the circle at `p`, with its label. -/
def quarterKey (p : Q) : Plane.Figure :=
  { items := #[Plane.Exact.circle ((0, 0) : Q) (1 : Rat) |>.faint |>.named "the unit circle",
      Plane.Exact.point ((0, 0) : Q) |>.faint,
      Plane.Exact.label "O" ((0, 0) : Q) .belowLeft |>.faint,
      (group #[Plane.Exact.point p |>.accent 0 |>.incident .on "the unit circle",
        Plane.Exact.label "P" p .aboveRight |>.accent 0]).actor "P"],
    width := 320 }

/-- The point `P` turned a quarter about the origin `O`, then held. -/
@[figure illustration]
def quarterTurn : Motion :=
  { keys := #[quarterKey (1, 0), quarterKey (0, 1), quarterKey (0, 1)]
    captions := #["P on the unit circle at (1, 0).", "P turned a quarter about O, to (0, 1).",
      "Nothing moves."]
    steps := #[{ moves := #[("P", Plane.Exact.turnAbout ((0, 0) : Q) (1 / 4))] },
      MotionStep.idle]
    info := { title := "A quarter turn", description := "The point P turns about the origin O." } }

/-- A panel's key: two faint corner points that fix the frame, a line below, and the point `X` at
`p`. -/
def panelKey (p : Point) : Plane.Figure :=
  { items := #[Plane.point ⟨-2, -2⟩ |>.faint, Plane.point ⟨2, 2⟩ |>.faint,
      Plane.segment ⟨-2, -1.5⟩ ⟨2, -1.5⟩ |>.faint, (Plane.point p |>.accent 0).actor "X"] }

/-- The left panel: `X` turned a quarter about the origin, twice, then held. -/
def turner : Motion where
  keys := #[panelKey ⟨1, 0⟩, panelKey ⟨0, 1⟩, panelKey ⟨-1, 0⟩, panelKey ⟨-1, 0⟩]
  steps := #[{ moves := #[("X", .turn ⟨0, 0⟩ (1 / 4))] },
    { moves := #[("X", .turn ⟨0, 0⟩ (1 / 4))] }, MotionStep.idle]

/-- The right panel: `X` slid by one, then still while the other panel moves, then held. -/
def slider : Motion where
  keys := #[panelKey ⟨-1, 1⟩, panelKey ⟨0, 1⟩, panelKey ⟨0, 1⟩, panelKey ⟨0, 1⟩]
  steps := #[{ moves := #[("X", .slide ⟨1, 0⟩)] }, {}, MotionStep.idle]

/-- Two panels on one clock: a point turned about the origin beside a point slid along a line,
stacked on small screens. -/
@[figure illustration]
def slidePanels : MotionPanels where
  panels := #[{ title := "Turn", motion := turner }, { title := "Slide", motion := slider }]
  captions := #["The start.", "X turns a quarter on the left and slides on the right.",
    "X turns a quarter again on the left.", "Nothing moves."]
  info := { title := "A turn beside a slide",
            description := "Left: a point turns by quarters about the origin. Right: a point \
              slides one step to the right." }
  narrowWidth := some 300

end ManualExample
