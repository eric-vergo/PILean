/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Trust.Attr

/-!
# The example's motions

Motions of plane figures, shown inline on the chapter's pages "Motion" and "Escaping" with
their key stills (the shapes of PILean's gallery of motions):

* `quarterTurn`: a point turned a quarter about the origin, then held; linked to
  `quarterTurn_spec`, which writes it out whole (its key figures and its declared moves);
* `fifthTurn`: a disk turned a fifth about an outside centre, an illustration;
* `twoFrames`: two panels on one clock, a point turned by fifths about two centres beside the pair
  of centres turned about the point's centre of the moment, with a narrow rendition stacked for
  small screens, an illustration;
* `oddMotion`: two panels whose strings hold markup, shown on the page "Escaping".
-/

namespace Example

open PILean PILean.Plane

/-- A rational point. -/
abbrev Q := Rat × Rat

/-! ### One point, a quarter turn -/

/-- The key figure of `quarterTurn` with the point `P` at `p`: the unit circle and the origin
`O`, faint, and `P` with its label. -/
def quarterKey (p : Q) : Plane.Figure :=
  { items := #[Plane.Exact.circle ((0, 0) : Q) (1 : Rat) |>.faint |>.named "the unit circle",
      Plane.Exact.point ((0, 0) : Q) |>.faint,
      Plane.Exact.label "O" ((0, 0) : Q) .belowLeft |>.faint,
      (group #[Plane.Exact.point p |>.accent 0 |>.incident .on "the unit circle",
        Plane.Exact.label "P" p .aboveRight |>.accent 0]).actor "P"],
    width := 320 }

/-- The point `P` turned a quarter about the origin `O`, then held. -/
@[figure]
def quarterTurn : Motion :=
  { keys := #[quarterKey (1, 0), quarterKey (0, 1), quarterKey (0, 1)]
    captions := #["P on the unit circle at (1, 0).", "P turned a quarter about O, to (0, 1).",
      "Nothing moves."]
    steps := #[{ moves := #[("P", Plane.Exact.turnAbout ((0, 0) : Q) (1 / 4))] },
      MotionStep.idle]
    info := { title := "A quarter turn", description := "The point P turns about the origin O." } }

/-- The motion `quarterTurn` written out: three key figures (the unit circle, the origin `O` and
the point `P` at `(1, 0)`, then twice at `(0, 1)`), its captions, its title and description, and
its two steps: `P` turned about `(0, 0)` by `1/4` of a full turn, then an idle step; its points are
pairs of rationals. -/
theorem quarterTurn_spec : quarterTurn =
    { keys := #[quarterKey (1, 0), quarterKey (0, 1), quarterKey (0, 1)]
      captions := #["P on the unit circle at (1, 0).", "P turned a quarter about O, to (0, 1).",
        "Nothing moves."]
      steps := #[{ moves := #[("P", Plane.Exact.turnAbout ((0, 0) : Q) (1 / 4))] },
        MotionStep.idle]
      info := { title := "A quarter turn",
                description := "The point P turns about the origin O." } } ∧
    (∀ p : Q, quarterKey p =
      { items := #[Plane.Exact.circle ((0, 0) : Q) (1 : Rat) |>.faint |>.named "the unit circle",
          Plane.Exact.point ((0, 0) : Q) |>.faint,
          Plane.Exact.label "O" ((0, 0) : Q) .belowLeft |>.faint,
          (group #[Plane.Exact.point p |>.accent 0 |>.incident .on "the unit circle",
            Plane.Exact.label "P" p .aboveRight |>.accent 0]).actor "P"],
        width := 320 }) ∧
    Q = (Rat × Rat) :=
  ⟨rfl, fun _ => rfl, rfl⟩

figure_links quarterTurn quarterTurn_spec

/-! ### A disk, a fifth of a turn -/

/-- The disk `D` with its centre and label, its centre at angle `a` on the circle of radius
`2.5` about the origin. -/
def diskAt (a : Float) : Item :=
  let c := Plane.polar 2.5 a
  (group #[Plane.disk c 1.2 |>.accent 1, Plane.point c |>.accent 1,
    Plane.label "D" c .above |>.accent 1]).actor "D"

/-- The disk `D` turned a fifth about the origin `O`, then held. -/
@[figure illustration]
def fifthTurn : Motion :=
  let o := #[Plane.point ⟨0, 0⟩ |>.faint, Plane.label "O" ⟨0, 0⟩ .belowLeft |>.faint]
  let at72 := diskAt (2 * Plane.pi / 5)
  { keys := #[{ items := o.push (diskAt 0), width := 360 }, { items := o.push at72, width := 360 },
      { items := o.push at72, width := 360 }]
    captions := #["The disk D.", "D turned a fifth about O.", "Nothing moves."]
    steps := #[{ moves := #[("D", Plane.Exact.turnAbout ((0, 0) : Q) (1 / 5))] },
      MotionStep.idle]
    info := { title := "A fifth of a turn", description := "The disk D turns about O by 72°." } }

/-! ### Two frames on one clock -/

/-- The point `p` turned about `c` by `q` of a full turn, counterclockwise. -/
def turnPoint (c p : Point) (q : Float) : Point :=
  let θ := 2 * Plane.pi * q
  let d := p - c
  ⟨c.x + d.x * θ.cos - d.y * θ.sin, c.y + d.x * θ.sin + d.y * θ.cos⟩

/-- The first centre at the start. -/
def centreA : Point := ⟨-0.4, 0⟩

/-- The second centre at the start. -/
def centreB : Point := ⟨0.4, 0⟩

/-- The radius of the disks. -/
def radius : Float := 1.4

/-- The point at the start. -/
def start : Point := ⟨0.1, 0.5⟩

/-- The point `P` with its label, an actor. -/
def pointP (p : Point) : Item :=
  (group #[Plane.point p |>.accent 0, Plane.label "P" p .aboveRight |>.accent 0]).actor "P"

/-- The positions of the point in the left panel at the five keys: turned a fifth about `A`,
then about `B`, then not at all, then about `A` again. -/
def leftPositions : Array Point :=
  let p1 := turnPoint centreA start 0.2
  let p2 := turnPoint centreB p1 0.2
  #[start, p1, p2, p2, turnPoint centreA p2 0.2]

/-- The left panel: the disks fixed, the point turned by fifths about the active centre. -/
def leftPanel : Motion where
  keys := leftPositions.map fun p =>
    { items := #[Plane.circle centreA radius |>.faint, Plane.circle centreB radius |>.faint,
        Plane.point centreA, Plane.label "A" centreA .below, Plane.point centreB,
        Plane.label "B" centreB .below, pointP p] }
  steps := #[{ moves := #[("P", .turn centreA (1 / 5))] },
    { moves := #[("P", .turn centreB (1 / 5))] }, MotionStep.idle,
    { moves := #[("P", .turn centreA (1 / 5))] }]

/-- The rigid body of the right panel: the two disks, the edge between the centres and the
centres with their labels, five actors that move together. -/
def body (a b : Point) : Array Item :=
  #[Plane.disk a radius |>.accent 1 |>.actor "DA", Plane.disk b radius |>.accent 2 |>.actor "DB",
    Plane.segment a b |>.actor "E",
    (group #[Plane.point a |>.accent 1, Plane.label "A" a .above]).actor "A",
    (group #[Plane.point b |>.accent 2, Plane.label "B" b .below]).actor "B"]

/-- The ids of the body's actors. -/
def bodyIds : Array String := #["DA", "DB", "E", "A", "B"]

/-- The centres of the right panel at the five keys: the pair turned a fifth backwards about `A`,
then about `B` where it is then, then not at all, then about `A` where it is then. -/
def rightCentres : Array (Point × Point) :=
  let b1 := turnPoint centreA centreB (-0.2)
  let a2 := turnPoint b1 centreA (-0.2)
  #[(centreA, centreB), (centreA, b1), (a2, b1), (a2, b1), (a2, turnPoint a2 b1 (-0.2))]

/-- The right panel: the point fixed, the pair of centres with their disks and edge turned by
fifths about whichever centre is active. -/
def rightPanel : Motion where
  keys := rightCentres.map fun (a, b) =>
    { items := body a b ++ #[Plane.point start |>.accent 0, Plane.label "P" start .below] }
  steps :=
    let all := fun (c : Point) => { moves := bodyIds.map fun id => (id, Move.turn c (-1 / 5)) }
    #[all centreA, all (rightCentres[1]!.2), MotionStep.idle, all (rightCentres[3]!.1)]

/-- The two frames on one clock: on the left the point turns by fifths about the active centre
while the disks stay; on the right the pair of centres turns about the active centre while the
point stays. Stacked on small screens. -/
@[figure illustration]
def twoFrames : MotionPanels where
  panels := #[{ title := "The point turns", motion := leftPanel },
    { title := "The centres turn", motion := rightPanel }]
  captions := #["The start.", "A fifth of a turn about A.", "A fifth of a turn about B.",
    "Nothing moves.", "A fifth of a turn about A."]
  info := { title := "Two frames on one clock",
            description := "Left: the point P turns by fifths about the active centre while the \
              disks stay. Right: the pair of centres with its disks turns by fifths about the \
              active centre while the point stays." }
  narrowWidth := some 360

/-! ### Strings that hold markup -/

/-- A key of `oddPanel`: two faint corner points that fix the frame and the point `id`, with a
label `text`, at `p`. -/
def oddKey (id text : String) (p : Point) : Plane.Figure :=
  { items := #[Plane.point ⟨-2, -2⟩ |>.faint, Plane.point ⟨2, 2⟩ |>.faint,
      (group #[Plane.point p |>.accent 0, Plane.label text p .aboveRight |>.accent 0]).actor id] }

/-- A panel of `oddMotion`: the actor `id`, labelled `text`, turned a quarter about the origin,
then held. -/
def oddPanel (id text : String) : Motion where
  keys := #[oddKey id text ⟨1, 0⟩, oddKey id text ⟨0, 1⟩, oddKey id text ⟨0, 1⟩]
  steps := #[{ moves := #[(id, .turn ⟨0, 0⟩ (1 / 4))] }, MotionStep.idle]

/-- A picture of two panels whose title, description, panel titles, captions, labels and actor
ids hold markup, quotes, the end of a CDATA section, `--` and `url(#…)`: the page must show them
as text. -/
@[figure illustration]
def oddMotion : MotionPanels where
  panels := #[
    { title := "<script>alert(1)</script> \"q\" ]]> --",
      motion := oddPanel "<script>alert(3)</script>\"&'" "<i>P</i> & \"Q\"" },
    { title := "</style> url(#x) <!--", motion := oddPanel "]]> -- url(#a)" "</desc> ]]>" }]
  captions := #["<script>alert(1)</script> one.", "\"Quotes\" & 'marks' ]]> -- two.",
    "</style><b>three</b> url(#x)."]
  info := { title := "<title>]]></title> & \"odd\"",
            description := "</desc><script>alert(2)</script> -- <!-- url(#x)" }

end Example
