/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILean
import PILean.Trust.Attr
import PILeanVersoManual
import PILeanManual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open PILeanVerso.Manual
open PILeanManual

#doc (Manual) "Motions" =>
%%%
tag := "motions"
%%%

```lean -show
namespace PILeanManual.Motions
open PILean PILean.Plane PILean.Anim
```

A *motion* is a looping animation of a plane figure that is given by its rests, not by a
function of time: a list of exact figures, the *key frames*, and for each step between two
consecutive key frames what moves. The motion is written as an animated SVG that the browser plays
by itself (SMIL, no script) and, beside it, one still for every key frame, which is the key frame
drawn by the plane figures' own pipeline. So a reader of a page sees a figure move, and a reader
who cannot or does not want motion sees the key frames in order, each with a caption, and every
one of them is an exact figure of the library with its checks and its metadata. This chapter
follows the writing of one motion from the figures to the page; the model's own documentation is
{api}`PILean.Plane.Motion`, the timing's {api}`PILean.Anim.Timeline`, and the outputs' and
checks' {api}`PILean.Trust.Motion`. An {name}`PILean.Animation` (a drawing as a function of
time, see {ref "animations"}[Animations]) is the tool for a plot that changes continuously; a
motion is the tool for a construction that goes from one picture to the next.

# Key Frames and Actors
%%%
tag := "motions-keys"
%%%

A {name}`PILean.Plane.Motion` has `keys`, an array of {name}`PILean.Plane.Figure`s. Key `k` is the
picture at rest `k`; the first is shown while the loop starts, the last before it closes. Each key
frame is an ordinary plane figure, so it may use everything the chapter on plane figures
describes: exact points, labels, metadata, incidences, colour roles. Nothing rescales while a
motion runs: all keys are drawn in one view that holds every key and everything the turns sweep
(each turning actor at the start and end of its turn and wherever its points are farthest on their
circles), so a key that sets a frame of its own is an error.

What moves is an *actor*: a top-level item of the key figures that carries an id
({name}`PILean.Plane.Item.actor`, the same as {name}`PILean.Plane.Item.withId`). The same id in
consecutive keys names the same actor. An item without an id does not move; if it differs between
two keys it crossfades, and a note says so. A group carries a point and its label, or a polygon
and its vertex marks, as one actor.

```lean
/-- A rational point. -/
abbrev Q := Rat × Rat

/-- Faint reference marks, the same in every key: the origin and its name. -/
def backdrop : Array Item :=
  #[Plane.Exact.point ((0, 0) : Q) |>.faint,
    Plane.Exact.label "O" ((0, 0) : Q) .belowLeft |>.faint]

/-- The triangle `T` (actor `"T"`), with its label at its first vertex. -/
def triangle (a b c : Q) : Item :=
  (group #[Plane.Exact.polygon [a, b, c] |>.filled |>.accent 0,
    Plane.Exact.label "T" a .aboveRight |>.accent 0]).actor "T"

/-- The square mark `S` (actor `"S"`). -/
def mark (p : Q) : Item := Plane.Exact.point p |>.marker .square |>.accent 2 |>.actor "S"

/-- The point `B` with its label (actor `"B"`). -/
def newcomer : Item :=
  (group #[Plane.Exact.point ((-3, 1) : Q) |>.accent 1,
    Plane.Exact.label "B" ((-3, 1) : Q) .above |>.accent 1]).actor "B"

/-- The disk `D` (actor `"D"`) of radius `r`. -/
def disk (r : Rat) : Item := Plane.Exact.disk ((3, -2) : Q) r |>.accent 1 |>.actor "D"

/-- The key frame of the motion below with the triangle at `(a, b, c)`, the mark at `s` (if
any), `B` present or not and the disk of radius `r`. -/
def tourKey (a b c : Q) (s : Option Q) (b? : Bool) (r : Rat) : Plane.Figure :=
  { items := backdrop ++ #[triangle a b c] ++ (s.map fun p => #[mark p]).getD #[] ++
      (if b? then #[newcomer] else #[]) ++ #[disk r],
    width := 420 }
```

# Declaring Moves
%%%
tag := "motions-moves"
%%%

For every step, {name}`PILean.Plane.MotionStep` lists the moves of the actors it moves, by id
(`moves : Array (String × Move)`); an actor that is not named stays where it is. A
{name}`PILean.Plane.Move` is one of

* `turn centre turns`: a turn about `centre` by an exact fraction of a full turn, counterclockwise
  in the figure's coordinates (`1/4` is 90°); {name}`PILean.Plane.Exact.turnAbout` takes the
  centre as an exact point;
* `slide v`: a slide along the vector `v` ({name}`PILean.Plane.Exact.slideFromTo` takes the
  two exact points);
* `appear`: the actor is in the next key and not in this one, and fades in;
* `vanish`: the actor is in this key and not in the next, and fades out;
* `morph`: the actor's drawing changes between the keys (a disk whose radius changes), and the
  browser interpolates the path data; where the drawings cannot be interpolated, they crossfade,
  which is an error under the default level of checks. With `Motion.between`, an author who has
  the figure at fractions of the step exactly can give it, and the morph is sampled there.

A turn is drawn as true arcs: each point of the actor moves on its circle at the eased angle. The
labels and markers of a turning actor ride the turn but are not turned themselves, so text stays
upright. A step in which nothing moves is {name}`PILean.Plane.MotionStep.idle`; it takes its time.

```lean
/-- Six key frames and five steps, one for each kind of move. -/
@[figure illustration]
def tour : Motion where
  keys :=
    let t0 : Q × Q × Q := ((1, 0), (3, 0), (1, 1))
    let t1 : Q × Q × Q := ((0, 1), (0, 3), (-1, 1))
    let k := fun (t : Q × Q × Q) => tourKey t.1 t.2.1 t.2.2
    #[k t0 (some (-2, -2)) false (1 / 2), k t1 (some (-2, -2)) false (1 / 2),
      k t1 (some (0, -2)) false (1 / 2), k t1 (some (0, -2)) true (1 / 2),
      k t1 (some (0, -2)) true 1, k t1 none true 1]
  captions := #["T, the square S, the disk D.", "T turns a quarter about O.",
    "S slides two to the right.", "B appears.", "The radius of D grows from 1/2 to 1.",
    "S vanishes."]
  steps := #[
    { moves := #[("T", Plane.Exact.turnAbout ((0, 0) : Q) (1 / 4))] },
    { moves := #[("S", Plane.Exact.slideFromTo ((-2, -2) : Q) (0, -2))] },
    { moves := #[("B", .appear)] },
    { moves := #[("D", .morph)] },
    { moves := #[("S", .vanish)] }]
  info :=
    let description := "A triangle turns about the origin, a mark slides, a point appears, a \
      disk grows and the mark vanishes."
    { title := "One of each move", description }
```

:::figure PILeanManual.Motions.tour (alt := "A blue triangle labelled T turns a quarter about the origin O, a green square slides to the right, a point B appears, an orange disk grows and the square vanishes; then the picture starts again.")
Every kind of move, one step each.
:::

Each declared move is checked to land on the next key (the next section). For a turn that means
the actor in key `k`, turned about the centre by the stated fraction, is the actor in key
`k + 1`; the check compares leaf by leaf the kinds, looks, texts, metadata and the anchors that
fix each drawing (a point, the ends of a segment, a circle's centre, a polygon's vertices, an
arc's ends, a label's point) to within 0.01 px. It does not see the direction or the number of
revolutions of a turn (a turn by `1/5` and one by `6/5` land alike), so a turn by a whole turn
or more is an error unless the step sets `allowFullTurns`.

# Pacing and Easing
%%%
tag := "motions-pacing"
%%%

The timing is exact: durations are rational numbers of seconds
({name}`PILean.Anim.Pacing`, {name}`PILean.Anim.Timeline`), so the cycle, the start of every
segment and the boundaries as fractions of the cycle are exact, and facts about them can be
stated as theorems about rationals. A cycle rests on key `0` for `firstHold`; then, for each
step, moves for the step's duration and rests on the next key for `hold` (`lastHold` after the last step). By
default a step takes the pacing's time for the longest kind of move it has (`turn` 1 s; `slide`
0.8 s, which a morph takes too; `fade` 0.35 s for an appearance or a disappearance, and for a step
with no moves); an idle step (`MotionStep.idle`) takes `idle` (0.9 s) and is not eased. A step can
set its own `duration` and its own `easing`. Progress through every segment is
eased by a cubic Bézier curve as in SMIL's `keySplines` and CSS:
{name}`PILean.Anim.Easing.standard` (`ease-in-out`, the default), `Easing.linear`, or
`Easing.spline x₁ y₁ x₂ y₂`.

The loop closes with the *seam*: under `Seam.crossfade d` (the default, 0.4 s) the picture fades
out at the end of the cycle and in at its start, and the jump from the last key back to the first
happens while nothing is visible; under `Seam.cut` the picture jumps.

```lean (name := cycleEx)
#eval tour.timeline.cycle
#eval tour.timeline.keyTimes.size
#eval tour.animSteps.map (·.dur)
```

```leanResult cycleEx
```

The cycle is the holds plus the steps plus the seam: 1.2 + 3.3 + 4 × 0.6 + 1.8 + 0.4 = 9.1 s; the
key times are the 14 boundaries of the segments, as fractions of the cycle.

# Checks
%%%
tag := "motions-checks"
%%%

A motion that contradicts its keys is not drawn. {name}`PILean.Plane.Motion.report` computes the
keys as drawn, the plan and the problems once; {name}`PILean.Plane.Motion.svg?` and
{name}`PILean.Plane.Motion.animation?` return the animated SVG and the baked frames, or the
messages of the errors that stop them. The problems are of two severities, an error and a note,
and include five groups of checks:

* the *arrival* of every declared move at its key (above), and the other rules of a step (an actor
  that differs without a declared move, comes without `appear`, leaves without `vanish`, or has a
  morph that cannot be interpolated);
* the *layout checks* of the plane figures on every key (overlaps, contrast, labels), after the
  automatic label placements are fixed on the first key where their actor appears, so that a label
  rides its actor on every later key;
* the *rests*: at the middle of every key's rest the whole baked drawing, every path and every
  text, is the key's still within 0.05 px, which bounds what the per-step tolerance can add up to
  and catches a wrong counter-rotation or stacking order;
* the *writer against the baker*: the written SVG, read back with the evaluator of SMIL timing, is
  what the baker draws, at the middle of every rest and every move;
* the *bounds*: nothing of any layer leaves the picture while it moves.

A step that cannot be as declared is an example worth reading once:

```lean (name := badEx)
/-- `tour` with the first turn declared as an eighth, which does not land on key 1. -/
def badTour : Motion :=
  let eighth : MotionStep := { moves := #[("T", Plane.Exact.turnAbout ((0, 0) : Q) (1 / 8))] }
  { tour with steps := tour.steps.set! 0 eighth }

#eval match badTour.svg? with
  | .error es => es
  | .ok _ => #["written"]
#eval match tour.svg? with
  | .error es => es
  | .ok _ => #["written"]
```

```leanResult badEx
```

The *level* of the checks is `Motion.checks`. Under `CheckLevel.fail`, the default, an error stops
the motion: `svg?` gives the messages and nothing is written. Under `CheckLevel.warn` the errors
are warnings on the animated SVG, and a move that misses its key is drawn as a crossfade between
the two drawings; under `ignore` the checks are not reported. Whatever the level, a motion that is
not well formed (a caption per key, one step fewer than keys, a poster among the keys), whose
written picture would have an id twice (actor ids that differ but are written alike, `a b` and
`a_b`), or whose panels use different text engines, is stopped.

A motion is *checked strictly* when it was built at `fail` and has no error left. By default a
build writes only such motions: `pilean-build` refuses the others before it renders anything, and a
site build fails. `pilean-build --allow-unchecked` (for a site, `--figure-allow-unchecked`) writes a
motion built at another level, for a draft: its files record the level and the number of errors
left (`errorsLeft` in the manifest), and its figure page says in words what that means.
{ref "trust-pilean-build"}[`pilean-build`] lists the options; `--require-checked` is accepted and
is the default.

# Questions That Come Up
%%%
tag := "motions-questions"
%%%

* *A moving point that lands on a point of the next key.* The layout checks keep two markers at
  least 2 px apart (`CheckOptions.markerGap`) on every key, so a moving copy cannot come to rest on
  a point that is another item. Make them one actor: give the point of the later key the moving
  actor's id, so the actor that moves is the point that stays. When the two must be different items
  (a different look, say), they can only crossfade, and the point dips in opacity for the length of
  the fade; the model has no declaration that one actor becomes another item.
* *An item that appears or vanishes needs an id.* `appear` and `vanish` name an actor, so an item
  that is in one key and not the next carries an id ({name}`PILean.Plane.Item.actor`), also when the
  key is a static figure reused; the items that stay as they are need none.
* *Labels placed automatically.* A label with an automatic placement is placed once, on the first
  key where its actor appears, against that key's elements, and rides its actor afterwards; a
  stroke that appears in a later key is not considered, and the layout checks of that key report
  the collision. Give such a label an explicit placement (`.above`, `.right`, …, or an offset).
  Placing it against the elements of all keys at once would be a change to the placement, which
  is not made.
* *The same items, fainter.* {name}`PILean.Plane.Item.fillOpacity` sets the opacity of a tint;
  there is no opacity for strokes. For a fainter stroke use {name}`PILean.Plane.Item.faint`, or a
  colour role of the style (`PlaneStyle.roles`, {name}`PILean.Plane.Item.role`), which keeps a
  dark twin; a fixed colour with an alpha ({name}`PILean.Plane.Item.color`) has none.
* *A curved arrow.* An arc with an arrowhead is an element of its own:
  `Plane.arc c r θ₀ θ₁ |>.withArrow` ({name}`PILean.Plane.Item.withArrow`) ends in an arrowhead
  at `θ₁` (with `θ₁ < θ₀` it points clockwise), and {name}`PILean.Plane.angleMark` draws an angle
  mark with its arrowhead.

# Panels on One Clock
%%%
tag := "motions-panels"
%%%

{name}`PILean.Plane.MotionPanels` puts several motions side by side, or one above another, in one
SVG and on one timeline: step `k` of the picture is step `k` of every panel, so what the panels
show at a key is shown at the same moment. All panels have the same number of keys; a step is idle
when it is idle in every panel, and otherwise takes the longest kind of move any panel makes in it
(a panel that does not move in a step waits). The captions, the pacing, the title and the checks
level are the picture's, not the panels'. Each panel is a {name}`PILean.Plane.MotionPanel`: a
title and a motion with its own view.

By default the panels are drawn at one scale (`PanelScale.common`: a unit length is as long in
every panel); `PanelScale.independent` fits each to its share, for a panel that zooms in. A picture
can set `narrowWidth` to be rendered a second time, with its panels stacked at that width: that is
its *narrow rendition*, which a page shows on small screens. Its ids and its stills are its own.

```lean
/-- A panel's key: two faint points that fix the frame and the point `X` at `p`. -/
def panelKey (p : Point) : Plane.Figure :=
  { items := #[Plane.point ⟨-2, -2⟩ |>.faint, Plane.point ⟨2, 2⟩ |>.faint,
      (Plane.point p |>.accent 0).actor "X"] }

/-- A point turned by quarters about the origin. -/
def turner : Motion where
  keys := #[panelKey ⟨1, 0⟩, panelKey ⟨0, 1⟩, panelKey ⟨-1, 0⟩, panelKey ⟨-1, 0⟩]
  steps := #[{ moves := #[("X", .turn ⟨0, 0⟩ (1 / 4))] },
    { moves := #[("X", .turn ⟨0, 0⟩ (1 / 4))] }, MotionStep.idle]

/-- A point slid one to the right, then held while the other panel turns. -/
def slider : Motion where
  keys := #[panelKey ⟨-1, 1⟩, panelKey ⟨0, 1⟩, panelKey ⟨0, 1⟩, panelKey ⟨0, 1⟩]
  steps := #[{ moves := #[("X", .slide ⟨1, 0⟩)] }, {}, MotionStep.idle]

/-- A turn beside a slide, on one clock, stacked on small screens. -/
@[figure illustration]
def beside : MotionPanels where
  panels := #[{ title := "Turn", motion := turner }, { title := "Slide", motion := slider }]
  captions := #["The start.", "X turns on the left and slides on the right.",
    "X turns again on the left.", "Nothing moves."]
  info :=
    let description := "Left: a point turns by quarters about the origin. Right: a point slides \
      one step to the right."
    { title := "A turn beside a slide", description }
  narrowWidth := some 300
```

:::figure PILeanManual.Motions.beside (alt := "Two panels side by side. In the left panel, titled Turn, a point goes a quarter of the way round the origin, then another quarter. In the right panel, titled Slide, a point slides one step to the right during the first turn, then waits.")
Two motions on one clock.
:::

The panels' own checks are all there, labelled with the panel, and the picture adds its own:
unequal numbers of keys, captions that are not one per key, panels with one title, a panel whose
content or title does not fit its share, a line or a ray in a panel (it would run to the edge of
the whole page), panels on different backgrounds, and the composed picture's own rest check and
writer check. Every id of panel `i` carries the prefix `p{i + 1}-`, so two panels may use the
same actor ids.

# Captions and Text Alternative
%%%
tag := "motions-captions"
%%%

`captions` holds one caption per key, written without a counter: a page shows key `k` of `n` as
"Step `k` of `n`: " and the caption. They are the text alternative of the stills, and the contact
sheet shows each under its still. The motion's `info` has a title (the name a screen reader gives
the picture) and a description; the animated SVG's own description is the description followed by
the captions. A motion with an empty title, or with neither a description nor a caption, is
reported: as an error under the default level of checks, as a note otherwise.

# Standing
%%%
tag := "motions-standing"
%%%

A motion is a figure of the build like any other, with a standing ({ref "trust-check"}[what the
answers establish]). A motion without a linked theorem is marked as an illustration,
`@[figure illustration]`, as `tour` is; `pilean-build --require-standing` refuses one that is
not marked. A theorem is linked to a motion with `figure_links`, and the rule is the same as for
any figure: the theorem is proved from the standard axioms and its statement names the motion's
constant. What such a theorem can state is the key figures and the declared moves: the actors, the
centres and exact fractions of the turns, the vectors of the slides, the captions, the pacing and
the level of checks. It cannot state the frames the browser draws between the keys: the stills
are the key figures, the arrival check holds the moves to the keys within a tolerance in floating
point, and what happens between is the browser's drawing, checked in a browser (below) and not
part of any statement. A figure's page says this in words.

# The Files a Build Writes
%%%
tag := "motions-outputs"
%%%

For a motion `d` with `n` keys, `pilean-build` writes the files below. A site build writes the same
files and, for a motion with a dark twin, also the SVG of each key's still in the dark theme
(`d-key-k-dark.svg`, and `d-narrow-key-k-dark.svg` for the narrow rendition), which is all a page
shows of the dark motion:

| File | What it is |
|---|---|
| `d.svg` | the animated SVG, with the poster key's still inside it |
| `d-poster.png`, `d-poster.pdf` | the poster key's still |
| `d-keys.svg`, `.png`, `.pdf` | the contact sheet: every key's still in a grid with its caption, for print |
| `d-key-k.svg`, `.png` | the still of key `k` (from 0), byte for byte the SVG and PNG of the key figure |
| `d-narrow.svg`, `d-narrow-key-k.svg`, `.png` | the narrow rendition and its stills (a picture of panels with `narrowWidth`) |
| `d.png`, `d.gif` | the baked frames, only with `MotionFigure.rasters` |

Every file records the motion in its source record: the number of keys, the cycle in seconds,
the captions, the check level and the errors left. {name}`PILean.Plane.Motion.animation?` gives
the baked frames as an {name}`PILean.Animation`, the route to APNG and GIF. A motion that is
stopped writes none of these files.

# Showing a Motion in a Verso Page
%%%
tag := "motions-page"
%%%

Both Verso adapters show a motion wherever `:::figure` names one, as this chapter does; nothing
of it needs a script. The reader sees:

* *Motion on* (the default): the moving picture, inline, on its own clock, in the page's theme.
  Under it the caption, which ends with the note "Animation; a still replaces it while you point
  at it or focus it, or after a click or tap until you click elsewhere."
* *On hover or focus*: the poster key's still covers the picture, in the picture's own box, so
  nothing around it moves. Hover applies on a device that hovers, so a tap on a phone does not
  leave it stuck; focus is the keyboard, a click or a tap, and lasts until a click elsewhere, with
  a ring that is at least 3:1 against the page. The moving picture is only made transparent, so
  its text alternative stays, and its clock runs on: when the still goes, the picture is where
  its clock has got to, not where it was covered.
* *Motion off*: under the Blueprint's switch (`data-motion="reduce"`), under the reader's
  `prefers-reduced-motion: reduce`, and in print, the picture is hidden and the key stills are
  shown in a grid, each with its caption. The grid has as many columns as fit with each column at
  least three quarters of a still's width (one column for a wide picture of two panels, more for a
  small one), so that the text in the stills stays legible; a still wider than the page's column
  fills it. Assistive technology reads the list of key frames with
  their captions; with motion on it
  reads the picture's text alternative and then that list, once.
* *Small screens* (560 px or less): the narrow rendition and its stills, when the motion has one.

A figure's page lists what the animation is in words, the table of its steps (each step's keys,
its duration exactly, each move with its actor), the stills with their captions in the same kind
of grid, and every file, among them the contact sheet. Its code comes after the animation, folded
when it is longer than 60 lines.

The picture is hidden by `visibility` or `opacity`, never by `display: none`: Chromium freezes a
picture whose `transform` is animated when it is hidden with `display: none` and shown again,
until the animation repeats. A site's own stylesheet must not reach into the pictures: a rule on
`.pilean-inline-svg` or its descendants also matches a motion's moving picture, and must not set
`display`, `visibility`, `opacity`, `transform` or `animation` there, and must not repaint `fill`
or `stroke` inside a picture, which makes the live motion differ from its stills (the stills are
image files, which the rule does not reach). A site under a content policy must allow the `style`
element of every inline picture. The adapters' README lists the markup and the rules.

# Checking a Site
%%%
tag := "motions-site"
%%%

The scripts in the folder `tools/site/` are not needed to build a site, only to check
one; they read a published folder (the generator's `html-multi`) and its figures folder, need
Python 3 and, for the browser checks, the `playwright` package with a Chromium it can find
(nothing is installed or downloaded):

* `inline_check.py` holds every inline picture, a moving picture included, to its file: element
  for element, with the page's id prefix taken off, the poster's still over the picture, the list
  of stills to the key files, and the manifest's record (`fail`, no errors left);
* `markup_check.py` finds nothing active in a motion: no script, event attribute, link, form
  control, embedded content, animation started by anything but the clock, or tab stop other than
  the picture's own;
* `page_check.py` holds each figure's page to the manifest: a motion's files are exactly those
  the adapters write for it (the table above, with the dark twins of the key stills when the site
  has a dark theme), `7 + 6n` files with a narrow rendition and a dark twin, `6 + 3n` with a dark
  twin only, `7 + 4n` and `6 + 2n` without one; its sentence and its table of steps are there,
  and its stills are listed with their
  captions;
* `motion_browser.py SITE --expect DIR` loads every page with a motion in Chromium: the picture
  at the middle of every rest is where the key's still has it, labels and markers stay upright,
  motion off shows the stills with their captions, each still at three quarters of its width or
  more or as wide as its column, hover and focus show the poster's still in the picture's box, and
  in print the moving picture is hidden and a still is shown; after each of these the picture
  follows its clock, compared at two rests of the motion's timeline that certainly draw different
  pictures, so that a frozen picture cannot pass.

`DIR` holds, for each motion the site shows, `<decl>.json` (and `<decl>-narrow.json`) with the
animated SVG, the stills of the keys and the poster's PNG beside it: the expectations. A site
writes them with its own few lines of Lean, as the example's `writeMotion` (a `Plane.Motion`) and
`writePanels` (a `Plane.MotionPanels`) do, in
{sourceFile}`verso/example/ExampleTest.lean`, with the library's
`PILeanTest.MotionChecks.expectations` and `PILeanTest.MotionPanelsChecks.expectations`, which
list the rests, the turns and the slides (a slide's actor stays on the straight segment between
its keys, at the eased fraction); a writer that calls them gets what they list by rebuilding.
The files carry the version of their format; expectations written by an older version, or that
list other turns or slides than the motion declares, fail the checks with a message that says so. A
motion shown without its expectations fails the check. With `--workers N` the pages are checked N
at a time.

The checks have been run in Chromium, Firefox and WebKit. A continuous-integration gate runs them
in Chromium. `--engine firefox` runs them in Playwright's Firefox (installed for Playwright
first), where the freeze control (a freeze of Chromium's) and the PDF print (which Playwright
makes in Chromium only) are reported as not applicable. On macOS, `tools/webkit/webkit_check.py
DIR` checks the positions in the system's WebKit, the engine of Safari, from a transparent window
that lets every click through and never takes the focus; it fails when the clock does not run,
and is for a local run, not a Linux gate. A motion with no anchored actor, a morph alone, has no
position to read there or in the site check's free-running reading, which say so; the browser
check below holds it to its stills pixel by pixel.

# The Browser Check
%%%
tag := "motions-browser"
%%%

{sourceFile}`tools/motion-browser-check.py` opens the animated SVG files by themselves, in
headless Chromium, with the clock paused and set, and reads where every actor is. At the middle of
each key's rest every actor is where the key's still has it; at a quarter, a half and three
quarters of each turn the actor is on the turn's circle at the eased fraction of its angle; labels
and markers are not turned; under reduced motion the poster's still is shown and the picture
matches its PNG; turning reduced motion on inside one key's rest and off again for a moment inside a
later key's rest whose picture differs shows the picture of the running clock, and
the check fails when the two moments draw the same picture; the motion plays when it is not
paused; and, for panels, every panel is in phase and nothing leaves its panel while it moves.

The pictures are compared with the stills pixel by pixel, with a rule that allows for what
Chromium does differently when it draws a shape turned into place and the same shape drawn in
place: a pixel is unexplained only when it lies outside the range of the other picture's
neighbouring pixels, widened by 40 levels, and, after a small blur of both pictures, still
differs by more than a fifth of the local contrast. The rule sees a stroke, a label, a dot or a
ring that is moved by 2 pixels or more or is missing. It does not see a difference of less than
about 40 to 50 levels (a fill at 10 percent opacity that is missing or of another colour, a line
of little contrast moved) or most shapes moved by 1 pixel; the anchor checks, at 0.05 px, are the
precise instrument, and they cover the actors' anchors and the upright marks only. The check runs
outside `lake test`, because it needs a browser.

# File Names
%%%
tag := "motions-names"
%%%

A figure's files are named after its declaration, with every character other than an ASCII
letter, a digit, `.`, `_` and `-` written as `_`. Declarations that differ only there, such as
`wordLoop₁` and `wordLoop₂`, would share their files, and the build stops with `two outputs have
the path …`. Name such motions with ASCII digits (`wordLoop1`).
