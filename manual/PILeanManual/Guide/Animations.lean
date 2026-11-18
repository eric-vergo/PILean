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

#doc (Manual) "Animations" =>
%%%
tag := "animations"
%%%

```lean -show
namespace PILeanManual.Animations
open PILean PILean.Plot
```

An {name}`PILean.Animation` is a drawing as a function of time: a size, a frame rate, a duration,
a loop count (0 loops forever), the function `frame : Float → Canvas.Shape`, a background and the
text engine and font family of its text. Frame `i` shows the drawing at the time `i / fps`, for
`i < frameCount`; {name}`PILean.Animation.exactTime` is that time as a rational number and
{name}`PILean.Animation.time` its conversion to `Float`, which is what the drawing function is
given.

```lean
/-- A dot going round a circle, with a trail of the angle swept so far. -/
def orbitFrame (st : Style) (t : Float) : Canvas.Shape :=
  let a := 6.283185307179586 * t / 2
  let c : Point := ⟨120 + 70 * a.sin, 90 - 70 * a.cos⟩
  .group #[
    .path (Canvas.rect 0 0 240 180) (some (.solid st.background)),
    .path (Canvas.circle ⟨120, 90⟩ 70) none (some { ink := st.grid, width := 2 }),
    .path (Path.empty.moveTo ⟨120, 90⟩ |>.lineTo c) none
      (some { ink := st.inkMuted, width := 1.5, dash := #[4, 3] }),
    .path (Canvas.circle c 10) (some (.solid st.palette[0]!))]

/-- One turn in two seconds, at 12 frames a second, looping. -/
@[figure]
def orbit : Animation :=
  { width := 240, height := 180, fps := 12, duration := 2, frame := orbitFrame Style.light,
    text := Style.light.text, fontFamily := Style.light.fontFamily }
```

```lean (name := animEx)
#eval orbit.frameCount
#eval (orbit.exactTime 3, orbit.time 3)
#eval orbit.toSvg.length
```

```leanResult animEx
```

# Outputs
%%%
tag := "anim-outputs"
%%%

One animation is written in three formats and a still:

* *Animated SVG* ({name}`PILean.Animation.toSvg`), declarative only: SMIL `animate` elements, no
  script. When every frame has the same elements and attribute names, the picture is written once
  and each attribute that changes is animated between at most `svgKeyframes` (30) keyframes,
  linearly where the values have the same text between their numbers (path data with the same
  commands, coordinates, opacities) and in steps otherwise; when the frames' structure differs,
  each frame is a group of its own, shown in turn.
* *Animated PNG* ({name}`PILean.Animation.toApng`) and *GIF* ({name}`PILean.Animation.toGif`,
  optionally dithered) draw every frame with the rasteriser into a
  {name}`PILean.FrameSeq` and store only what changes from frame to frame (the changed
  rectangle; equal frames are merged). APNG delays are exact fractions; GIF delays are in
  centiseconds, kept exact in their sum; a GIF has one palette, by median cut, or the exact colours
  when there are at most 256.
* A *poster frame* ({name}`PILean.Animation.posterSvg`, {name}`PILean.Animation.posterPng`), the
  last frame unless `posterTime` says otherwise. The animated SVG contains it too and shows it
  instead of the motion when the viewer asks for reduced motion (`prefers-reduced-motion:
  reduce`).

The same bytes come out on every run. The animated SVG:

:::figure PILeanManual.Animations.orbit (alt := "A dot going round a circle once every two seconds, joined to the centre by a dashed line.") (width := "240px")
:::

and the GIF of the same animation, drawn by PILean's rasteriser:

:::figure PILeanManual.Animations.orbit (alt := "The same dot going round a circle, as a GIF.") (format := "gif") (width := "240px")
:::

A plot can be animated through its drawing: `frame := fun t => (fig t).draw` for a function `fig`
from time to {name}`PILean.Plot.Figure`. Keeping the sampling fixed from frame to frame keeps the
path commands equal, so the SVG interpolates instead of switching frames:

```lean
/-- The bars of a small chart growing to their values with an ease-out. -/
def growing (t : Float) : Figure :=
  let p := min 1 (t / 1.2)
  let k := 0.02 + 0.98 * (1 - (1 - p) ^ 3)
  { title := "Growing bars", width := 360, height := 240, legend := false,
    panels := #[{
      y := { label := "count", domain := some (0, 20) },
      series := #[.bars #["Mon", "Tue", "Wed", "Thu", "Fri"]
        #[("north", #[12, 15, 9, 17, 14].map (· * k))]] }] }

/-- The growing bars, played once and held. -/
@[figure]
def growingBars : Animation :=
  { width := 360, height := 240, fps := 10, duration := 1.6, loops := 1,
    frame := fun t => (growing t).draw, text := Style.light.text,
    fontFamily := Style.light.fontFamily }
```

:::figure PILeanManual.Animations.growingBars (alt := "Five bars for Monday to Friday growing from the baseline to 12, 15, 9, 17 and 14 in a little over a second, then holding.") (width := "360px")
:::

# What Is Proved
%%%
tag := "anim-proved"
%%%

Frame `i` is the drawing at the exact time `i / fps`: {name}`PILean.Animation.exactTime_eq` and
{name}`PILean.Animation.time_eq_exactTime` say what the time is, and
{name}`PILean.Animation.frameSeq_getElem` and {name}`PILean.Animation.frameTrees_getElem` that
frame `i` of the raster frames (animated PNG, GIF) and of the animated SVG is the drawing at that
time. Nothing is proved about the drawing function itself or about the number of frames:
{name}`PILean.Animation.frameCount` rounds the duration times the frame rate as floating-point
numbers, which is tested. The encoders are tested, not proved: the gallery's animations are read
back by PILean's readers and opened by macOS's ImageIO, and their animated SVGs are checked in a
headless browser ({ref "raster-anim-read"}[]).
