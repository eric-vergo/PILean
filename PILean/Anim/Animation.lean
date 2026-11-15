/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Anim.Apng
import PILean.Anim.Gif
import PILean.Canvas

/-!
# Animations

One model for every animated output: a drawing as a function of time (`Animation.frame`), with a
frame rate, a duration and a loop setting. Frame `i` shows the drawing at `t = i / fps`, for
`i < frameCount`.

* **Animated PNG and GIF** draw every frame with the rasteriser (`FrameSeq.toApng`,
  `FrameSeq.toGif`, which store only what changes from frame to frame).
* **Animated SVG** uses declarative animation only (SMIL `animate` elements; no script). When
  every frame has the same elements and attributes (only values change), the picture is written
  once and each attribute that changes gets an `animate` with its values over time: the viewer
  interpolates real attributes (path data with the same commands, coordinates, opacities)
  linearly between keyframes, at most `svgKeyframes` of them; values that cannot be interpolated
  change in steps. Otherwise every frame is written as its own group, shown in turn (frame
  switching).
* **Reduced motion.** Every animation has a poster frame (`Animation.poster`, the last frame by
  default), as a still SVG or PNG (`posterSvg`, `posterPng`); the animated SVG contains it too,
  shown instead of the motion when the viewer asks for reduced motion
  (`prefers-reduced-motion: reduce`).

Everything is deterministic: the same animation gives the same bytes.

## Main definitions

* `Animation`, `Animation.frameCount`, `Animation.time`.
* `Animation.toApng`, `Animation.toGif`, `Animation.toSvg`, `posterSvg`, `posterPng`.
* `sameShape`, `mergeFrames`: the test for interpolation and the merged tree.
-/

namespace PILean

open Svg Canvas

/-- An animation: a drawing for each time, its size, frame rate, duration and loops. -/
structure Animation where
  /-- Width in pixels. -/
  width : Nat
  /-- Height in pixels. -/
  height : Nat
  /-- Frames per second. -/
  fps : Nat := 30
  /-- Duration in seconds. -/
  duration : Float := 2
  /-- Plays: `0` repeats forever. -/
  loops : Nat := 0
  /-- The drawing at a time in seconds, `0 ≤ t < duration`. -/
  frame : Float → Shape
  /-- The time of the poster frame (the still shown for reduced motion); the last frame by
  default. -/
  posterTime : Option Float := none
  /-- The background under every frame. -/
  background : Rgba := ⟨255, 255, 255, 255⟩
  /-- The font family of SVG text. -/
  fontFamily : String := "sans-serif"
  /-- The text engine that draws text into raster frames. -/
  text : TextEngine
  /-- The largest number of keyframes an interpolated SVG animation stores. -/
  svgKeyframes : Nat := 30

namespace Animation

variable (a : Animation)

/-- The number of frames: `duration × fps`, rounded, at least 1, at most 10,000. -/
def frameCount : Nat :=
  let n := (a.duration * a.fps.toFloat).round
  if n.isNaN || n < 1 then 1 else min 10000 n.toUInt64.toNat

/-- The time of frame `i`. -/
def time (i : Nat) : Float := i.toFloat / (max a.fps 1).toFloat

/-- The poster frame's time. -/
def poster : Float := a.posterTime.getD (a.time (a.frameCount - 1))

/-- Frame `i` as an RGBA image. -/
def image (i : Nat) : Image :=
  (a.frame (a.time i)).toImage a.width a.height a.text a.background

/-- The frames as a frame sequence for the raster writers. -/
def frameSeq : FrameSeq :=
  { width := a.width, height := a.height,
    frames := (List.range a.frameCount).toArray.map a.image,
    delays := Array.replicate a.frameCount (1, max a.fps 1), loops := a.loops }

/-- The animation as an animated PNG. -/
def toApng : Except Anim.AnimError ByteArray := a.frameSeq.toApng

/-- The animation as a GIF (with Floyd–Steinberg dithering when `dither`). -/
def toGif (dither : Bool := false) : Except Anim.AnimError ByteArray := a.frameSeq.toGif dither

/-- The poster frame as a still SVG document. -/
def posterSvg : String :=
  let bg := Shape.path (rect 0 0 a.width.toFloat a.height.toFloat) (some (.solid a.background))
  (Shape.group #[bg, a.frame a.poster]).toSvg a.width.toFloat a.height.toFloat a.fontFamily

/-- The poster frame as a PNG. -/
def posterPng : Except Png.PngError ByteArray :=
  (a.frame a.poster).toPng a.width a.height a.text a.background

end Animation

/-- Whether two node trees have the same shape: the same elements with the same attribute names
in the same order, and the same text, at most `fuel` deep. -/
def sameShape : Nat → Node → Node → Bool
  | 0, _, _ => false
  | _, .text a, .text b => a == b
  | fuel + 1, .element n as cs, .element m bs ds =>
    n == m && as.size == bs.size && (as.zip bs).all (fun (x, y) => x.1 == y.1) &&
      cs.size == ds.size && (cs.zip ds).all fun (c, d) => sameShape fuel c d
  | _, _, _ => false

/-- The pieces of an attribute value: runs of number characters and the text between them. -/
def valuePieces (v : String) : Array (Bool × String) := Id.run do
  let mut out : Array (Bool × String) := #[]
  let mut cur := ""
  let mut num := false
  for c in v.toList do
    let isNum := c.isDigit || c == '.' || c == '-'
    if cur.isEmpty then cur := String.singleton c; num := isNum
    else if isNum == num && !(isNum && c == '-') then cur := cur.push c
    else out := out.push (num, cur); cur := String.singleton c; num := isNum
  if !cur.isEmpty then out := out.push (num, cur)
  return out

/-- Whether values can be interpolated: the same text between their numbers, and as many
numbers (path data with the same commands, coordinate lists of one length, single numbers). -/
def interpolable (vs : Array String) : Bool :=
  match vs[0]? with
  | none => false
  | some v0 =>
    let p0 := valuePieces v0
    p0.any (·.1) && vs.all fun v =>
      let p := valuePieces v
      p.size == p0.size && (p.zip p0).all fun (x, y) => x.1 == y.1 && (x.1 || x.2 == y.2)

/-- Whether every attribute that changes across the frames (all of the same shape) can be
interpolated, at most `fuel` deep. -/
def framesInterpolable : Nat → Array Node → Bool
  | 0, _ => false
  | fuel + 1, frames =>
    match frames[0]? with
    | some (Node.element _ attrs children) =>
      (List.range attrs.size).all (fun k =>
        let vs := frames.map fun f => match f with
          | .element _ as _ => ((as[k]?).map (·.2)).getD ""
          | .text _ => ""
        vs.all (· == (vs[0]?.getD "")) || interpolable vs) &&
      (List.range children.size).all fun j =>
        framesInterpolable fuel (frames.map fun f => match f with
          | .element _ _ cs => (cs[j]?).getD (.text "")
          | t => t)
    | _ => true

/-- One tree whose changing attributes are animated, from the trees of the keyframes (all of the
same shape) shown at `keyTimes` over `dur` seconds; `reps` is SMIL's `repeatCount`. -/
def mergeFrames (fuel : Nat) (frames : Array Node) (keyTimes : String) (dur : String)
    (reps : String) : Node :=
  match fuel, frames[0]? with
  | 0, _ => .text ""
  | _, none => .text ""
  | _, some (Node.text t) => .text t
  | fuel + 1, some (Node.element name attrs children) => Id.run do
    let mut anims : Array Node := #[]
    let mut fixed : Array (String × String) := #[]
    for h : k in [0:attrs.size] do
      let (key, v0) := attrs[k]
      let vs := frames.map fun f => match f with
        | .element _ as _ => ((as[k]?).map (·.2)).getD v0
        | .text _ => v0
      if vs.all (· == v0) then fixed := fixed.push (key, v0)
      else
        fixed := fixed.push (key, v0)
        let mode := if interpolable vs then "linear" else "discrete"
        anims := anims.push (el "animate" #[("attributeName", key),
          ("values", ";".intercalate vs.toList), ("keyTimes", keyTimes), ("dur", dur),
          ("calcMode", mode), ("repeatCount", reps), ("fill", "freeze")])
    let kids := (List.range children.size).toArray.map fun j =>
      mergeFrames fuel (frames.map fun f => match f with
        | .element _ _ cs => (cs[j]?).getD (.text "")
        | t => t) keyTimes dur reps
    return .element name fixed (anims ++ kids)

/-- The ids of a frame's definitions and the references to them renamed with a prefix, so that
frames written side by side do not collide. -/
def prefixIds (pre : String) : Nat → Node → Node
  | 0, n => n
  | _, .text t => .text t
  | fuel + 1, .element name attrs children =>
    let attrs := attrs.map fun (k, v) =>
      if k == "id" then (k, pre ++ v)
      else if v.startsWith "url(#" then (k, "url(#" ++ pre ++ (v.drop 5).toString)
      else (k, v)
    .element name attrs (children.map (prefixIds pre fuel))

namespace Animation

variable (a : Animation)

/-- The style element that shows the poster instead of the motion under reduced motion. -/
def reducedMotionStyle : Node :=
  el "style" #[] #[.text (".poster{display:none}@media (prefers-reduced-motion: reduce)" ++
    "{.poster{display:inline}.motion{display:none}}")]

/-- The animation as an animated SVG document (see the module docstring). -/
def toSvg : String := Id.run do
  let n := a.frameCount
  let w := a.width.toFloat
  let h := a.height.toFloat
  let mode := TextMode.native a.fontFamily
  let trees := (List.range n).toArray.map fun i => el "g" #[] (a.frame (a.time i) |>.render mode)
  let durS := n.toFloat / (max a.fps 1).toFloat
  let dur := fmtNum durS 4 ++ "s"
  let reps := if a.loops == 0 then "indefinite" else toString a.loops
  let first := (trees[0]?).getD (.text "")
  let uniform := trees.all (sameShape 256 first)
  let motion := if uniform && n > 1 then
      -- keyframes: when everything that changes can be interpolated, at most `svgKeyframes`
      -- evenly spaced ones, else every frame; then the end of the cycle (the first frame again
      -- when looping, so that the loop closes smoothly)
      let k := if framesInterpolable 256 trees then max 2 (min a.svgKeyframes n) else n
      let idx := (List.range k).toArray.map fun j => j * n / k
      let keys := idx.map fun i => (trees[i]?).getD first
      let keys := keys.push (if a.loops == 0 then first else (trees.back?).getD first)
      let times := (List.range (k + 1)).toArray.map fun j =>
        if j == k then "1" else fmtNum (((idx[j]?).getD 0).toFloat / n.toFloat) 4
      mergeFrames 256 keys (";".intercalate times.toList) dur reps
    else
      -- frame switching: frame `i` visible from `i / n` to `(i + 1) / n` of the cycle
      el "g" #[] <| (List.range n).toArray.map fun i =>
        let tree := prefixIds s!"f{i}-" 256 ((trees[i]?).getD first)
        let t0 := fmtNum (i.toFloat / n.toFloat) 4
        let t1 := fmtNum ((i + 1).toFloat / n.toFloat) 4
        let (values, times) :=
          if i == 0 then ("visible;hidden", s!"0;{t1}")
          else if i + 1 == n then ("hidden;visible", s!"0;{t0}")
          else ("hidden;visible;hidden", s!"0;{t0};{t1}")
        let vis := if i == 0 then "visible" else "hidden"
        el "g" #[("visibility", vis)] (#[el "animate" #[("attributeName", "visibility"),
          ("values", values), ("keyTimes", times), ("dur", dur), ("calcMode", "discrete"),
          ("repeatCount", reps), ("fill", "freeze")], tree])
  let bg := rect 0 0 w h (some a.background)
  let poster := prefixIds "poster-" 256
    (el "g" #[("class", "poster")] (a.frame a.poster |>.render mode))
  return document w h #[reducedMotionStyle, bg, el "g" #[("class", "motion")] #[motion], poster]

end Animation

end PILean
