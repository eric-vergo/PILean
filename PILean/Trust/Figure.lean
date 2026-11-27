/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plot.Figure
import PILean.Plane
import PILean.Explorer
import PILean.Graph.Draw
import PILean.Anim.Animation
import PILean.Diagram.Basic
import PILean.Pdf.Figures
import PILean.Raster.DomainColouring
import PILean.Trust.Provenance

/-!
# Renderable figures

`ToOutputs α` says how a value of `α` becomes image files: a list of `Output`s, each with a file
name suffix, a format, the bytes (computed on demand) and the *specification encoding*, the bytes
a fingerprint covers (see `docs/TRUST.md`).

The specification of an output is the SVG document PILean's deterministic writer makes from the
drawing, before any source information is added: for a figure, a graph and an animation the SVG
output, the animation's APNG and GIF (the SVG of all frames) and its poster (the SVG of the poster
frame); for a PNG and a PDF the SVG with text as shapes, which is the drawing the PNG is
rasterised from and the PDF is written from.
It covers the values a function takes where the figure samples it, not the function's code.

## Main definitions

* `Format`, `Output`, `ToOutputs`
* `Standing`: whether a theorem is linked to a figure or the figure is an illustration
* `InlineSvg`, `FrameSet`: pictures and families of frames a web page puts inline
* `MotionStepRow`, `MotionMoveRow`, `MotionData`, `motionLinkedWords`: what a page needs to show
  a motion (its record, `MotionSummary`, is in `PILean.Trust.Provenance`; its outputs in
  `PILean.Trust.Motion`)
* instances for `Plot.Figure`, `Plane.Figure`, `Explorer`, `Graph`, `GraphFigure`,
  `Animation`, `Diagram.Diagram` and `DomainColouring`
-/

namespace PILean.Trust

/-- The format of an output file. -/
inductive Format where
  /-- A Scalable Vector Graphics document. -/
  | svg
  /-- A PNG image. -/
  | png
  /-- An animated PNG. -/
  | apng
  /-- A GIF animation. -/
  | gif
  /-- A one-page PDF document (`PILean.Pdf`). -/
  | pdf
deriving BEq, Repr, Inhabited

/-- The format's name, as written in a manifest: `svg`, `png`, `apng`, `gif` or `pdf`. -/
def Format.name : Format → String
  | .svg => "svg"
  | .png => "png"
  | .apng => "apng"
  | .gif => "gif"
  | .pdf => "pdf"

/-- The extension of the files of a format (without the dot): an animated PNG is a `png` file. -/
def Format.ext : Format → String
  | .svg => "svg"
  | .png => "png"
  | .apng => "png"
  | .gif => "gif"
  | .pdf => "pdf"

/-- The format with a given name, if there is one. -/
def Format.ofName? : String → Option Format
  | "svg" => some .svg
  | "png" => some .png
  | "apng" => some .apng
  | "gif" => some .gif
  | "pdf" => some .pdf
  | _ => none

/-- How a figure stands with respect to the object it shows. A figure is `linked` when at least
one theorem is linked to it by `figure_links` and passed that command's rule
(`PILean.Trust.figureTheoremProblem?`: the theorem is proved from the standard axioms and its
statement names the figure) in the environment where the build's table of figures (`figures%`)
was elaborated; otherwise it is an `illustration`, openly marked as one by
`@[figure illustration]` or not. The standing says that such a theorem exists, not what it
states: what a linked theorem says is in its statement, which is its reader's to judge
(`docs/PROOFS.md`). -/
inductive Standing where
  /-- The theorems linked to the figure by `figure_links`, by full name, each of which passed
  the rule when the table of figures was elaborated; never empty for a figure `figures%` makes. -/
  | linked (theorems : Array String)
  /-- No theorem is linked to the figure; `marked` says whether its declaration says so with
  `@[figure illustration]`. -/
  | illustration (marked : Bool)
deriving BEq, Repr, Inhabited

/-- The standing's word, as source records and manifests write it: `linked` or `illustration`. -/
def Standing.word : Standing → String
  | .linked _ => "linked"
  | .illustration _ => "illustration"

/-- The theorems of a linked standing, by full name; empty for an illustration. -/
def Standing.theorems : Standing → Array String
  | .linked ts => ts
  | .illustration _ => #[]

/-- Whether the standing is an illustration that its declaration does not mark as one: a figure
`pilean-build --require-standing` refuses. -/
def Standing.unmarked : Standing → Bool
  | .illustration false => true
  | _ => false

/-- A picture a web page can put inline (as an `svg` element) instead of a file: its size in pixels
and the SVG nodes of its body, as `Svg.document` writes them. -/
structure InlineSvg where
  /-- The width in pixels. -/
  width : Float
  /-- The height in pixels. -/
  height : Float
  /-- The nodes of the document's body. -/
  nodes : Array Svg.Node
  /-- The light colours (`#rrggbb`) of the picture paired with those of its dark twin, for a page
  that restyles it in its dark theme (`Style.darkColourPairs`); empty without a twin. -/
  darkColours : Array (String × String) := #[]
  /-- The fill opacities (as written) of the picture's tints paired with the dark twin's. -/
  darkOpacities : Array (String × String) := #[]
  deriving Inhabited

/-- The fill opacity attribute a tint of opacity `a` gets (`Svg.paint` of an opaque colour at
that alpha). -/
def tintOpacityText (a : Float) : String :=
  fmtNum ((max 0 (min 1 a) * 255).round / 255) 3

/-- The restyling of an inline picture in the dark theme of a page, for a picture in the style
`st`: its light colours paired with its dark twin's (`Style.darkColourPairs`) and its tint
opacity paired with the twin's when they differ; both empty without a twin. -/
def InlineSvg.themeOf (st : Style) : Array (String × String) × Array (String × String) :=
  (st.darkColourPairs, match st.darkTwin? with
    | some d =>
      if st.plane.fillOpacity == d.plane.fillOpacity then #[]
      else #[(tintOpacityText st.plane.fillOpacity, tintOpacityText d.plane.fillOpacity)]
    | none => #[])

/-- An inline picture in a style: its nodes, and its dark colours and tint opacities when the
style has a dark twin (`InlineSvg.themeOf`). -/
def InlineSvg.ofStyle (w h : Float) (nodes : Array Svg.Node) (st : Style) : InlineSvg :=
  let (darkColours, darkOpacities) := InlineSvg.themeOf st
  { width := w, height := h, nodes, darkColours, darkOpacities }

/-- The SVG document of an inline picture. -/
def InlineSvg.document (i : InlineSvg) : String := Svg.document i.width i.height i.nodes

/-- The inline frames of an `Explorer` for a web page: the axis, the steps, the frames
(axis-major, as in `Explorer`) and the poster's position. -/
structure FrameSet where
  /-- The name of the parameter axis; empty for none. -/
  axisName : String := ""
  /-- The labels of the axis's values. -/
  axisValues : Array String := #[]
  /-- The captions of the steps (or the labels of the values of the parameter `stepName`). -/
  stepCaptions : Array String := #[]
  /-- The name of the parameter whose values the steps are; empty for steps with captions. -/
  stepName : String := ""
  /-- The frames. -/
  frames : Array InlineSvg
  /-- The poster's position in `frames`. -/
  poster : Nat := 0
  deriving Inhabited

/-- One move of a step of a motion, as a figure page lists it: what the motion declares, and what
the animation draws for it (`drawn`). -/
structure MotionMoveRow where
  /-- The panel of a picture of several panels the actor belongs to; empty for one motion. -/
  panel : String := ""
  /-- The actor's id. -/
  actor : String
  /-- The kind of move declared: `turn`, `slide`, `appearance`, `disappearance` or `morph`. -/
  kind : String
  /-- For a turn: its centre, in the figure's (world) coordinates. -/
  centre : Option Point := none
  /-- For a turn: the exact fraction of a full turn, counterclockwise. -/
  turns : Option Rat := none
  /-- For a slide: its vector, in the figure's (world) coordinates. -/
  vector : Option Point := none
  /-- What the animation draws for the move: `kind` when it is drawn as declared, `crossfade` when
  the declared move does not carry the actor onto the next key and the two drawings crossfade
  instead (possible only under the check levels `warn` and `ignore`). -/
  drawn : String := ""
  /-- For an appearance or a disappearance in part of its step or during a rest: where it starts
  and ends, in seconds from the start of the step or of the rest. -/
  window : Option (Rat × Rat) := none
  deriving Inhabited

/-- A point of the figure's coordinates as a page writes it: `(x, y)`, at most four decimals. -/
def pointWords (p : Point) : String := s!"({fmtNum p.x 4}, {fmtNum p.y 4})"

/-- A fraction of a full turn as degrees, exactly: `90°`, or `360/7°` when not whole. -/
def turnDegreesWords (q : Rat) : String :=
  let d := 360 * q
  if d.den == 1 then s!"{d.num}°" else s!"{d.num}/{d.den}°"

/-- A time in seconds as a page writes it, exactly: `1 s`, `3/10 s`. -/
def secondsWords (t : Rat) : String :=
  if t.den == 1 then s!"{t.num} s" else s!"{t.num}/{t.den} s"

/-- Whether the move is drawn as it is declared. -/
def MotionMoveRow.asDeclared (r : MotionMoveRow) : Bool := r.drawn.isEmpty || r.drawn == r.kind

/-- The move in words, for a page: `turn about (0, 0) by 1/4 of a full turn (90°)`,
`slide by (1, 0)`, or the kind alone; followed by `, drawn as a crossfade (the move does not land
on the next key)` when the animation does not draw it as declared. -/
def MotionMoveRow.words (r : MotionMoveRow) : String :=
  let declared := match r.kind, r.centre, r.turns, r.vector with
    | "turn", some c, some q, _ =>
      s!"turn about {pointWords c} by {q} of a full turn ({turnDegreesWords q})"
    | "slide", _, _, some v => s!"slide by {pointWords v}"
    | k, _, _, _ => k
  let declared := match r.window with
    | some (a, b) => s!"{declared} from {secondsWords a} to {secondsWords b}"
    | none => declared
  if r.asDeclared then declared
  else s!"{declared}, drawn as a {r.drawn} (the move does not land on the next key)"

/-- The rest on a key of a motion, as a figure page lists it: the key, how long the rest lasts,
whether the key is a still, and the actors that appear or vanish during it, with their windows. -/
structure MotionRestRow where
  /-- The key. -/
  key : Nat
  /-- How long the rest lasts, in seconds. -/
  duration : Rat
  /-- Whether the key is a still. -/
  still : Bool := true
  /-- The fades during the rest, in the order the key declares them. -/
  fades : Array MotionMoveRow := #[]
  deriving Inhabited

/-- One step of a motion, from key `step` to key `step + 1`, as a figure page lists it. -/
structure MotionStepRow where
  /-- The step's number, from `0`: it goes from key `step` to key `step + 1`. -/
  step : Nat
  /-- How long the step takes, in seconds. -/
  duration : Rat
  /-- Whether nothing moves in the step (it takes its time). -/
  idle : Bool := false
  /-- The moves of its actors, in the order the motion declares them. -/
  moves : Array MotionMoveRow := #[]
  deriving Inhabited

/-- What a page needs to show a motion inline: its record, the moving picture without what the
standalone file adds for itself, the key stills with their captions, the table of its steps, and
whether items change between keys without a declared move.

`live` is the body of the animated SVG file without its `title`, `desc`, its `style` element (the
reduced-motion rule) and its poster group: the background (and the panels' titles) and the group
of class `pilean-motion-live` that holds every animation. The file's root holds, in order, the
title and the description (when the motion has them), that `style` element, the nodes of `live`,
and the poster group; so a site check can rebuild the file from `live` and compare. `stills`
holds the still of every key that is one (the picture of the output `-key-k`, `k` the key, which
`stillKeys` gives for each frame) with their captions (`stepCaptions`) and the poster's position
among them (`poster`, always among the frames).

A page must say so when `MotionData.unchecked` holds (`MotionData.checkWords`). -/
structure MotionData where
  /-- The record of the motion: keys, cycle, captions, check level, errors left. -/
  summary : MotionSummary
  /-- The moving picture, for a page that puts it inline (with the theme's colour pairs). -/
  live : InlineSvg
  /-- The key stills with their captions. -/
  stills : FrameSet
  /-- The steps, in order. -/
  steps : Array MotionStepRow
  /-- Whether items change between two keys without a declared move, and crossfade. -/
  crossfades : Bool := false
  /-- The key of each still of `stills`, in order (the `k` of its files `-key-k`). -/
  stillKeys : Array Nat := #[]
  /-- The rest on every key, in order. -/
  rests : Array MotionRestRow := #[]
  deriving Inhabited

/-- Whether the motion was not checked strictly: built at the check level `warn` or `ignore`
(`MotionSummary.strict`). A page must say so (`MotionData.checkWords`). -/
def MotionData.unchecked (d : MotionData) : Bool := !d.summary.strict

/-- `a`, `a and b`, `a, b and c`. -/
def listWords : List String → String
  | [] => ""
  | [a] => a
  | [a, b] => a ++ " and " ++ b
  | a :: rest => a ++ ", " ++ listWords rest

/-- What the browser does between key frames, from the moves the animation draws: turns, slides,
fades, changes of outline, crossfades of items whose declared move does not land, and crossfades
of items that change without a declared move. -/
def MotionData.betweenWords (d : MotionData) : String :=
  let drawn := d.steps.flatMap (·.moves.map fun r => if r.asDeclared then r.kind else r.drawn)
  let parts :=
    (if drawn.contains "turn" then ["turns drawn items about the stated centres"] else []) ++
    (if drawn.contains "slide" then ["slides drawn items along the stated vectors"] else []) ++
    (if drawn.contains "appearance" || drawn.contains "disappearance" then
      ["fades items in or out"] else []) ++
    (if drawn.contains "morph" then ["changes the outlines of drawn items"] else []) ++
    (if drawn.contains "crossfade" then
      ["crossfades items whose declared move does not land on the next key frame"] else []) ++
    (if d.crossfades then ["crossfades items that change without a declared move"] else [])
  if parts.isEmpty then "Nothing moves between the key frames."
  else s!"Between key frames the browser {listWords parts}."

/-- What a page says when the motion is `unchecked`; none otherwise: the level it was built at,
and how many problems the strict level (`fail`) treats as errors were left, or that the strict
level finds none. -/
def MotionData.checkWords (d : MotionData) : Option String :=
  let n := d.summary.errorsLeft
  if d.summary.strict then none
  else if n == 0 then
    some s!"It was built at the check level {d.summary.checks}, which does not stop a motion \
      whose moves miss its key frames; the strict level finds no error in it."
  else
    some s!"It was built at the check level {d.summary.checks}: {n} problem\
      {if n == 1 then "" else "s"} that the strict level treats as errors did not stop it, and \
      between some key frames the animation is not what the steps declare."

/-- What a figure page says of a motion besides its standing: the number of key frames and what
the stills are (`the key figures as drawn`; a claim that their data is exact belongs to the
figure's own description), what the browser does between them (`betweenWords`), and
`checkWords` when the motion is unchecked. -/
def MotionData.words (d : MotionData) : String :=
  let n := d.summary.keys
  let shown := match d.summary.stills with
    | some ks => if ks.size == 1 then ", 1 of them shown as a still"
      else s!", {ks.size} of them shown as stills"
    | none => ""
  " ".intercalate ([s!"An animation drawn from {n} key frame{if n == 1 then "" else "s"}{shown}; \
    the stills are the key figures as drawn.", d.betweenWords] ++ d.checkWords.toList)

/-- What a figure page says of a theorem linked to a motion: what such a theorem can state. -/
def motionLinkedWords : String :=
  "A theorem about a motion can state its key figures and its declared moves (the actors, the \
    centres and fractions of the turns, the vectors of the slides); the frames the browser draws \
    between the key frames are not part of any statement."

/-- One file a figure is rendered to. -/
structure Output where
  /-- The suffix of the file's stem, for instance `""`, `"-dark"` or `"-poster"`. -/
  name : String
  /-- The file's format. -/
  format : Format
  /-- The file's bytes, without source information; an error message if it cannot be made. -/
  bytes : Unit → Except String ByteArray
  /-- The canonical encoding of what is drawn, which the fingerprint covers. -/
  spec : ByteArray
  /-- The identity of the text engine the output is drawn with (`TextEngine.id`), which the
  fingerprint covers through `rendererWith`; empty for the built-in lettering. -/
  textEngine : String := ""
  /-- For an SVG output: the same picture as nodes, for a page that puts it inline. -/
  inline : Unit → Option InlineSvg := fun _ => none
  /-- For an SVG output a page can put inline: the restyling of its dark theme, the
  `darkColours` and `darkOpacities` of `inline` (`InlineSvg.themeOf` of its style), which the
  manifest records so that a site check can tie the page's theme rules to it. -/
  theme : Unit → Array (String × String) × Array (String × String) := fun _ => (#[], #[])
  /-- For the poster of a family of frames: every frame, for a page that shows them inline. -/
  frames : Unit → Option FrameSet := fun _ => none
  /-- Problems of the figure's layout a build should report as warnings (on one output of a
  figure, so that they are reported once). -/
  problems : Unit → Array String := fun _ => #[]
  /-- For every output of a motion: what the manifest records about the motion
  (`MotionSummary`); none for other figures. -/
  motion : Unit → Option MotionSummary := fun _ => none
  /-- For the animated SVG of a motion (and of its narrow rendition): what a page needs to show
  the motion inline (`MotionData`). -/
  motionPage : Unit → Option MotionData := fun _ => none
  /-- The standing of the figure the output belongs to. `ToOutputs` instances leave it at an
  unmarked illustration; `figures%` sets it on every output of a figure from the links
  `figure_links` recorded and the figure's `@[figure illustration]` marking. -/
  standing : Standing := .illustration false

/-- An empty SVG output that cannot be rendered (for indexing arrays of outputs). -/
instance : Inhabited Output :=
  ⟨{ name := "", format := .svg, bytes := fun _ => .error "no output", spec := .empty }⟩

/-- The outputs with the standing `s` set on each (`figures%` applies it to a figure's outputs). -/
def withStanding (s : Standing) (os : Array Output) : Array Output :=
  os.map ({ · with standing := s })

/-- Values that PILean can render to files. -/
class ToOutputs (α : Type) where
  /-- The files a value is rendered to, in a fixed order. -/
  outputs : α → Array Output

/-- The bytes of an output, or the problems as an error when `fail` and there are some. -/
def checkedBytes (fail : Bool) (problems : Unit → Array String)
    (bytes : Unit → Except String ByteArray) : Except String ByteArray :=
  let ps := if fail then problems () else #[]
  if ps.isEmpty then bytes () else .error ("problems: " ++ "; ".intercalate ps.toList)

/-- Figures: the SVG (with the problems of its checks, `PILean.Plot.Check`, which the figure's
`checks` level reports as warnings), the PNG when the figure has pixels, and the PDF. A figure
whose `checks` level is `fail` and that has such problems cannot be rendered. -/
instance : ToOutputs Plot.Figure where
  outputs fig :=
    let ok := checkedBytes (fig.checks == .fail) fun _ => fig.checkMessages
    #[{ name := "", format := .svg, bytes := fun _ => ok fun _ => .ok fig.toSvg.toUTF8,
        spec := fig.toSvg.toUTF8, textEngine := fig.style.text.id,
        inline := fun _ => some (InlineSvg.ofStyle fig.width fig.height
          (fig.draw.render (.forSvg fig.style.text fig.style.fontFamily)) fig.style),
        theme := fun _ => InlineSvg.themeOf fig.style,
        problems := fun _ => if fig.checks == .warn then fig.checkMessages else #[] },
      { name := "", format := .png,
        bytes := fun _ => ok fun _ => match fig.toPng with
          | some b => .ok b
          | none => .error "the figure has no pixels",
        spec := (fig.toSvg (outlines := true)).toUTF8, textEngine := fig.style.text.id },
      { name := "", format := .pdf, bytes := fun _ => ok fun _ => .ok fig.toPdf,
        spec := (fig.toSvg (outlines := true)).toUTF8, textEngine := fig.style.text.id }]

/-- The bytes of a plane figure's output, or the figure's layout problems as an error when its
`checks` level is `fail` and it has some. -/
def planeBytes (fig : Plane.Figure) (bytes : Unit → Except String ByteArray) :
    Except String ByteArray :=
  checkedBytes (fig.checks == .fail) (fun _ => fig.checkMessages) bytes

/-- The plane figure as a picture a page puts inline: its SVG nodes (its `auto` labels placed) at
its page size, with the theme of its style. -/
def _root_.PILean.Plane.Figure.inline (fig : Plane.Figure) : InlineSvg :=
  let g := fig.autoPlaced
  InlineSvg.ofStyle g.frame.width.round g.frame.height.round fig.svgNodes fig.style

/-- The SVG and PNG outputs of one plane figure, named with `suffix`, and its PDF when `pdf`;
the SVG carries the figure's layout warnings when `warn`. -/
def planeOutputs (fig : Plane.Figure) (suffix : String) (warn : Bool) (pdf : Bool := true) :
    Array Output :=
  #[{ name := suffix, format := .svg,
      bytes := fun _ => planeBytes fig fun _ => .ok fig.toSvg.toUTF8,
      spec := fig.toSvg.toUTF8, textEngine := fig.style.text.id,
      inline := fun _ => some fig.inline,
      theme := fun _ => InlineSvg.themeOf fig.style,
      problems := fun _ => if warn && fig.checks == .warn then fig.checkMessages else #[] },
    { name := suffix, format := .png,
      bytes := fun _ => planeBytes fig fun _ => match fig.toPng with
        | some b => .ok b
        | none => .error "the figure has no pixels",
      spec := (fig.toSvg (outlines := true)).toUTF8, textEngine := fig.style.text.id }] ++
    if pdf then
      #[{ name := suffix, format := .pdf, bytes := fun _ => planeBytes fig fun _ => .ok fig.toPdf,
          spec := (fig.toSvg (outlines := true)).toUTF8, textEngine := fig.style.text.id }]
    else #[]

/-- Plane figures: the SVG (with the layout problems the figure's `checks` level reports as
warnings), the PNG and the PDF, and the SVG and PNG at the narrow width (suffix `-narrow`) when the
figure has one (a rendition for small screens, which a paper does not need). A figure whose
`checks` level is `fail` and that has layout problems cannot be rendered. -/
instance : ToOutputs Plane.Figure where
  outputs fig :=
    planeOutputs fig "" true ++ match fig.narrow with
      | some n => planeOutputs n "-narrow" true (pdf := false)
      | none => #[]

/-- An explorer frame for a page. -/
def _root_.PILean.ExplorerFrame.inline (f : ExplorerFrame) : InlineSvg :=
  InlineSvg.ofStyle f.width f.height f.svgNodes f.style

/-- Families of frames: the poster's SVG (carrying every frame for a page that shows them
inline, and the frames' problems as warnings, `Explorer.problems`), PNG and PDF, then each frame `k`
as an SVG of its own named `-frame-k` (`k` from 0, in the order of `Explorer.frames`), so that
every picture a page shows inline is a file with its fingerprint and its manifest entry. An
explorer that is not well formed (`Explorer.valid`: a frame for every point, at most
`Explorer.maxFrames`) cannot be rendered, nor one whose frames' SVG together is over
`Explorer.maxBytes` bytes (checked on the poster's SVG, which carries them all), nor one with a
frame whose checks level is `fail` and that has problems (`Explorer.problemsFail`). -/
instance : ToOutputs Explorer where
  outputs x :=
    let p := x.posterFrame
    let ok := fun (b : Unit → Except String ByteArray) =>
      if !x.valid then .error s!"the explorer has {x.frames.size} frames for \
        {x.values} values and {x.steps} steps (at most {Explorer.maxFrames}), or its poster \
        {x.poster} is not among them"
      else checkedBytes x.problemsFail (fun _ => x.problems) b
    let okAll := fun (b : Unit → Except String ByteArray) => ok fun _ =>
      let n := x.svgBytes
      if n > Explorer.maxBytes then
        .error s!"the frames' SVG takes {n} bytes, more than {Explorer.maxBytes}"
      else b ()
    let frameOutputs := x.frames.zipIdx.map fun (f, k) =>
      ({ name := s!"-frame-{k}", format := .svg, bytes := fun _ => ok fun _ => .ok f.toSvg.toUTF8,
         spec := f.toSvg.toUTF8, textEngine := f.style.text.id,
         inline := fun _ => some f.inline, theme := fun _ => InlineSvg.themeOf f.style } :
        Output)
    #[{ name := "", format := .svg, bytes := fun _ => okAll fun _ => .ok p.toSvg.toUTF8,
        spec := p.toSvg.toUTF8, textEngine := p.style.text.id,
        inline := fun _ => some p.inline, theme := fun _ => InlineSvg.themeOf p.style,
        frames := fun _ => some
          { axisName := x.axisName, axisValues := x.axisValues,
            stepCaptions := x.stepCaptions, stepName := x.stepName,
            frames := x.frames.map (·.inline), poster := x.poster },
        problems := fun _ => if x.problemsFail then #[] else x.problems },
      { name := "", format := .png,
        bytes := fun _ => ok fun _ => match p.toPng with
          | some b => .ok b
          | none => .error "the poster has no pixels",
        spec := (p.toSvg (outlines := true)).toUTF8, textEngine := p.style.text.id },
      { name := "", format := .pdf, bytes := fun _ => ok fun _ => .ok p.toPdf,
        spec := (p.toSvg (outlines := true)).toUTF8, textEngine := p.style.text.id }] ++
      frameOutputs

/-- Diagrams: the outputs of their plane figure (`Diagram.toPlane`), so the SVG, PNG and PDF, and
at a narrow width the SVG and PNG with the suffix `-narrow`. -/
instance : ToOutputs Diagram.Diagram where
  outputs d := ToOutputs.outputs d.toPlane

/-- Domain colourings (`PILean.DomainColouring`, a raster picture computed in floating point, an
illustration): the PNG and a PDF that embeds it (`Pdf.ofImage`); no SVG. The specification is the
picture's size and its samples, so the fingerprint covers every pixel. -/
instance : ToOutputs DomainColouring where
  outputs d :=
    let im := d.toImage
    let spec := match im with
      | some i => s!"domain colouring {i.width} {i.height}\n".toUTF8 ++ i.data
      | none => .empty
    let none' : Except String ByteArray := .error "the picture has no pixels, or too many"
    #[{ name := "", format := .png, spec,
        bytes := fun _ => match im with
          | some i => (i.writePng).mapError toString
          | none => none' },
      { name := "", format := .pdf, spec,
        bytes := fun _ => match im.bind Pdf.ofImage with
          | some b => .ok b
          | none => none' }]

/-- A graph with how it is laid out and drawn. -/
structure GraphFigure where
  /-- The graph. -/
  graph : Graph
  /-- The options of the layered layout. -/
  options : Graph.LayeredOptions := {}
  /-- The style. -/
  style : Style := {}
  /-- The scale of the PNG relative to the SVG. -/
  scale : Float := 1

/-- A graph with the layout and style of the default `GraphFigure`: the SVG, the PNG and the
PDF. -/
instance : ToOutputs GraphFigure where
  outputs f :=
    let g := f.graph
    #[{ name := "", format := .svg, bytes := fun _ => .ok (g.toSvg f.options f.style).toUTF8,
        spec := (g.toSvg f.options f.style).toUTF8, textEngine := f.style.text.id },
      { name := "", format := .png,
        bytes := fun _ => match g.toPng f.options f.style f.scale with
          | .ok b => .ok b
          | .error e => .error (toString e),
        spec := (g.toSvg f.options f.style (outlines := true)).toUTF8,
        textEngine := f.style.text.id },
      { name := "", format := .pdf, bytes := fun _ => .ok (g.toPdf f.options f.style),
        spec := (g.toSvg f.options f.style (outlines := true)).toUTF8,
        textEngine := f.style.text.id }]

/-- A graph is rendered with the default layered layout and light style, scale 1. -/
instance : ToOutputs Graph where
  outputs g := ToOutputs.outputs ({ graph := g } : GraphFigure)

/-- Animations: the animated SVG (with the animation's problems as warnings), the APNG, the GIF
and the poster frame (a PNG and a PDF with the suffix `-poster`). An animation whose problems
stop it (`Animation.problemsFail`) cannot be rendered. -/
instance : ToOutputs Animation where
  outputs a :=
    let svg := a.toSvg.toUTF8
    let ok := checkedBytes a.problemsFail a.problems
    let toErr := fun {ε : Type} [ToString ε] (r : Except ε ByteArray) =>
      r.mapError toString
    let t := a.text.id
    #[{ name := "", format := .svg, bytes := fun _ => ok fun _ => .ok svg, spec := svg,
        textEngine := t, problems := fun _ => if a.problemsFail then #[] else a.problems () },
      { name := "", format := .apng, bytes := fun _ => ok fun _ => toErr a.toApng, spec := svg,
        textEngine := t },
      { name := "", format := .gif, bytes := fun _ => ok fun _ => toErr a.toGif, spec := svg,
        textEngine := t },
      { name := "-poster", format := .png, bytes := fun _ => ok fun _ => toErr a.posterPng,
        spec := a.posterSvg.toUTF8, textEngine := t },
      { name := "-poster", format := .pdf, bytes := fun _ => ok fun _ => .ok a.posterPdf,
        spec := a.posterSvg.toUTF8, textEngine := t }]

end PILean.Trust
