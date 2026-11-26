/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Trust.Figure
import PILean.Plane.MotionPanels

/-!
# Motions as build outputs

A motion of plane figures (`PILean.Plane.Motion`) or a picture of several motions as panels on one
clock (`PILean.Plane.MotionPanels`) becomes files through a *checked motion* (`CheckedMotion`).
Its constructor is private to this module: a checked motion is made only from the checked report
of a motion (`Plane.MotionReport.checked`) or of a picture of panels
(`Plane.MotionPanelsReport.checked`), so whether it is stopped, which errors stop it and which
were left cannot be claimed apart from the report. It holds what every output reads: the checked
animated SVG (never one of the routes that end in `Unchecked`), the key stills ready-made
(`MotionStill`), the captions, the cycle, the table of the steps and the problems.
`ToCheckedMotion α` says which report a value of `α` is checked by; `motionOutputs` turns a
checked motion into the files.

For a motion `m` declared as `d`, with `n` keys, the files are (`docs/DESIGN.md`):

* `d.svg`: the animated SVG (`MotionReport.svg?`, `MotionPanelsReport.svg?`);
* `d-poster.png`, `d-poster.pdf`: the poster key's still;
* `d-keys.svg`, `.png`, `.pdf`: the contact sheet, every key's still in a grid with its caption
  (`CheckedMotion.sheet`), with a title and a description listing the captions;
* `d-key-k.svg`, `d-key-k.png` for each key `k` from `0`: the still of key `k`, byte for byte the
  SVG and PNG of the key figure (`Plane.Motion.keyFigure k`) or of the picture's key
  (`MotionPanelsReport.keyStillSvg k`, `keyStillPng k`);
* with a narrow rendition (a picture of panels with a `narrowWidth`): `d-narrow.svg` and
  `d-narrow-key-k.svg`, `.png`;
* only when asked (`MotionFigure.rasters`): the APNG `d.png` and the GIF `d.gif` of the baked
  frames.

A motion that is stopped renders none of them: every output fails with the messages of what
stops it, and has no inline picture, no theme and no page data. It is stopped by an error under
`CheckLevel.fail` (the default), and at every level when it is not well formed, when its written
picture has an id twice (actor ids that differ but are written alike), or, for a picture of
panels, when its panels use different text engines. Every output records the motion
(`Output.motion`: keys, cycle, captions, check level, and whether errors were left), in its
source record and in the manifest; the animated SVG also carries what a page needs to show it
inline (`Output.motionPage`).

## Main definitions

* `MotionStill`, `MotionRendition`, `CheckedMotion`, `ToCheckedMotion`: the interface.
* `liveNodes`, `duplicateIds`: what the written picture holds.
* `wrapText`, `sheetColumns`, `sheetOf`, `CheckedMotion.sheet`, `CheckedMotion.sheetNodes`,
  `CheckedMotion.sheetSvg`: the contact sheet.
* `stillOutputs`, `MotionFigure`, `motionOutputs`, and the instances for `Plane.Motion`,
  `Plane.MotionPanels` and `MotionFigure`.
* `Plane.moveRows`, `Plane.Motion.stepRows`, `Plane.MotionReport.checked`,
  `Plane.MotionPanelsReport.checked`, `Plane.Motion.withStyle`, `Plane.MotionPanels.withStyle`.
-/

namespace PILean.Trust

open Canvas

/-! ### The interface -/

/-- A key still, ready-made: its page size, the SVG nodes of its body (`svg` is their document),
the same with text drawn as shapes (the specification of its PNG and PDF), its PNG and PDF, its
drawing for the contact sheet, and its style. -/
structure MotionStill where
  /-- The width in pixels. -/
  width : Float
  /-- The height in pixels. -/
  height : Float
  /-- The SVG nodes of the body. -/
  nodes : Array Svg.Node
  /-- The SVG nodes with text drawn as shapes. -/
  outlined : Array Svg.Node
  /-- The PNG, if the still has pixels. -/
  png : Unit → Option ByteArray
  /-- The PDF. -/
  pdf : Unit → ByteArray
  /-- The drawing, for the contact sheet. -/
  drawing : Shape
  /-- The style. -/
  style : Style

instance : Inhabited MotionStill :=
  ⟨{ width := 0, height := 0, nodes := #[], outlined := #[], png := fun _ => none,
     pdf := fun _ => .empty, drawing := .group #[], style := {} }⟩

/-- The SVG document of a still. -/
def MotionStill.svg (s : MotionStill) : String := Svg.document s.width s.height s.nodes

/-- The still as a picture a page puts inline. -/
def MotionStill.inline (s : MotionStill) : InlineSvg :=
  InlineSvg.ofStyle s.width s.height s.nodes s.style

/-- The still of a frame (for a key figure, `ExplorerFrame.ofPlane`, which draws it as the plane
figures' pipeline does: the SVG, PNG and PDF of the figure, byte for byte). -/
def MotionStill.ofFrame (f : ExplorerFrame) : MotionStill :=
  { width := f.width, height := f.height, nodes := f.svgNodes, outlined := f.svgNodes (some true),
    png := fun _ => f.toPng, pdf := fun _ => f.toPdf, drawing := f.drawing, style := f.style }

/-- One rendition of a checked motion (the motion at its width, or its narrow rendition): its
page size, the checked animated SVG document (or the messages of the errors that stop it), the
nodes of its moving picture for a page (`liveNodes`), its key stills, and what stops this
rendition beyond what stops the motion (`stops`: the errors of a narrow rendition). -/
structure MotionRendition where
  /-- The width in pixels. -/
  width : Float
  /-- The height in pixels. -/
  height : Float
  /-- The animated SVG document, or the messages of the errors that stop the motion. -/
  svg : Except (Array String) String
  /-- The moving picture for a page; empty when the rendition is stopped. -/
  live : Array Svg.Node
  /-- The still of each key, in order. -/
  stills : Array MotionStill
  /-- What stops this rendition beyond what stops the motion. -/
  stops : Array String := #[]

/-- A motion checked once, as its outputs read it. Made only by `Plane.MotionReport.checked` and
`Plane.MotionPanelsReport.checked` (the constructor is private), so every field that says how the
motion was checked comes from its report. -/
structure CheckedMotion where private mk ::
  /-- The title of the picture (the sheet's heading and title). -/
  title : String
  /-- One caption per key. -/
  captions : Array String
  /-- The key shown as the poster. -/
  poster : Nat
  /-- The length of one cycle, in seconds. -/
  cycle : Rat
  /-- The style the sheet is drawn in (background, colours, text engine). -/
  style : Style
  /-- Whether the sheet's SVG draws its text as shapes. -/
  textAsShapes : Bool
  /-- The level the motion's checks were applied at. -/
  checks : CheckLevel
  /-- The motion at its width. -/
  main : MotionRendition
  /-- The narrow rendition, for small screens, if the motion has one. -/
  narrow : Option MotionRendition
  /-- The table of the steps. -/
  steps : Array MotionStepRow
  /-- Whether items change between two keys without a declared move. -/
  crossfades : Bool
  /-- The messages of the problems a build reports as warnings (empty when stopped). -/
  warnings : Array String
  /-- What stops the motion: its errors under `fail`, and at every level what makes it
  impossible to write as recorded (not well formed, an id twice, several text engines). -/
  stops : Array String
  /-- Whether its checks found errors that did not stop it (under `warn` or `ignore`). -/
  unchecked : Bool
  /-- The motion as baked frames at a number of frames a second, or what stops it. -/
  animation : Nat → Except (Array String) Animation

/-- Values that are rendered as motions: the checked motion of their report. -/
class ToCheckedMotion (α : Type) where
  /-- The motion checked once (`Plane.MotionReport.checked`, `Plane.MotionPanelsReport.checked`).
  -/
  checked : α → CheckedMotion

/-- Whether the checked motion is stopped. -/
def CheckedMotion.stopped (c : CheckedMotion) : Bool := !c.stops.isEmpty

/-- The check level's word in a record: `fail`, `warn` or `ignore`. -/
def levelWord : CheckLevel → String
  | .fail => "fail" | .warn => "warn" | .ignore => "ignore"

/-- The record every output of the checked motion carries. -/
def CheckedMotion.summary (c : CheckedMotion) : MotionSummary :=
  { keys := c.main.stills.size, cycle := c.cycle, captions := c.captions.size,
    checks := levelWord c.checks, unchecked := c.unchecked }

/-- The body of the root `root` of an animated SVG as a page puts it inline: its children without
`title`, `desc`, `style` and the poster group (class `Animation.posterClass`). -/
def liveNodes (root : Svg.Node) : Array Svg.Node :=
  match root with
  | .element _ _ cs => cs.filter fun
    | .element n as _ =>
      !(n == "title" || n == "desc" || n == "style" ||
        (n == "g" && as.contains ("class", Animation.posterClass)))
    | .text _ => true
  | .text _ => #[]

/-- The values of the `id` attributes of an SVG document that occur more than once, each once, in
order of first occurrence: a cheap scan of the written text (an attribute ` id="…"`). -/
def duplicateIds (doc : String) : Array String := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut dups : Array String := #[]
  for piece in (doc.splitOn " id=\"").drop 1 do
    let v := (piece.splitOn "\"").headD ""
    if seen.contains v then
      if !dups.contains v then dups := dups.push v
    else seen := seen.insert v
  return dups

/-- The messages for the ids the document `doc` has twice, naming the actors (`actors`) whose
written id ends each such id (`safeToken`). -/
def idStops (doc : String) (actors : Array String) : Array String :=
  (duplicateIds doc).map fun v =>
    let names := actors.filter fun a => v.endsWith (safeToken a)
    s!"the written picture has the id {v} more than once (the actors \
      {", ".intercalate names.toList} are written alike): give them ids that differ in their \
      letters, digits, `_`, `-` and `.`"

/-- What a page needs to show the rendition `r` of the checked motion inline. -/
def CheckedMotion.page (c : CheckedMotion) (r : MotionRendition) : MotionData :=
  { summary := c.summary, live := InlineSvg.ofStyle r.width r.height r.live c.style,
    stills := { stepCaptions := c.captions, frames := r.stills.map (·.inline),
                poster := c.poster },
    steps := c.steps, crossfades := c.crossfades }

/-! ### The contact sheet -/

/-- The words of `s` in lines no wider than `width` at the size `size` of the text engine `e`, the
words kept whole and in order (a word wider than `width` gets a line of its own). -/
def wrapText (e : TextEngine) (size width : Float) (s : String) : Array String := Id.run do
  let mut lines : Array String := #[]
  let mut cur := ""
  for w in (s.splitOn " ").filter (!·.isEmpty) do
    let next := if cur.isEmpty then w else cur ++ " " ++ w
    if cur.isEmpty || e.measure next size ≤ width then cur := next
    else
      lines := lines.push cur
      cur := w
  if !cur.isEmpty then lines := lines.push cur
  return lines

/-- The widest the contact sheet is laid out, in pixels: two stills of 360 pixels side by side;
printed across a page of 6.5 inches, its captions at `sheetCaptionSize` are about eight points
tall. -/
def sheetMaxWidth : Float := 800

/-- The room around the sheet and between its cells, in pixels. -/
def sheetGap : Float := 20

/-- The size of the captions on the sheet, in pixels. -/
def sheetCaptionSize : Float := 14

/-- The number of columns of the sheet for `n` stills of width `w`: as many as fit in
`sheetMaxWidth` (at least one, at most `n`), then as few as keep the same number of rows, so the
rows are filled evenly. -/
def sheetColumns (n : Nat) (w : Float) : Nat :=
  let fit := ((sheetMaxWidth - sheetGap) / (w + sheetGap)).floor
  let fit := if fit.isNaN || fit < 1 then 1 else fit.toUInt64.toNat
  let c := max 1 (min n fit)
  let rows := (n + c - 1) / c
  if rows == 0 then 1 else (n + rows - 1) / rows

/-- The contact sheet of key stills: the title on top (if any), then the stills at their own size
in a grid of `sheetColumns` columns, each framed by a thin line in the style's faint colour, with
its caption wrapped below it in the style's ink, on the style's background. One drawing, written
as SVG, PNG and PDF like a frame of an explorer (`ExplorerFrame`); its text is drawn by the
style's text engine. -/
def sheetOf (title : String) (captions : Array String) (stills : Array MotionStill)
    (st : Style) (textAsShapes : Bool := true) : ExplorerFrame :=
  let w := stills.foldl (fun a f => max a f.width.round) 0
  let h := stills.foldl (fun a f => max a f.height.round) 0
  let n := stills.size
  let cols := sheetColumns n w
  let ink := st.plane.ink
  let size := sheetCaptionSize
  let lineH := (size * 1.4).round
  let capLines := (Array.range n).map fun k => wrapText st.text size w (captions.getD k "")
  let top := if title.isEmpty then sheetGap else sheetGap + (size * 1.3).round + sheetGap
  let rows := (n + cols - 1) / cols
  -- the height of each row: the stills and the most caption lines in it
  let rowH := (Array.range rows).map fun r =>
    let most := (Array.range cols).foldl (init := 0) fun a c =>
      max a ((capLines.getD (r * cols + c) #[]).size)
    h + (if most == 0 then 0 else 8 + most.toFloat * lineH)
  let rowY := rowH.foldl (init := (#[], top)) (fun (ys, y) rh => (ys.push y, y + rh + sheetGap))
  let width := sheetGap + cols.toFloat * (w + sheetGap)
  let height := if n == 0 then top + sheetGap else rowY.2
  let cells := (Array.range n).flatMap fun k =>
    let x := sheetGap + (k % cols).toFloat * (w + sheetGap)
    let y := rowY.1.getD (k / cols) top
    let f := stills.getD k default
    #[Shape.group #[f.drawing] (Affine.translate x y),
      .path (Canvas.rect (x - 0.5) (y - 0.5) (w + 1) (h + 1)) none
        (some { ink := st.plane.faint, width := 1 })] ++
      (capLines.getD k #[]).mapIdx fun i line =>
        Shape.text line ⟨x, y + h + 8 + size + i.toFloat * lineH⟩ size ink
  let head := if title.isEmpty then #[] else
    #[Shape.text title ⟨sheetGap, sheetGap + size * 1.3⟩ (size * 1.3) ink]
  { drawing := .group (#[.path (Canvas.rect 0 0 width height) (some (.solid st.background))] ++
      head ++ cells),
    width, height, style := st, srgb := true, textAsShapes }

/-- The contact sheet of the checked motion's key stills (`sheetOf`). -/
def CheckedMotion.sheet (c : CheckedMotion) : ExplorerFrame :=
  sheetOf c.title c.captions c.main.stills c.style c.textAsShapes

/-- The nodes of the contact sheet's SVG: a `title` (the motion's title and `key frames`) and a
`desc` listing the captions, the accessible name and description of a sheet whose text is drawn
as shapes, then the sheet's drawing. -/
def CheckedMotion.sheetNodes (c : CheckedMotion) : Array Svg.Node :=
  let title := if c.title.isEmpty then "Key frames" else s!"{c.title}: key frames"
  #[Svg.el "title" #[] #[.text title],
    Svg.el "desc" #[] #[.text (" ".intercalate c.captions.toList)]] ++ c.sheet.svgNodes

/-- The contact sheet's SVG document (`sheetNodes`). -/
def CheckedMotion.sheetSvg (c : CheckedMotion) : String :=
  Svg.document c.sheet.width c.sheet.height c.sheetNodes

/-! ### The outputs -/

/-- The SVG (with its inline picture and its theme) and the PNG of a still, named with `suffix`,
and its PDF when `pdf`. -/
def stillOutputs (f : MotionStill) (suffix : String) (pdf : Bool := false) : Array Output :=
  let t := f.style.text.id
  let outlined := (Svg.document f.width f.height f.outlined).toUTF8
  #[{ name := suffix, format := .svg, bytes := fun _ => .ok f.svg.toUTF8,
      spec := f.svg.toUTF8, textEngine := t, inline := fun _ => some f.inline,
      theme := fun _ => InlineSvg.themeOf f.style },
    { name := suffix, format := .png,
      bytes := fun _ => match f.png () with
        | some b => .ok b
        | none => .error "the still has no pixels",
      spec := outlined, textEngine := t }] ++
    if pdf then #[{ name := suffix, format := .pdf, bytes := fun _ => .ok (f.pdf ()),
                    spec := outlined, textEngine := t }]
    else #[]

/-- A motion with the choices of its outputs: whether the APNG and the GIF of its baked frames are
written too (`rasters`, off by default: the animated SVG is the motion, and baked frames of a long
motion are large), and at how many frames a second. -/
structure MotionFigure (α : Type) where
  /-- The motion. -/
  motion : α
  /-- Whether to write the APNG and the GIF of the baked frames. -/
  rasters : Bool := false
  /-- The frames a second of the APNG and the GIF. -/
  fps : Nat := 30

/-- The output `o` of a motion stopped by `es`: its bytes the messages, and no inline picture, no
theme, no page data and no warnings; unchanged when `es` is empty. -/
def stoppedBy (es : Array String) (o : Output) : Output :=
  if es.isEmpty then o
  else { o with bytes := fun _ => .error ("problems: " ++ "; ".intercalate es.toList),
                inline := fun _ => none, theme := fun _ => (#[], #[]),
                motionPage := fun _ => none, problems := fun _ => #[] }

/-- The outputs of a checked motion (see the module docstring), the APNG and the GIF only with
`rasters`, at `fps` frames a second. Every output records the motion (`Output.motion`); every
output of a stopped motion fails with what stops it (`stoppedBy`), and those of a stopped narrow
rendition with what stops that too; the animated SVG carries the warnings and what a page needs
to show it (`Output.motionPage`). -/
def motionOutputs (c : CheckedMotion) (rasters : Bool := false) (fps : Nat := 30) :
    Array Output :=
  let summary := c.summary
  let t := c.style.text.id
  let animated := fun (suffix : String) (r : MotionRendition) =>
    let spec := match r.svg with | .ok s => s.toUTF8 | .error _ => .empty
    ({ name := suffix, format := .svg, spec, textEngine := t,
       bytes := fun _ => match r.svg with
         | .ok s => .ok s.toUTF8
         | .error es => .error ("problems: " ++ "; ".intercalate es.toList),
       theme := fun _ => InlineSvg.themeOf c.style,
       motionPage := fun _ => some (c.page r) } : Output)
  let stills := fun (suffix : String) (r : MotionRendition) =>
    r.stills.zipIdx.flatMap fun (f, k) => stillOutputs f s!"{suffix}-key-{k}"
  let main := animated "" c.main
  let anim := fun (fmt : Format) =>
    ({ name := "", format := fmt, spec := main.spec, textEngine := t,
       bytes := fun _ => match c.animation fps with
         | .ok a => if fmt == .gif then a.toGif.mapError toString else a.toApng.mapError toString
         | .error es => .error ("problems: " ++ "; ".intercalate es.toList) } : Output)
  let raster : Array Output := if rasters then #[anim .apng, anim .gif] else #[]
  -- a poster out of range stops the motion (it is not well formed); its files still fail
  let poster := (stillOutputs (c.main.stills.getD c.poster default) "-poster" (pdf := true)).filter
    (·.format != .svg)
  let sh := c.sheet
  let sheetSvg := c.sheetSvg
  let sheet : Array Output :=
    #[{ name := "-keys", format := .svg, bytes := fun _ => .ok sheetSvg.toUTF8,
        spec := sheetSvg.toUTF8, textEngine := t,
        inline := fun _ => some (InlineSvg.ofStyle sh.width sh.height c.sheetNodes c.style),
        theme := fun _ => InlineSvg.themeOf c.style },
      { name := "-keys", format := .png,
        bytes := fun _ => match sh.toPng with
          | some b => .ok b
          | none => .error "the contact sheet has no pixels",
        spec := (sh.toSvg (outlines := true)).toUTF8, textEngine := t },
      { name := "-keys", format := .pdf, bytes := fun _ => .ok sh.toPdf,
        spec := (sh.toSvg (outlines := true)).toUTF8, textEngine := t }]
  let wide := #[{ main with problems := fun _ => c.warnings }] ++ raster ++ poster ++ sheet ++
    stills "" c.main
  let narrow := match c.narrow with
    | some r =>
      (#[animated "-narrow" r] ++ stills "-narrow" r).map (stoppedBy (c.stops ++ r.stops))
    | none => #[]
  (wide.map (stoppedBy c.stops) ++ narrow).map fun o => { o with motion := fun _ => summary }

/-- A motion with the choices of its outputs: the outputs of `motionOutputs`. -/
instance {α : Type} [ToCheckedMotion α] : ToOutputs (MotionFigure α) where
  outputs f := motionOutputs (ToCheckedMotion.checked f.motion) f.rasters f.fps

end PILean.Trust

namespace PILean.Plane

open PILean.Trust

/-! ### The step table -/

/-- What the animation draws for the move `mv` of the actor `id` in step `j`, given the layers
`vs` of the motion (`Motion.versions`): the move's own kind when a layer of the actor carries it
from key `j` to key `j + 1` by that move (a turn, a slide or a morph), or when the actor really
appears or vanishes there; `crossfade` otherwise (the move does not land, and the two drawings
crossfade). -/
def moveDrawn (vs : Array MotionVersion) (j : Nat) (id : String) (mv : Move) : String :=
  let mine := vs.filter (·.actor == some id)
  let across := mine.find? fun v => v.first ≤ j && j + 1 ≤ v.last
  let sameKind := fun (m : Option Move) => (match mv, m with
    | .turn .., some (.turn ..) | .slide _, some (.slide _) | .morph, some .morph => true
    | _, _ => false : Bool)
  let ok : Bool := match mv with
    | .turn .. | .slide _ | .morph =>
      across.any fun v => sameKind (v.moves.getD (j - v.first) none)
    | .appear => !mine.any (·.visible j)
    | .vanish => !mine.any (·.visible (j + 1))
  if ok then mv.name else "crossfade"

/-- The rows of the moves `moves` of step `j` of a panel named `panel` (empty for one motion),
with what the animation draws for each (`moveDrawn`). -/
def moveRows (vs : Array MotionVersion) (panel : String) (j : Nat)
    (moves : Array (String × Move)) : Array MotionMoveRow :=
  moves.map fun (id, mv) =>
    let drawn := moveDrawn vs j id mv
    match mv with
    | .turn c q => { panel, actor := id, kind := mv.name, centre := some c, turns := some q, drawn }
    | .slide v => { panel, actor := id, kind := mv.name, vector := some v, drawn }
    | _ => { panel, actor := id, kind := mv.name, drawn }

/-- Whether some item of the motion with layers `vs` and `n` keys changes between two keys
without a declared move: a layer that begins after the first key without a declared appearance,
or ends before the last without a declared disappearance (a crossfade). -/
def crossfadesIn (m : Motion) (vs : Array MotionVersion) (n : Nat) : Bool :=
  let declared := fun (j : Nat) (actor : Option String) (want : Move → Bool) =>
    match actor with
    | some id => (m.moveOf j id).any want
    | none => false
  vs.any fun v =>
    (v.first > 0 && !declared (v.first - 1) v.actor (· matches .appear)) ||
      (v.last + 1 < n && !declared v.last v.actor (· matches .vanish))

/-- The table of the motion's steps (its keys as drawn `K`): for each step its duration
(`Motion.animStep` of the pacing, a negative one as zero), whether it is idle, and each declared
move with its centre and exact fraction of a turn, or its vector, and what the animation draws
for it (`moveDrawn`). -/
def Motion.stepRows (m : Motion) (K : MotionKeys := m.keysOf) : Array MotionStepRow :=
  let vs := (m.versions K K.env).1
  m.steps.mapIdx fun j s =>
    { step := j, duration := max 0 (Motion.animStep m.pacing s).dur, idle := s.kind == .idle,
      moves := moveRows vs "" j s.moves }

/-- The motion with every key, and every figure between two keys, drawn in the style `st`: for
the dark twin of a motion whose keys have the light colours, `Style.darkTwin?` of
`Motion.style`. -/
def Motion.withStyle (m : Motion) (st : Style) : Motion :=
  { m with keys := m.keys.map ({ · with style := st }),
           between := fun j q => (m.between j q).map ({ · with style := st }) }

/-- The style of a motion: that of its first key. -/
def Motion.style (m : Motion) : Style := (m.keys[0]?.map (·.style)).getD {}

/-- The picture with every panel's motion drawn in the style `st` (`Motion.withStyle`). -/
def MotionPanels.withStyle (P : MotionPanels) (st : Style) : MotionPanels :=
  { P with panels := P.panels.map fun p => { p with motion := p.motion.withStyle st } }

/-- The style of a picture of panels: that of its first panel. -/
def MotionPanels.style (P : MotionPanels) : Style :=
  ((P.panels[0]?).map (·.motion.style)).getD {}

/-! ### The checked motions -/

/-- The ids of a motion's actors, in the order of its keys, each once. -/
def Motion.actorIds (m : Motion) : Array String :=
  (m.keys.flatMap (·.items.filterMap Item.actorId?)).toList.eraseDups.toArray

/-- The checked motion of the report of one motion (`Motion.report`): the animated SVG of the
checked route (`MotionReport.svg?`), the body of its root for a page (`liveNodes`), the stills
(the keys as drawn, `Motion.keyFigure`, through `ExplorerFrame.ofPlane`), the step table, the
warnings, and what stops it: its errors under `fail`, and at every level the errors of a motion
that is not well formed (`Motion.WellFormed`) and an id written twice (`idStops`). A single
motion has no narrow rendition. -/
def MotionReport.checked (r : MotionReport) : CheckedMotion :=
  let f := r.plan.env.frame
  let m := r.motion
  let errors := r.errors
  let wellFormed := decide m.WellFormed
  let idProblems := match r.svg? with
    | .ok doc => idStops doc m.actorIds
    | .error _ => #[]
  let stops := (if r.problemsFail || !wellFormed then errors else #[]) ++ idProblems
  let st := (r.keys.figure 0).style
  { title := m.info.title, captions := m.captions, poster := m.poster,
    cycle := r.plan.timeline.cycle, style := st,
    textAsShapes := (r.keys.figure 0).textAsShapes, checks := m.checks,
    main := { width := f.width.round, height := f.height.round, svg := r.svg?,
              live := if !stops.isEmpty then #[] else liveNodes (m.svgRootIn r.keys r.plan),
              stills := r.keys.figs.map fun fig => MotionStill.ofFrame (ExplorerFrame.ofPlane fig) },
    narrow := none,
    steps := m.stepRows r.keys,
    crossfades := crossfadesIn m (m.versions r.keys r.keys.env).1 m.keys.size,
    warnings := if !stops.isEmpty then #[] else r.checkMessages,
    stops, unchecked := stops.isEmpty && !errors.isEmpty,
    animation := fun fps => if stops.isEmpty then r.animation? fps else .error stops }

/-- A motion is checked by its report. -/
instance : ToCheckedMotion Motion where
  checked m := m.report.checked

/-- Motions: the outputs of `motionOutputs`, without the APNG and the GIF (`MotionFigure` asks for
them). -/
instance : ToOutputs Motion where
  outputs m := motionOutputs m.report.checked

/-- What stops a picture of panels from being written as recorded, at every level: the errors of
a picture that is not well formed, panels drawn with different text engines (its stills and its
sheet are drawn with one), and an id written twice (`idStops`). -/
def MotionPanelsReport.writeStops (r : MotionPanelsReport) : Array String :=
  let engines := (r.panels.map (·.keys.env.style.text.id)).toList.eraseDups
  let actors := r.figure.panels.flatMap (·.motion.actorIds)
  (if decide r.figure.WellFormed then #[] else r.errors) ++
    (if engines.length > 1 then
      #["the panels are drawn with different text engines; a picture of panels uses one"]
    else #[]) ++
    (match r.svg? with
      | .ok doc => idStops doc actors
      | .error _ => #[])

/-- The still of key `k` of a picture of panels: the picture's key (`stillNodes`, whose document
is `keyStillSvg k`; `keyStillPng k`), its PDF drawn from the same shapes (`stillShape`, text by
the picture's text engine). -/
def MotionPanelsReport.still (r : MotionPanelsReport) (k : Nat) : MotionStill :=
  let w := r.layout.width.round
  let h := r.layout.height.round
  let st := r.style
  let outlined := (r.stillShape k).render (.shapes st.text)
  { width := w, height := h, nodes := r.stillNodes k, outlined,
    png := fun _ => r.keyStillPng k,
    pdf := fun _ => Pdf.ofSvgNodes w h outlined st.background,
    drawing := r.stillShape k, style := st }

/-- The rendition of a picture of panels: its checked SVG, the body of its root for a page (the
background, the panels' titles and the moving picture, as the file writes them before the poster
group), its stills, and what stops it beyond `stops`. -/
def MotionPanelsReport.rendition (r : MotionPanelsReport) (stops : Array String) :
    MotionRendition :=
  { width := r.layout.width.round, height := r.layout.height.round, svg := r.svg?,
    live := if !stops.isEmpty then #[] else
      r.background.render r.mode ++ r.titleNodes ++
        #[Svg.el "g" #[("class", Animation.liveClass)] r.liveNodes],
    stills := (Array.range r.figure.keyCount).map r.still, stops }

/-- The step table of a picture of panels (`stepRows`): each step's duration on the shared
timeline, whether it is idle, and every panel's moves, named by the panel (`MotionPanels.name`),
with what the animation draws for each (`moveDrawn`, from the panel's layers). -/
def MotionPanelsReport.tableRows (r : MotionPanelsReport) : Array MotionStepRow :=
  let vss := r.panels.map fun pr => (pr.motion.versions pr.keys pr.keys.env).1
  r.stepRows.map fun row =>
    { step := row.step, duration := max 0 row.duration, idle := row.kind == .idle,
      moves := row.moves.flatMap fun (i, id, mv) =>
        moveRows (vss.getD i #[]) (r.figure.name i) row.step #[(id, mv)] }

/-- The checked motion of the report of a picture of panels (`MotionPanels.report`), with the
report of its narrow rendition (`MotionPanels.narrow`), if it has one: the main rendition stopped
by the picture's errors under `fail` and by `writeStops`; the narrow one also by its own errors
under `fail` and its own `writeStops`; the errors left by either, under `warn` or `ignore`, make
the motion `unchecked`. -/
def MotionPanelsReport.checked (r : MotionPanelsReport) (narrow : Option MotionPanelsReport) :
    CheckedMotion :=
  let P := r.figure
  let stops := (if r.problemsFail then r.errors else #[]) ++ r.writeStops
  let narrowStops := fun (n : MotionPanelsReport) =>
    ((if n.problemsFail then n.errors else #[]) ++ n.writeStops).map ("narrow rendition: " ++ ·)
  let left := !r.errors.isEmpty || narrow.any (!·.errors.isEmpty)
  { title := P.info.title, captions := P.captions, poster := P.poster,
    cycle := r.timeline.cycle, style := r.style,
    textAsShapes := ((r.panels[0]?).bind fun pr => (pr.keys.figs[0]?).map (·.textAsShapes)).getD
      true,
    checks := P.checks,
    main := r.rendition stops,
    narrow := narrow.map fun n => n.rendition (narrowStops n),
    steps := r.tableRows,
    crossfades := r.panels.any fun pr =>
      crossfadesIn pr.motion (pr.motion.versions pr.keys pr.keys.env).1 pr.motion.keys.size,
    warnings := if !stops.isEmpty then #[] else
      r.checkMessages ++ ((narrow.map (·.checkMessages.map ("narrow rendition: " ++ ·))).getD #[]),
    stops, unchecked := stops.isEmpty && left,
    animation := fun fps => if stops.isEmpty then r.animation? fps else .error stops }

/-- A picture of panels is checked by its report and that of its narrow rendition. -/
instance : ToCheckedMotion MotionPanels where
  checked P := P.report.checked (P.narrow.map (·.report))

/-- Pictures of panels: the outputs of `motionOutputs`, without the APNG and the GIF
(`MotionFigure` asks for them). -/
instance : ToOutputs MotionPanels where
  outputs P := motionOutputs (ToCheckedMotion.checked P)

end PILean.Plane
