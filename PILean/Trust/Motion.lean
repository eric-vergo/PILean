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
Its constructor is private to this module: a checked motion is made only from a motion
(`Plane.Motion.checked`) or a picture of panels (`Plane.MotionPanels.checked`), whose reports are
computed there, so whether it is stopped, which errors stop it and which were left cannot be
claimed apart from the checks; no function takes a report. It holds what every output reads: the checked
animated SVG (never one of the routes that end in `Unchecked`), the key stills ready-made
(`MotionStill`), the captions, the cycle, the table of the steps and the problems.
`ToCheckedMotion α` says which report a value of `α` is checked by; `motionOutputs` turns a
checked motion into the files.

For a motion `m` declared as `d`, with `n` keys, the files are (`docs/DESIGN.md`):

* `d.svg`: the animated SVG (`MotionReport.svg?`, `MotionPanelsReport.svg?`);
* `d-poster.png`, `d-poster.pdf`: the poster key's still;
* `d-keys.svg`, `.png`, `.pdf`: the contact sheet, every still in a grid with its caption
  (`CheckedMotion.sheet`), with a title and a description listing the captions;
* `d-key-k.svg`, `d-key-k.png` for each key `k` that is a still (`Plane.Motion.stillKeys`; every
  key, from `0`, unless some key is not a still): the still of key `k`, byte for byte the SVG and
  PNG of the key figure (`Plane.Motion.keyFigure k`) or of the picture's key
  (`MotionPanelsReport.keyStillSvg k`, `keyStillPng k`);
* with a narrow rendition (a picture of panels with a `narrowWidth`): `d-narrow.svg` and
  `d-narrow-key-k.svg`, `.png`;
* only when asked (`MotionFigure.rasters`): the APNG `d.png` and the GIF `d.gif` of the baked
  frames.

A motion that is stopped renders none of them: every output fails with the messages of what stops
it, and has no inline picture, no theme and no page data. It is stopped by an error under
`CheckLevel.fail` (the default), and at every level when it is not well formed, when its written
picture has an id twice (actor ids that differ but are written alike), when its poster is not a
still, or, for a picture of panels, when its panels use different text engines. Every output records
the motion (`Output.motion`: keys, cycle, captions, check level, whether errors were left, and the
stills when some key is not one), in its source record and in the manifest; the animated SVG also
carries what a page needs to show it inline (`Output.motionPage`).

## Main definitions

* `MotionStill`, `MotionRendition`, `CheckedMotion`, `ToCheckedMotion`: the interface.
* `liveNodes`, `duplicateIds`: what the written picture holds.
* `wrapText`, `sheetColumns`, `sheetOf`, `CheckedMotion.sheet`, `CheckedMotion.sheetNodes`,
  `CheckedMotion.sheetSvg`: the contact sheet.
* `stillOutputs`, `MotionFigure`, `motionOutputs`, and the instances for `Plane.Motion`,
  `Plane.MotionPanels` and `MotionFigure`.
* `Plane.moveRows`, `Plane.Motion.stepRows`, `Plane.Motion.restRows`,
  `Plane.Motion.stepWindowSeconds`, `Plane.Motion.restFadeRows`, `Plane.Motion.checked`,
  `Plane.MotionPanels.checked`, `Plane.Motion.withStyle`, `Plane.MotionPanels.withStyle`.
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
  /-- The still of each key that is one (`CheckedMotion.stillKeys`), in order. -/
  stills : Array MotionStill
  /-- What stops this rendition beyond what stops the motion. -/
  stops : Array String := #[]

/-- A motion checked once, as its outputs read it. Made only by `Plane.Motion.checked` and
`Plane.MotionPanels.checked` (the constructor is private), which compute the report themselves, so
every field that says how the motion was checked comes from its checks. -/
structure CheckedMotion where private mk ::
  /-- The title of the picture (the sheet's heading and title). -/
  title : String
  /-- The number of keys. -/
  keyCount : Nat
  /-- The keys that are stills, in order. -/
  stillKeys : Array Nat
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
  /-- The rest on every key. -/
  rests : Array MotionRestRow
  /-- Whether items change between two keys without a declared move. -/
  crossfades : Bool
  /-- The messages of the problems a build reports as warnings (empty when stopped). -/
  warnings : Array String
  /-- What stops the motion: its errors under `fail`, and at every level what makes it
  impossible to write as recorded (not well formed, an id twice, several text engines). -/
  stops : Array String
  /-- The number of problems the strict level (`fail`) treats as errors that did not stop it (in a
  rendition that is written). -/
  errorsLeft : Nat
  /-- The motion as baked frames at a number of frames a second, or what stops it. -/
  animation : Nat → Except (Array String) Animation

/-- Values that are rendered as motions: the checked motion of their report. -/
class ToCheckedMotion (α : Type) where
  /-- The motion checked once (`Plane.Motion.checked`, `Plane.MotionPanels.checked`). -/
  checked : α → CheckedMotion

/-- Whether the checked motion is stopped. -/
def CheckedMotion.stopped (c : CheckedMotion) : Bool := !c.stops.isEmpty

/-- The check level's word in a record: `fail`, `warn` or `ignore`. -/
def levelWord : CheckLevel → String
  | .fail => "fail" | .warn => "warn" | .ignore => "ignore"

/-- The record every output of the checked motion carries. -/
def CheckedMotion.summary (c : CheckedMotion) : MotionSummary :=
  { keys := c.keyCount, cycle := c.cycle, captions := c.captions.size,
    checks := levelWord c.checks, errorsLeft := c.errorsLeft, narrow := c.narrow.isSome,
    stills := if c.stillKeys.size == c.keyCount then none else some c.stillKeys }

/-- The captions of the stills, in order. -/
def CheckedMotion.stillCaptions (c : CheckedMotion) : Array String :=
  c.stillKeys.map (c.captions.getD · "")

/-- The position of the poster among the stills (`0` when it is not one, which stops the
motion). -/
def CheckedMotion.posterIndex (c : CheckedMotion) : Nat := (c.stillKeys.idxOf? c.poster).getD 0

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
    stills := { stepCaptions := c.stillCaptions, frames := r.stills.map (·.inline),
                poster := c.posterIndex },
    steps := c.steps, crossfades := c.crossfades, stillKeys := c.stillKeys, rests := c.rests }

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
  sheetOf c.title c.stillCaptions c.main.stills c.style c.textAsShapes

/-- The nodes of the contact sheet's SVG: a `title` (the motion's title and `key frames`) and a
`desc` listing the captions, the accessible name and description of a sheet whose text is drawn
as shapes, then the sheet's drawing. -/
def CheckedMotion.sheetNodes (c : CheckedMotion) : Array Svg.Node :=
  let title := if c.title.isEmpty then "Key frames" else s!"{c.title}: key frames"
  #[Svg.el "title" #[] #[.text title],
    Svg.el "desc" #[] #[.text (" ".intercalate c.stillCaptions.toList)]] ++ c.sheet.svgNodes

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
    r.stills.zipIdx.flatMap fun (f, i) => stillOutputs f s!"{suffix}-key-{c.stillKeys.getD i i}"
  let main := animated "" c.main
  let anim := fun (fmt : Format) =>
    ({ name := "", format := fmt, spec := main.spec, textEngine := t,
       bytes := fun _ => match c.animation fps with
         | .ok a => if fmt == .gif then a.toGif.mapError toString else a.toApng.mapError toString
         | .error es => .error ("problems: " ++ "; ".intercalate es.toList) } : Output)
  let raster : Array Output := if rasters then #[anim .apng, anim .gif] else #[]
  -- a poster out of range stops the motion (it is not well formed); its files still fail
  let poster := (stillOutputs (c.main.stills.getD c.posterIndex default) "-poster"
    (pdf := true)).filter
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
with what the animation draws for each (`moveDrawn`) and the windows of the fades in part of the
step (`windows`: the actors with their windows in seconds from the step's start). -/
def moveRows (vs : Array MotionVersion) (panel : String) (j : Nat)
    (moves : Array (String × Move)) (windows : Array (String × Rat × Rat) := #[]) :
    Array MotionMoveRow :=
  moves.map fun (id, mv) =>
    let drawn := moveDrawn vs j id mv
    let window := (windows.find? (·.1 == id)).map (·.2)
    match mv with
    | .turn c q => { panel, actor := id, kind := mv.name, centre := some c, turns := some q, drawn }
    | .slide v => { panel, actor := id, kind := mv.name, vector := some v, drawn }
    | _ => { panel, actor := id, kind := mv.name, drawn, window }

/-- The windows of the fades of the motion in part of step `j` (`Motion.fadesOn` on the timeline
`base`), in seconds from the step's start. -/
def Motion.stepWindowSeconds (m : Motion) (K : MotionKeys) (base : Anim.Timeline) (j : Nat) :
    Array (String × Rat × Rat) :=
  let d := kindDur base (.move j)
  ((m.fadesOn K base).steps.getD j #[]).map fun (id, _, a, b) => (id, a * d, b * d)

/-- The fades of the motion during the rest on key `k` of a panel named `panel` (empty for one
motion), as rows (`Motion.fadesOn` on the timeline `base`), their windows in seconds from the
rest's start. -/
def Motion.restFadeRows (m : Motion) (K : MotionKeys) (base : Anim.Timeline) (panel : String)
    (k : Nat) : Array MotionMoveRow :=
  let d := kindDur base (.rest k)
  ((m.fadesOn K base).rests.getD k #[]).map fun (id, f, a, b) =>
    { panel, actor := id, kind := f.name, drawn := f.name, window := some (a * d, b * d) }

/-- Whether some item of the motion with layers `vs` and `n` keys changes between two keys
without a declared move: a layer that begins after the first key, or ends before the last, in a
step that declares no move for its actor (an item without an id has none). A layer that begins or
ends where its actor has a declared move is that move's appearance or disappearance, or the
crossfade of a move that does not land, which the step table marks (`moveDrawn`). -/
def crossfadesIn (m : Motion) (vs : Array MotionVersion) (n : Nat) : Bool :=
  -- a move in step `j`, or a fade during the rest on key `j + 1`, that ends or begins the layer
  let declared := fun (j : Nat) (actor : Option String) =>
    match actor with
    | some id => (m.moveOf j id).isSome || (m.restFadeOf (j + 1) id).isSome
    | none => false
  vs.any fun v =>
    (v.first > 0 && !declared (v.first - 1) v.actor) ||
      (v.last + 1 < n && !declared v.last v.actor)

/-- The table of the motion's steps (its keys as drawn `K`): for each step its duration
(`Motion.animStep` of the pacing, a negative one as zero), whether it is idle, and each declared
move with its centre and exact fraction of a turn, or its vector, and what the animation draws
for it (`moveDrawn`). -/
def Motion.stepRows (m : Motion) (K : MotionKeys := m.keysOf) : Array MotionStepRow :=
  let vs := (m.versions K K.env).1
  m.steps.mapIdx fun j s =>
    { step := j, duration := max 0 (Motion.animStep m.pacing s).dur, idle := s.kind == .idle,
      moves := moveRows vs "" j s.moves (m.stepWindowSeconds K m.baseTimeline j) }

/-- The rest on every key of the motion (its keys as drawn `K`): its duration on the motion's
timeline, whether the key is a still, and the fades during it (`Motion.restFadeRows`). -/
def Motion.restRows (m : Motion) (K : MotionKeys := m.keysOf) : Array MotionRestRow :=
  let base := m.baseTimeline
  (Array.range m.keys.size).map fun k =>
    { key := k, duration := max 0 (kindDur base (.rest k)), still := m.isStill k,
      fades := m.restFadeRows K base "" k }

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

/-- The number of problems the strict level treats as errors: those of the motion's report at its
level when that is `fail`, else those of the motion checked at `fail`. -/
def Motion.strictErrors (m : Motion) (r : MotionReport) : Nat :=
  if m.checks == .fail then r.errors.size else ({ m with checks := .fail } : Motion).report.errors.size

/-- The checked motion of one motion, its report (`Motion.report`) computed here: the animated
SVG of the checked route (`MotionReport.svg?`), the body of its root for a page (`liveNodes`), the
stills (the keys that are stills as drawn, `Motion.keyFigure`, through `ExplorerFrame.ofPlane`),
the step table and the rests,
the warnings, what stops it (its errors under `fail`, and at every level the errors of a motion
that is not well formed, `Motion.WellFormed`, an id written twice, `idStops`, and a poster that is
not a still), and the errors
the strict level finds that did not stop it (`Motion.strictErrors`). It takes the motion, not a
report, so that what it says of the checks is the checks' own. A single motion has no narrow
rendition. -/
def Motion.checked (m : Motion) : CheckedMotion :=
  let r := m.report
  let f := r.plan.env.frame
  let errors := r.errors
  let wellFormed := decide m.WellFormed
  let idProblems := match r.svg? with
    | .ok doc => idStops doc m.actorIds
    | .error _ => #[]
  let posterStops := if wellFormed && !m.isStill m.poster then
      #[s!"the poster is key {m.poster}, which is not a still"] else #[]
  let stops := (if r.problemsFail || !wellFormed then errors else #[]) ++ idProblems ++ posterStops
  let st := (r.keys.figure 0).style
  { title := m.info.title, keyCount := m.keys.size, stillKeys := m.stillKeys,
    captions := m.captions, poster := m.poster,
    cycle := r.plan.timeline.cycle, style := st,
    textAsShapes := (r.keys.figure 0).textAsShapes, checks := m.checks,
    main := { width := f.width.round, height := f.height.round, svg := r.svg?,
              live := if !stops.isEmpty then #[] else liveNodes (m.svgRootIn r.keys r.plan),
              stills := m.stillKeys.map fun k =>
                MotionStill.ofFrame (ExplorerFrame.ofPlane (r.keys.figure k)) },
    narrow := none,
    steps := m.stepRows r.keys, rests := m.restRows r.keys,
    crossfades := crossfadesIn m (m.versions r.keys r.keys.env).1 m.keys.size,
    warnings := if !stops.isEmpty then #[] else r.checkMessages,
    stops, errorsLeft := if stops.isEmpty then m.strictErrors r else 0,
    animation := fun fps => if stops.isEmpty then r.animation? fps else .error stops }

/-- A motion is checked by its report (`Motion.checked`). -/
instance : ToCheckedMotion Motion where
  checked m := m.checked

/-- Motions: the outputs of `motionOutputs`, without the APNG and the GIF (`MotionFigure` asks for
them). -/
instance : ToOutputs Motion where
  outputs m := motionOutputs m.checked

/-- What stops a picture of panels from being written as recorded, at every level: the errors of
a picture that is not well formed, panels drawn with different text engines (its stills and its
sheet are drawn with one), an id written twice (`idStops`), and a poster that is not a still. -/
def MotionPanelsReport.writeStops (r : MotionPanelsReport) : Array String :=
  let engines := (r.panels.map (·.keys.env.style.text.id)).toList.eraseDups
  let actors := r.figure.panels.flatMap (·.motion.actorIds)
  (if decide r.figure.WellFormed then #[] else r.errors) ++
    (if engines.length > 1 then
      #["the panels are drawn with different text engines; a picture of panels uses one"]
    else #[]) ++
    (match r.svg? with
      | .ok doc => idStops doc actors
      | .error _ => #[]) ++
    (if decide r.figure.WellFormed && !r.figure.isStill r.figure.poster then
      #[s!"the poster is key {r.figure.poster}, which is not a still"] else #[])

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
    stills := r.figure.stillKeys.map r.still, stops }

/-- The step table of a picture of panels (`stepRows`): each step's duration on the shared
timeline, whether it is idle, and every panel's moves, named by the panel (`MotionPanels.name`),
with what the animation draws for each (`moveDrawn`, from the panel's layers). -/
def MotionPanelsReport.tableRows (r : MotionPanelsReport) : Array MotionStepRow :=
  let vss := r.panels.map fun pr => (pr.motion.versions pr.keys pr.keys.env).1
  let base := r.figure.baseTimeline
  r.stepRows.map fun row =>
    { step := row.step, duration := max 0 row.duration, idle := row.kind == .idle,
      moves := row.moves.flatMap fun (i, id, mv) =>
        let pr := r.panels.getD i default
        moveRows (vss.getD i #[]) (r.figure.name i) row.step #[(id, mv)]
          (pr.motion.stepWindowSeconds pr.keys base row.step) }

/-- The rest on every key of a picture of panels: its duration on the shared timeline, whether the
key is a still, and every panel's fades during it, named by the panel. -/
def MotionPanelsReport.restRows (r : MotionPanelsReport) : Array MotionRestRow :=
  let base := r.figure.baseTimeline
  (Array.range r.figure.keyCount).map fun k =>
    { key := k, duration := max 0 (kindDur base (.rest k)), still := r.figure.isStill k,
      fades := r.panels.zipIdx.flatMap fun (pr, i) =>
        pr.motion.restFadeRows pr.keys base (r.figure.name i) k }

/-- The number of problems the strict level treats as errors in the picture `P` whose report is
`r`: `r`'s errors when its level is `fail`, else those of the picture checked at `fail`. -/
def MotionPanels.strictErrors (P : MotionPanels) (r : MotionPanelsReport) : Nat :=
  if P.checks == .fail then r.errors.size
  else ({ P with checks := .fail } : MotionPanels).report.errors.size

/-- The checked motion of a picture of panels, its report (`MotionPanels.report`) and that of its
narrow rendition (`MotionPanels.narrow`) computed here: the main rendition stopped by the
picture's errors under `fail` and by `writeStops`; the narrow one also by its own errors under
`fail` and its own `writeStops`; the errors the strict level finds in each rendition that is not
stopped are the errors left (`MotionPanels.strictErrors`). It takes the picture, not a report, so
that what it says of the checks is the checks' own. -/
def MotionPanels.checked (P : MotionPanels) : CheckedMotion :=
  let r := P.report
  let narrowP := P.narrow
  let narrow := narrowP.map (·.report)
  let stops := (if r.problemsFail then r.errors else #[]) ++ r.writeStops
  let narrowStops := fun (n : MotionPanelsReport) =>
    ((if n.problemsFail then n.errors else #[]) ++ n.writeStops).map ("narrow rendition: " ++ ·)
  let narrowLeft := match narrowP, narrow with
    | some nP, some n => if (stops ++ narrowStops n).isEmpty then nP.strictErrors n else 0
    | _, _ => 0
  { title := P.info.title, keyCount := P.keyCount, stillKeys := P.stillKeys,
    captions := P.captions, poster := P.poster,
    cycle := r.timeline.cycle, style := r.style,
    textAsShapes := ((r.panels[0]?).bind fun pr => (pr.keys.figs[0]?).map (·.textAsShapes)).getD
      true,
    checks := P.checks,
    main := r.rendition stops,
    narrow := narrow.map fun n => n.rendition (narrowStops n),
    steps := r.tableRows, rests := r.restRows,
    crossfades := r.panels.any fun pr =>
      crossfadesIn pr.motion (pr.motion.versions pr.keys pr.keys.env).1 pr.motion.keys.size,
    warnings := if !stops.isEmpty then #[] else
      r.checkMessages ++ ((narrow.map (·.checkMessages.map ("narrow rendition: " ++ ·))).getD #[]),
    stops, errorsLeft := if stops.isEmpty then P.strictErrors r + narrowLeft else 0,
    animation := fun fps => if stops.isEmpty then r.animation? fps else .error stops }

/-- A picture of panels is checked by its report and that of its narrow rendition
(`MotionPanels.checked`). -/
instance : ToCheckedMotion MotionPanels where
  checked P := P.checked

/-- Pictures of panels: the outputs of `motionOutputs`, without the APNG and the GIF
(`MotionFigure` asks for them). -/
instance : ToOutputs MotionPanels where
  outputs P := motionOutputs P.checked

end PILean.Plane
