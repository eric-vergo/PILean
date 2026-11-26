/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Trust.Figure
import PILean.Plane.MotionOutput

/-!
# Motions as build outputs

A motion of plane figures (`PILean.Plane.Motion`) becomes files through a small interface: a
*checked motion* (`CheckedMotion`), computed once from the motion's checked route
(`Plane.Motion.report`), holds what every output reads: the checked animated SVG (never one of the
routes that end in `Unchecked`), the key stills as plane figures, the captions, the cycle, the
table of the steps and the problems. `ToCheckedMotion α` says how a value of `α` becomes one;
`motionOutputs` turns a checked motion into the files, so any type with such an instance is
rendered like a `Motion`.

For a motion `m` declared as `d`, with `n` keys, the files are (`docs/DESIGN.md`):

* `d.svg`: the animated SVG (`MotionReport.svg?`);
* `d-poster.png`, `d-poster.pdf`: the poster key's still;
* `d-keys.svg`, `.png`, `.pdf`: the contact sheet, every key's still in a grid with its caption
  (`CheckedMotion.sheet`), for print and PDF;
* `d-key-k.svg`, `d-key-k.png` for each key `k` from `0`: the still of key `k`; for a `Motion`,
  the key figure (`Plane.Motion.keyFigure k`) as the plane figures' pipeline draws it
  (`ExplorerFrame.ofPlane`), byte for byte the SVG and PNG of that figure;
* with a narrow rendition (`CheckedMotion.narrow`): `d-narrow.svg` and `d-narrow-key-k.svg`,
  `.png`;
* only when asked (`MotionFigure.rasters`): the APNG `d.png` and the GIF `d.gif` of the baked
  frames (`MotionReport.animation?`).

A motion whose problems stop it (`CheckLevel.fail`, the default) renders none of them: every
output fails with the messages of its errors, as a plane figure with layout problems does. Every
output records the motion (`Output.motion`: keys, cycle, captions, which the manifest writes);
the animated SVG also carries what a page needs to show it inline (`Output.motionPage`).

## Main definitions

* `MotionRendition`, `CheckedMotion`, `ToCheckedMotion`: the interface.
* `liveNodes`: the body of an animated SVG without what the standalone file adds for itself.
* `wrapText`, `sheetColumns`, `sheetOf`, `CheckedMotion.sheet`: the contact sheet.
* `stillOutputs`: the files of a still.
* `MotionFigure`, `motionOutputs`, and the instances for `Plane.Motion` and `MotionFigure`.
* `Plane.Motion.stepRows`, `Plane.MotionReport.checked`, `Plane.Motion.withStyle`.
-/

namespace PILean.Trust

open Canvas

/-! ### The interface -/

/-- One rendition of a checked motion (the motion at its width, or its narrow rendition): its
page size, the checked animated SVG document (or the messages of the errors that stop it), the
nodes of its moving picture for a page (`liveNodes` of the file's root), and the key stills as
drawings of their page size in a style (`ExplorerFrame`; for a key figure, `ExplorerFrame.ofPlane`,
which draws it as the plane figures' pipeline does). -/
structure MotionRendition where
  /-- The width in pixels. -/
  width : Float
  /-- The height in pixels. -/
  height : Float
  /-- The animated SVG document, or the messages of the errors that stop the motion. -/
  svg : Except (Array String) String
  /-- The moving picture for a page (`liveNodes` of the file's root); empty when the motion is
  stopped. -/
  live : Array Svg.Node
  /-- The still of each key, in order. -/
  stills : Array ExplorerFrame

/-- A motion checked once, as its outputs read it. A type whose values are rendered as motions
gives one (`ToCheckedMotion`); `Plane.MotionReport.checked` is the instance for one motion. -/
structure CheckedMotion where
  /-- The title of the picture (the sheet's heading). -/
  title : String
  /-- One caption per key. -/
  captions : Array String
  /-- The key shown as the poster. -/
  poster : Nat
  /-- The length of one cycle, in seconds. -/
  cycle : Rat
  /-- The style the stills and the sheet are drawn in (background, colours, text engine). -/
  style : Style
  /-- The motion at its width. -/
  main : MotionRendition
  /-- The narrow rendition, for small screens, if the motion has one. -/
  narrow : Option MotionRendition := none
  /-- The table of the steps. -/
  steps : Array MotionStepRow
  /-- The messages of the problems a build reports as warnings (empty when the motion is
  stopped). -/
  warnings : Array String
  /-- Whether the problems stop the motion from being rendered. -/
  problemsFail : Bool
  /-- The messages of the errors that stop it. -/
  errors : Array String
  /-- The motion as baked frames at a number of frames a second, or the messages of the errors
  that stop it (for the APNG and GIF, which are written only when asked). -/
  animation : Nat → Except (Array String) Animation

/-- Values that are rendered as motions: how one is checked. -/
class ToCheckedMotion (α : Type) where
  /-- The motion checked once. -/
  checked : α → CheckedMotion

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

/-- The summary every output of the checked motion records. -/
def CheckedMotion.summary (c : CheckedMotion) : MotionSummary :=
  { keys := c.main.stills.size, cycle := c.cycle, captions := c.captions.size }

/-- What a page needs to show the rendition `r` of the checked motion inline. -/
def CheckedMotion.page (c : CheckedMotion) (r : MotionRendition) : MotionData :=
  { summary := c.summary, live := InlineSvg.ofStyle r.width r.height r.live c.style,
    stills := { stepCaptions := c.captions, frames := r.stills.map (·.inline),
                poster := c.poster },
    steps := c.steps }

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
as SVG, PNG and PDF like a frame of an explorer (`ExplorerFrame`). -/
def sheetOf (title : String) (captions : Array String) (stills : Array ExplorerFrame)
    (st : Style) : ExplorerFrame :=
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
    width, height, style := st, srgb := true,
    textAsShapes := (stills[0]?.map (·.textAsShapes)).getD true }

/-- The contact sheet of the checked motion's key stills (`sheetOf`). -/
def CheckedMotion.sheet (c : CheckedMotion) : ExplorerFrame :=
  sheetOf c.title c.captions c.main.stills c.style

/-! ### The outputs -/

/-- The SVG (with its inline picture and its theme) and the PNG of a still, named with `suffix`,
and its PDF when `pdf`; for the still of a key figure (`ExplorerFrame.ofPlane`) these are byte for
byte the plane figure's SVG, PNG and PDF. -/
def stillOutputs (f : ExplorerFrame) (suffix : String) (pdf : Bool := false) : Array Output :=
  let t := f.style.text.id
  #[{ name := suffix, format := .svg, bytes := fun _ => .ok f.toSvg.toUTF8,
      spec := f.toSvg.toUTF8, textEngine := t, inline := fun _ => some f.inline,
      theme := fun _ => InlineSvg.themeOf f.style },
    { name := suffix, format := .png,
      bytes := fun _ => match f.toPng with
        | some b => .ok b
        | none => .error "the still has no pixels",
      spec := (f.toSvg (outlines := true)).toUTF8, textEngine := t }] ++
    if pdf then
      #[{ name := suffix, format := .pdf, bytes := fun _ => .ok f.toPdf,
          spec := (f.toSvg (outlines := true)).toUTF8, textEngine := t }]
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

/-- The outputs of a checked motion (see the module docstring), the APNG and the GIF only with
`rasters`, at `fps` frames a second. Every output fails with the errors of a motion that is
stopped (`CheckedMotion.problemsFail`), records the motion's summary (`Output.motion`), and the
animated SVG carries the warnings and what a page needs to show it (`Output.motionPage`). -/
def motionOutputs (c : CheckedMotion) (rasters : Bool := false) (fps : Nat := 30) :
    Array Output :=
  let ok := checkedBytes c.problemsFail (fun _ => c.errors)
  let summary := c.summary
  let mark := fun (o : Output) =>
    { o with bytes := fun _ => ok o.bytes, motion := fun _ => summary }
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
  let svgSpec := main.spec
  let raster : Array Output := if !rasters then #[] else
    #[{ name := "", format := .apng, spec := svgSpec, textEngine := t,
        bytes := fun _ => match c.animation fps with
          | .ok a => a.toApng.mapError toString
          | .error es => .error ("problems: " ++ "; ".intercalate es.toList) },
      { name := "", format := .gif, spec := svgSpec, textEngine := t,
        bytes := fun _ => match c.animation fps with
          | .ok a => a.toGif.mapError toString
          | .error es => .error ("problems: " ++ "; ".intercalate es.toList) }]
  let poster := match c.main.stills[c.poster]? with
    | some f => (stillOutputs f "-poster" (pdf := true)).filter (·.format != .svg)
    | none => #[]
  let sh := c.sheet
  let sheet : Array Output :=
    #[{ name := "-keys", format := .svg, bytes := fun _ => .ok sh.toSvg.toUTF8,
        spec := sh.toSvg.toUTF8, textEngine := t, inline := fun _ => some sh.inline,
        theme := fun _ => InlineSvg.themeOf c.style },
      { name := "-keys", format := .png,
        bytes := fun _ => match sh.toPng with
          | some b => .ok b
          | none => .error "the contact sheet has no pixels",
        spec := (sh.toSvg (outlines := true)).toUTF8, textEngine := t },
      { name := "-keys", format := .pdf, bytes := fun _ => .ok sh.toPdf,
        spec := (sh.toSvg (outlines := true)).toUTF8, textEngine := t }]
  let narrow := match c.narrow with
    | some r => #[animated "-narrow" r] ++ stills "-narrow" r
    | none => #[]
  (#[{ main with problems := fun _ => c.warnings }] ++ raster ++ poster ++ sheet ++
    stills "" c.main ++ narrow).map mark

/-- A motion with the choices of its outputs: the outputs of `motionOutputs`. -/
instance {α : Type} [ToCheckedMotion α] : ToOutputs (MotionFigure α) where
  outputs f := motionOutputs (ToCheckedMotion.checked f.motion) f.rasters f.fps

end PILean.Trust

namespace PILean.Plane

open PILean.Trust

/-- The table of the motion's steps: for each step its duration (`Motion.animStep` of the pacing,
a negative one as zero), whether it is idle, and each declared move with its centre and exact
fraction of a turn, or its vector. -/
def Motion.stepRows (m : Motion) : Array MotionStepRow :=
  m.steps.mapIdx fun j s =>
    { step := j, duration := max 0 (Motion.animStep m.pacing s).dur, idle := s.kind == .idle,
      moves := s.moves.map fun (id, mv) => match mv with
        | .turn c q => { actor := id, kind := mv.name, centre := some c, turns := some q }
        | .slide v => { actor := id, kind := mv.name, vector := some v }
        | _ => { actor := id, kind := mv.name } }

/-- The motion with every key, and every figure between two keys, drawn in the style `st`: for
the dark twin of a motion whose keys have the light colours, `Style.darkTwin?` of
`Motion.style`. -/
def Motion.withStyle (m : Motion) (st : Style) : Motion :=
  { m with keys := m.keys.map ({ · with style := st }),
           between := fun j q => (m.between j q).map ({ · with style := st }) }

/-- The style of a motion: that of its first key. -/
def Motion.style (m : Motion) : Style := (m.keys[0]?.map (·.style)).getD {}

/-- The checked motion of the report (`Motion.report`): the animated SVG of the checked route
(`MotionReport.svg?`), the body of its root for a page (`liveNodes`), the stills (the keys as
drawn, `Motion.keyFigure`, as frames of the plane figures' drawing, `ExplorerFrame.ofPlane`),
the step table, the warnings and the errors. A single motion has no narrow rendition. -/
def MotionReport.checked (r : MotionReport) : CheckedMotion :=
  let f := r.plan.env.frame
  let m := r.motion
  { title := m.info.title, captions := m.captions, poster := m.poster,
    cycle := r.plan.timeline.cycle, style := (r.keys.figure 0).style,
    main := { width := f.width.round, height := f.height.round, svg := r.svg?,
              live := if r.problemsFail then #[] else liveNodes (m.svgRootIn r.keys r.plan),
              stills := r.keys.figs.map ExplorerFrame.ofPlane },
    steps := m.stepRows,
    warnings := if r.problemsFail then #[] else r.checkMessages,
    problemsFail := r.problemsFail, errors := r.errors,
    animation := fun fps => r.animation? fps }

/-- A motion is checked by its report. -/
instance : ToCheckedMotion Motion where
  checked m := m.report.checked

/-- Motions: the outputs of `motionOutputs`, without the APNG and the GIF (`MotionFigure` asks for
them). -/
instance : ToOutputs Motion where
  outputs m := motionOutputs m.report.checked

end PILean.Plane
