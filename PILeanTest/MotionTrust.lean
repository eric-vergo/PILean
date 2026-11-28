/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Trust.Attr
import PILean.Trust.Build
import PILean.Trust.Verify
import PILeanTest.MotionFigures

/-!
# Motions as build outputs

The outputs of a motion and of a picture of panels (`PILean.Trust.Motion`): their names, formats
and order; the key stills and the poster byte for byte the files of the key figures (and of the
picture's keys, `keyStillSvg`, `keyStillPng`, at both widths); the animated SVG that of the checked
route, and its body for a page (`MotionData.live`) the file without what the file adds for itself;
the stills with their captions; the contact sheet's grid, captions, title and description; the
step table with what is drawn for each move; the page's words for each kind of move and for a
motion that is not checked strictly; a motion at each check level (stopped under `fail` with no
file, no inline picture and no page data; recorded as `warn` or `ignore` with the errors left;
a poster out of range never dropping files); ids written twice; the APNG and the GIF only when
asked; the dark style; the closed constructor of a checked motion. The record of a motion in the
source record and the manifest (format `pilean-manifest-4`): written and read back, refused when
malformed, when it does not read back, when the files of one declaration disagree or do not list
the key stills it counts; the earlier format still read. The inert scanner on what motions write.
A build of the gallery's motions into a directory under `.lake`: the files and the manifest, the
motion's own title as the accessible name, `pilean-verify` and `pilean-build --check` fresh and
after tampering with the animated SVG, a still, the sheet and the manifest's record, a forged
non-inert SVG, `--require-standing` and `--require-checked`, and a motion with errors failing the
build.
-/

namespace PILeanTest.MotionTrust

open PILean PILean.Trust PILean.Plane PILeanTest.MotionChecks

/-- Whether `t` occurs in `s`. -/
def has (s t : String) : Bool := (s.splitOn t).length > 1

/-- The text without white space, to compare markup written at different indentations. -/
def squeeze (s : String) : String := s.toList.filter (!·.isWhitespace) |> String.ofList

/-- The bytes of an output, or empty. -/
def bytesOf (o : Output) : ByteArray := match o.bytes () with
  | .ok b => b
  | .error _ => .empty

/-- The error of an output, or empty. -/
def errorOf (o : Output) : String := match o.bytes () with
  | .ok _ => ""
  | .error e => e

/-- The output of `os` with the suffix `name` and the format `f`. -/
def find (os : Array Output) (name : String) (f : Format) : Option Output :=
  os.find? fun o => o.name == name && o.format == f

/-- The page data of the animated SVG of `os`. -/
def pageOf (os : Array Output) : Option MotionData := (find os "" .svg).bind (·.motionPage ())

/-- The quarter turn whose first move misses its key by half a pixel. -/
def broken : Motion := missBy 0.5

/-- A motion at the check level `l`. -/
def atLevel (m : Motion) (l : CheckLevel) : Motion := { m with checks := l }

/-- Two actors whose ids differ but are written alike (`a b` and `a_b`). -/
def collide : Motion where
  keys := #[{ items := corners ++ #[(Plane.point ⟨1, 0⟩).actor "a b", (Plane.point ⟨2, 0⟩).actor "a_b"] },
    { items := corners ++ #[(Plane.point ⟨0, 1⟩).actor "a b", (Plane.point ⟨3, 0⟩).actor "a_b"] }]
  captions := #["Before.", "After."]
  steps := #[{ moves := #[("a b", .turn ⟨0, 0⟩ (1 / 4)), ("a_b", .slide ⟨1, 0⟩)] }]
  info := testInfo

/-- An item without an id that moves between two keys, with nothing declared. -/
def idless : Motion where
  keys := #[{ items := corners.push (Plane.point ⟨0, 0⟩) },
    { items := corners.push (Plane.point ⟨1, 0⟩) }]
  captions := #["Before.", "After."]
  steps := #[MotionStep.idle]
  info := testInfo

/-- Two keys alike and an idle step. -/
def still : Motion where
  keys := #[{ items := corners }, { items := corners }]
  captions := #["Before.", "After."]
  steps := #[MotionStep.idle]
  info := testInfo

/-- The texts of the `text` elements at the top of a drawing (not inside its groups), in order. -/
def top : Canvas.Shape → Array String
  | .group cs .. => cs.filterMap fun
    | .text s .. => some s
    | _ => none
  | _ => #[]

/-- The animated SVG file of a motion, rebuilt from its parts: the title, the description, the
reduced-motion style, the nodes a page puts inline (`live`) and the poster group of the poster
key's still. -/
def rebuilt (m : Motion) (live : InlineSvg) : String :=
  let w := live.width
  let h := live.height
  let poster := (m.keyFigure m.poster).svgNodes.map (prefixIds "poster-" 256)
  let head := #[Svg.el "title" #[] #[.text m.info.title],
    Svg.el "desc" #[] #[.text m.description]]
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++ Svg.render 0
    (Svg.el "svg" #[("xmlns", "http://www.w3.org/2000/svg"), ("width", fmtNum w),
      ("height", fmtNum h), ("viewBox", s!"0 0 {fmtNum w} {fmtNum h}"), ("role", "img")]
      (head ++ #[Animation.reducedMotionStyle] ++ live.nodes ++
        #[Svg.el "g" #[("class", Animation.posterClass)] poster])) ++ "\n"

/-- The record of a strictly checked motion of `n` keys with the cycle `c`. -/
def strict (n : Nat) (c : Rat) : MotionSummary := { keys := n, cycle := c, captions := n }

/-- The checks of the outputs of one golden motion. -/
def outputChecks (name : String) (m : Motion) : Array (String × Bool) :=
  let os := ToOutputs.outputs m
  let n := m.keys.size
  let r := m.report
  let svg := match r.svg? with | .ok s => s | .error _ => ""
  let main := find os "" .svg
  let page := pageOf os
  let ks := m.stillKeys
  let summary := { strict n r.plan.timeline.cycle with
    stills := if ks.size == n then none else some ks }
  let keyNames := ks.toList.flatMap fun k => [s!"svg-key-{k}", s!"png-key-{k}"]
  #[(s!"motion outputs {name}: the files, in order",
      os.toList.map (fun o => o.format.name ++ o.name) ==
        ["svg", "png-poster", "pdf-poster", "svg-keys", "png-keys", "pdf-keys"] ++ keyNames),
    (s!"motion outputs {name}: every output renders and records the motion, checked strictly",
      os.all fun o => (o.bytes ()).toOption.isSome && o.motion () == some summary),
    (s!"motion outputs {name}: the animated SVG is the checked route's, and its specification",
      main.all fun o => bytesOf o == svg.toUTF8 && o.spec == svg.toUTF8 && !svg.isEmpty),
    (s!"motion outputs {name}: each key still is the key figure's SVG and PNG, byte for byte",
      ks.all fun k =>
        (find os s!"-key-{k}" .svg).all (bytesOf · == (m.keyFigure k).toSvg.toUTF8) &&
        (find os s!"-key-{k}" .png).all (bytesOf · == ((m.keyFigure k).toPng).getD .empty)),
    (s!"motion outputs {name}: the poster is the poster key's PNG and PDF",
      (find os "-poster" .png).all (bytesOf · == ((m.keyFigure m.poster).toPng).getD .empty) &&
        (find os "-poster" .pdf).all (bytesOf · == (m.keyFigure m.poster).toPdf)),
    (s!"motion outputs {name}: every SVG output is inert",
      os.all fun o => o.format != .svg || (String.fromUTF8? (bytesOf o)).any Svg.isInert),
    (s!"motion outputs {name}: the page data records the motion, checked strictly",
      page.any fun d => d.summary == summary && d.steps.size == m.steps.size && !d.unchecked &&
        d.checkWords.isNone),
    (s!"motion outputs {name}: the file is the inline body with its title, description, \
        reduced-motion style and poster group put back",
      page.any fun d => rebuilt m d.live == svg),
    (s!"motion outputs {name}: the inline body is inert and holds no style and no poster",
      page.any fun d => Svg.isInert d.live.document && !has d.live.document "<style" &&
        !has d.live.document Animation.posterClass && has d.live.document Animation.liveClass),
    (s!"motion outputs {name}: the inline body carries the theme the manifest records",
      match main, page with
      | some o, some d => d.live.darkColours == (o.theme ()).1 && !d.live.darkColours.isEmpty
      | _, _ => false),
    (s!"motion outputs {name}: the stills are the key stills' pictures, with the captions",
      page.any fun d => d.stills.frames.size == ks.size &&
        d.stills.stepCaptions == m.stillCaptions && d.stillKeys == ks &&
        ks[d.stills.poster]? == some m.poster && d.stills.poster < d.stills.frames.size &&
        (ks.zipIdx.all fun (k, i) =>
          (d.stills.frames[i]?.map (·.document.toUTF8)) == some (m.keyFigure k).toSvg.toUTF8)),
    (s!"motion outputs {name}: the sheet's SVG is its inline picture, inert, with a title and a \
        description listing the captions",
      (find os "-keys" .svg).any fun o =>
        let t := String.fromUTF8! (bytesOf o)
        (o.inline ()).any (·.document.toUTF8 == bytesOf o) && Svg.isInert t &&
          has t s!"<title>{m.info.title}: key frames</title>" &&
          has t s!"<desc>{" ".intercalate m.stillCaptions.toList}</desc>"),
    (s!"motion outputs {name}: the sheet's PDF passes the structural check",
      (find os "-keys" .pdf).any fun o => (Pdf.check (bytesOf o)).toOption.isSome),
    (s!"motion outputs {name}: only the animated SVG reports the warnings",
      (os.filter fun o => o.name != "" || o.format != .svg).all fun o => (o.problems ()).isEmpty),
    (s!"motion outputs {name}: the checked motion is the report's",
      let c := ToCheckedMotion.checked m
      c.stopped == r.problemsFail && c.errorsLeft == 0 && c.summary == summary)]

/-- The outputs of the golden picture of panels, at both widths. -/
def panelChecks : Array (String × Bool) :=
  let P := PILeanTest.MotionPanelsChecks.framesPanels
  let r := P.report
  let nr := (P.narrow.map (·.report)).getD r
  let os := ToOutputs.outputs P
  let n := P.keyCount
  let svg := match r.svg? with | .ok s => s | .error _ => ""
  let nsvg := match nr.svg? with | .ok s => s | .error _ => ""
  let keyNames := fun (pre : String) =>
    (List.range n).flatMap fun k => [s!"svg{pre}-key-{k}", s!"png{pre}-key-{k}"]
  let page := pageOf os
  let npage := (find os "-narrow" .svg).bind (·.motionPage ())
  let rows := page.map (·.steps) |>.getD #[]
  #[("panels outputs: the files, in order, with the narrow rendition",
      os.toList.map (fun o => o.format.name ++ o.name) ==
        ["svg", "png-poster", "pdf-poster", "svg-keys", "png-keys", "pdf-keys"] ++ keyNames "" ++
          ["svg-narrow"] ++ keyNames "-narrow"),
    ("panels outputs: every output renders and records the picture",
      os.all fun o => (o.bytes ()).toOption.isSome &&
        o.motion () == some { strict n r.timeline.cycle with narrow := true }),
    ("panels outputs: the animated SVGs are the checked routes' at both widths",
      (find os "" .svg).any (bytesOf · == svg.toUTF8) && !svg.isEmpty &&
        (find os "-narrow" .svg).any (bytesOf · == nsvg.toUTF8) && !nsvg.isEmpty),
    ("panels outputs: each key still is the picture's key, SVG and PNG, byte for byte, at both \
        widths",
      (List.range n).all fun k =>
        (find os s!"-key-{k}" .svg).all (bytesOf · == (r.keyStillSvg k).toUTF8) &&
        (find os s!"-key-{k}" .png).all (bytesOf · == (r.keyStillPng k).getD .empty) &&
        (find os s!"-narrow-key-{k}" .svg).all (bytesOf · == (nr.keyStillSvg k).toUTF8) &&
        (find os s!"-narrow-key-{k}" .png).all (bytesOf · == (nr.keyStillPng k).getD .empty)),
    ("panels outputs: every SVG output is inert",
      os.all fun o => o.format != .svg || (String.fromUTF8? (bytesOf o)).any Svg.isInert),
    ("panels outputs: the inline bodies are in their files, inert, with no style and no poster",
      match page, npage with
      | some d, some nd =>
        [(d, svg), (nd, nsvg)].all fun (d, s) =>
          d.live.nodes.all (fun x => has (squeeze s) (squeeze (Svg.render 0 x))) && Svg.isInert d.live.document &&
            !has d.live.document "<style" && !has d.live.document Animation.posterClass
      | _, _ => false),
    ("panels outputs: the stills of a page are the files' pictures with the captions",
      page.any fun d => d.stills.frames.size == n && d.stills.stepCaptions == P.captions &&
        (List.range n).all fun k =>
          (d.stills.frames[k]?.map (·.document)) == some (r.keyStillSvg k)),
    ("panels outputs: the step table has every panel's moves, named by its panel",
      rows.size == r.stepRows.size &&
        (rows.zip r.stepRows).all (fun (a, b) => a.moves.size == b.moves.size) &&
        rows.all (·.moves.all fun mv => mv.panel == "The point turns" ||
          mv.panel == "The centres turn") && rows.all (·.moves.all (·.asDeclared))),
    ("panels outputs: the checked picture is the report's",
      let c := ToCheckedMotion.checked P
      c.stopped == r.problemsFail && c.errorsLeft == 0 && c.narrow.isSome &&
        c.summary.narrow),
    ("panels outputs: the dark style draws every file",
      (P.style.darkTwin?.map fun d => (ToOutputs.outputs (P.withStyle d)).all
        fun o => (o.bytes ()).toOption.isSome) == some true)]

/-- The contact sheet: its grid, the stills in it and the captions below them. -/
def sheetChecks : Array (String × Bool) :=
  let m := twoCentresMotion
  let c := m.checked
  let sh := c.sheet
  let w := (m.keyFigure 0).autoPlaced.frame.width.round
  let plain := sheetOf c.title c.captions c.main.stills c.style (textAsShapes := false)
  let st := c.style
  let lines := c.captions.map (wrapText st.text sheetCaptionSize w ·)
  #[("motion sheet: the number of columns fills the rows evenly within the widest sheet",
      sheetColumns 3 320 == 2 && sheetColumns 4 360 == 2 && sheetColumns 1 900 == 1 &&
        sheetColumns 5 200 == 3 && sheetColumns 4 200 == 2 && sheetColumns 0 300 == 1 &&
        sheetColumns 7 100 == 4 && sheetColumns 9 100 == 5),
    ("motion sheet: two columns of stills, framed, with room around them",
      sh.width == sheetGap + 2 * (w + sheetGap)),
    ("motion sheet: every still is drawn, at its grid position",
      match sh.drawing with
      | .group cs .. =>
        let placed := cs.filterMap fun
          | .group _ t .. => some (t.e, t.f)
          | _ => none
        placed.size == 4 && placed.map (·.1) == #[sheetGap, 2 * sheetGap + w, sheetGap,
          2 * sheetGap + w] && placed[0]!.2 == placed[1]!.2 && placed[2]!.2 > placed[0]!.2
      | _ => false),
    ("motion sheet: the title and every caption are written, wrapped to the width of a still",
      top plain.drawing == #[c.title] ++ lines.flatten &&
        lines.all (·.all fun l => st.text.measure l sheetCaptionSize ≤ w) &&
        (c.captions.zip lines).all fun (cap, ls) => " ".intercalate ls.toList == cap),
    ("motion sheet: a caption wider than a still is wrapped in words",
      let ws := wrapText st.text sheetCaptionSize 80 "one two three four five six"
      ws.size > 1 && " ".intercalate ws.toList == "one two three four five six" &&
        (wrapText st.text sheetCaptionSize 10 "unbreakable").toList == ["unbreakable"]),
    ("motion sheet: a single key makes a sheet of one still",
      (sheetOf "" #["Only."] #[MotionStill.ofFrame (ExplorerFrame.ofPlane (m.keyFigure 0))]
        st).width == 2 * sheetGap + w)]

/-- The step table and the page's words. -/
def wordChecks : Array (String × Bool) :=
  let rows := twoCentresMotion.stepRows
  let words := rows.map (·.moves.map (·.words))
  let between := fun (m : Motion) => ((pageOf (ToOutputs.outputs m)).map (·.betweenWords)).getD ""
  let quarter := "turn about (0, 0) by 1/4 of a full turn (90°)"
  #[("motion steps: one row per step, with its duration in seconds, exactly",
      rows.size == 3 && rows.map (·.duration) == #[1, 1, 4 / 5] && rows.all (!·.idle)),
    ("motion steps: each move with its actor, kind, centre and exact fraction of a turn",
      words == #[#[quarter, quarter, quarter, quarter],
        #["turn about (1, 1) by 1/2 of a full turn (180°)", "appearance"], #["slide by (1, 0)"]] &&
        rows.map (·.moves.map (·.actor)) == #[#["A", "T1", "T2", "T3"], #["A", "B"], #["S"]] &&
        rows.all (·.moves.all (·.asDeclared))),
    ("motion steps: an idle step takes the pacing's idle time and has no move",
      turnMotion.stepRows.map (fun r => (r.idle, r.duration, r.moves.size)) ==
        #[(false, 1, 1), (true, 9 / 10, 0)]),
    ("motion steps: a turn's degrees are exact",
      turnDegreesWords (1 / 7) == "360/7°" && turnDegreesWords (-1 / 4) == "-90°"),
    ("motion page: the words of a quarter turn",
      ((pageOf (ToOutputs.outputs turnMotion)).map (·.words)) ==
        some "An animation drawn from 3 key frames; the stills are the key figures as drawn. \
          Between key frames the browser turns drawn items about the stated centres."),
    ("motion page: turns, slides and an appearance",
      between twoCentresMotion == "Between key frames the browser turns drawn items about the \
        stated centres, slides drawn items along the stated vectors and fades items in or out."),
    ("motion page: a morph",
      between (morphMotion true) == "Between key frames the browser changes the outlines of \
        drawn items."),
    ("motion page: an item without an id that changes",
      between idless == "Between key frames the browser crossfades items that change without a \
        declared move."),
    ("motion page: nothing moves", between still == "Nothing moves between the key frames."),
    ("motion page: a theorem about a motion states its key figures and its declared moves",
      has motionLinkedWords "its key figures and its declared moves")]

/-- A motion at each check level, ids written twice, the APNG and the GIF on request, the dark
style. -/
def routeChecks : Array (String × Bool) :=
  let bad := ToOutputs.outputs broken
  let warned := ToOutputs.outputs (atLevel broken .warn)
  let ignored := ToOutputs.outputs (atLevel broken .ignore)
  let cleanWarn := ToOutputs.outputs (atLevel turnMotion .warn)
  let farPoster := ToOutputs.outputs { (atLevel turnMotion .ignore) with poster := 7 }
  let clash := ToOutputs.outputs collide
  let rasters := ToOutputs.outputs ({ motion := turnMotion, rasters := true, fps := 10 } :
    MotionFigure Motion)
  let turnSvg := match turnMotion.svg? with | .ok s => s.toUTF8 | .error _ => .empty
  let darkStyle := turnMotion.style.darkTwin?
  let dark := darkStyle.map fun d => turnMotion.withStyle d
  let crossRow := fun (os : Array Output) =>
    ((pageOf os).bind fun d => (d.steps[0]?).bind (·.moves[0]?)).any fun r =>
      r.drawn == "crossfade" && has r.words "drawn as a crossfade"
  #[("motion fail: every output of a motion with errors fails with the messages of its errors",
      !bad.isEmpty && !broken.report.errors.isEmpty && bad.all fun o =>
        errorOf o == "problems: " ++ "; ".intercalate broken.report.errors.toList),
    ("motion fail: a stopped motion gives no animated SVG, no page data, no inline picture and \
        no theme",
      (find bad "" .svg).all (·.spec.isEmpty) && bad.all fun o =>
        (o.motionPage ()).isNone && (o.inline ()).isNone && (o.theme ()).1.isEmpty),
    ("motion warn: it renders, records the level and the errors left, and its page says so",
      warned.all (fun o => (o.bytes ()).toOption.isSome &&
          (o.motion ()).any fun mo => mo.checks == "warn" && mo.errorsLeft == 1) &&
        (find warned "" .svg).any (fun o => !(o.problems ()).isEmpty) &&
        (pageOf warned).any fun d => d.unchecked && (d.checkWords.any (has · "errors")) &&
          has d.words "not what the steps declare"),
    ("motion warn and ignore: the step table says the missed move is drawn as a crossfade, and \
        so does the page",
      crossRow warned && crossRow ignored && (pageOf warned).any fun d =>
        has d.betweenWords "crossfades items whose declared move does not land"),
    ("motion ignore: it renders and records the level and the errors left, reporting nothing",
      ignored.all (fun o => (o.bytes ()).toOption.isSome && (o.problems ()).isEmpty &&
        (o.motion ()).any fun mo => mo.checks == "ignore" && mo.errorsLeft == 1)),
    ("motion warn without errors: recorded as warn, and the page says what that level means",
      cleanWarn.all (fun o => (o.motion ()).any fun mo => mo.checks == "warn" && mo.errorsLeft == 0) &&
        (pageOf cleanWarn).any fun d => d.unchecked &&
          d.checkWords.any (has · "the strict level finds no error")),
    ("motion warn: a problem the strict level treats as an error is counted as left, though warn \
        makes it a note",
      let os := ToOutputs.outputs (atLevel { turnMotion with info := {} } .warn)
      os.all (fun o => (o.motion ()).any (·.errorsLeft == 1)) &&
        (pageOf os).any fun d => d.checkWords.any (has · "1 problem that the strict level")),
    ("panels fail: errors of the narrow rendition alone stop it, are not counted as left, and \
        fail its files",
      let P : MotionPanels := { PILeanTest.MotionPanelsChecks.framesPanels with
        narrowWidth := some 80 }
      let os := ToOutputs.outputs P
      (P.narrow.any fun n => n.report.problemsFail) && !P.report.problemsFail &&
        (find os "" .svg).any (fun o => (o.bytes ()).toOption.isSome) &&
        (find os "-narrow" .svg).any (fun o => has (errorOf o) "narrow rendition: ") &&
        os.all fun o => (o.motion ()).any fun mo => mo.strict && mo.narrow),
    ("motion page: a move that does not land is one crossfade, not also an undeclared change",
      (pageOf warned).any fun d => !d.crossfades &&
        !has d.betweenWords "change without a declared move"),
    ("motion ignore: a poster out of range stops every output, dropping none silently",
      farPoster.size == (ToOutputs.outputs turnMotion).size &&
        farPoster.all fun o => has (errorOf o) "the poster is key 7" &&
          (o.motionPage ()).isNone),
    ("motion ids: actors written alike stop every output, naming them",
      !clash.isEmpty && clash.all fun o => has (errorOf o) "more than once (the actors a b, a_b"),
    ("motion rasters: the APNG and the GIF only when asked, of the animated SVG's specification",
      (rasters.toList.map (fun o => o.format.name ++ o.name)).take 3 == ["svg", "apng", "gif"] &&
        (find rasters "" .apng).any (fun o => o.spec == turnSvg &&
          detectedFormat? (bytesOf o) == some "apng") &&
        (find rasters "" .gif).any (fun o => detectedFormat? (bytesOf o) == some "gif") &&
        !(ToOutputs.outputs turnMotion).any (fun o => o.format == .apng || o.format == .gif)),
    ("motion dark: the motion in the dark style draws its stills and sheet in it",
      dark.any fun dm =>
        let os := ToOutputs.outputs dm
        let bg := (darkStyle.map (·.background.rgbHex)).getD ""
        os.all (fun o => (o.bytes ()).toOption.isSome) &&
          (find os "-key-0" .svg).any (fun o => bytesOf o == (dm.keyFigure 0).toSvg.toUTF8 &&
            has (String.fromUTF8! (bytesOf o)) bg) &&
          (find os "-keys" .svg).any (fun o => has (String.fromUTF8! (bytesOf o)) bg)),
    ("motion checked: the checked motion of a stopped motion is stopped, of a warned one not",
      (ToCheckedMotion.checked broken).stopped &&
        !(ToCheckedMotion.checked (atLevel broken .warn)).stopped &&
        (ToCheckedMotion.checked (atLevel broken .warn)).errorsLeft == 1)]

/-- A timeline its writer divided unsoundly, put into the reports of a motion and of a picture of
panels: it stops them at every check level (no SVG, no animation, what stops them its message
only), where an ordinary error stops them under `fail` only. -/
def unsoundChecks : Array (String × Bool) :=
  let bad : Anim.SegKind := .move 0
  let msgs := (unsoundProblems #[bad]).map (·.message)
  let levels := #[CheckLevel.fail, .warn, .ignore]
  let motionAt := fun (l : CheckLevel) =>
    let r := (atLevel turnMotion l).report
    { r with unsound := #[bad], problems := r.problems ++ unsoundProblems #[bad] }
  let panelsAt := fun (l : CheckLevel) =>
    let r := ({ PILeanTest.MotionPanelsChecks.framesPanels with checks := l } : MotionPanels).report
    { r with unsound := #[bad], problems := r.problems ++ unsoundProblems #[bad] }
  let erred := fun (l : CheckLevel) =>
    let r := (atLevel turnMotion l).report
    { r with problems := r.problems.push { severity := .error, message := "an error" } }
  #[("motion unsound: the writer divides the timelines of the motions tested soundly",
      turnMotion.report.unsound.isEmpty &&
        PILeanTest.MotionPanelsChecks.framesPanels.report.unsound.isEmpty),
    ("motion unsound: a timeline divided unsoundly stops a motion at every level, with its \
        message",
      levels.all fun l =>
        let r := motionAt l
        r.problemsFail && r.svg?.toOption.isNone && (r.animation? 10).toOption.isNone &&
          r.toAnimationUnchecked.problemsFail && r.stopErrors == msgs && r.stops == msgs),
    ("motion unsound: an ordinary error stops a motion under fail only",
      (erred .fail).problemsFail && !(erred .fail).stops.isEmpty &&
        #[CheckLevel.warn, .ignore].all fun l =>
          !(erred l).problemsFail && (erred l).svg?.toOption.isSome && (erred l).stops.isEmpty),
    ("panels unsound: a shared timeline divided unsoundly stops a picture of panels at every \
        level, with its message",
      levels.all fun l =>
        let r := panelsAt l
        r.problemsFail && r.svg?.toOption.isNone && (r.animation? 10).toOption.isNone &&
          r.stopErrors == msgs && r.stops == msgs)]

/-- A manifest entry of a motion's file. -/
def motionEntry (path : String) (motion : Option MotionSummary) : ManifestEntry :=
  { path, format := if path.endsWith ".png" then "png" else "svg", bytes := 1,
    sha256 := String.ofList (List.replicate 64 'a'),
    fingerprint := String.ofList (List.replicate 64 'b'), module := "M", decl := "M.d",
    file := "M.lean", line := 1, column := 0, version := "0.1.0", standing := some "illustration",
    motion }

/-- The record of a motion, in a source record and in the manifest. -/
def recordChecks : Array (String × Bool) :=
  let mo : MotionSummary := { keys := 1, cycle := 59 / 10, captions := 1 }
  let es := #[motionEntry "M/d.svg" (some mo), motionEntry "M/d-key-0.png" (some mo),
    motionEntry "M/d-key-0.svg" (some mo)]
  let text := Manifest.render es
  let parsed := (Manifest.parse text.toUTF8).toOption
  let edit := fun (a b : String) => Manifest.parse (text.replace a b).toUTF8
  let refused := fun (a b : String) => (edit a b) matches .error _
  let warnRecord : MotionSummary := { mo with checks := "warn", errorsLeft := 2 }
  let narrowRecord : MotionSummary := { mo with narrow := true }
  let narrowEs := #[motionEntry "M/d-narrow.svg" (some mo), motionEntry "M/d-narrow-key-0.png"
    (some mo), motionEntry "M/d-narrow-key-0.svg" (some mo)]
  let src : Source :=
    { module := "M", decl := "M.d", file := "M.lean", line := 1, column := 0, version := "0.1.0",
      motion := some warnRecord }
  #[("motion record: the format is pilean-manifest-4", manifestFormat == "pilean-manifest-4"),
    ("motion record: the text of a record, read back",
      mo.text == "keys=1;cycle=59/10;captions=1;checks=fail;errorsLeft=0;narrow=no" &&
        MotionSummary.ofText? mo.text == some mo && mo.strict && !warnRecord.strict &&
        MotionSummary.ofText? "keys=3;cycle=6;captions=3;checks=ignore;errorsLeft=2;narrow=yes" ==
          some { keys := 3, cycle := 6, captions := 3, checks := "ignore", errorsLeft := 2,
                 narrow := true }),
    ("motion record: a malformed record is refused",
      ["keys=1;cycle=59/10;captions=1;checks=fail;errorsLeft=0",
        "keys=0;cycle=1;captions=1;checks=fail;errorsLeft=0;narrow=no",
        "keys=1;cycle=2/4;captions=1;checks=fail;errorsLeft=0;narrow=no",
        "keys=1;cycle=1;captions=1;checks=never;errorsLeft=0;narrow=no",
        "keys=1;cycle=1;captions=1;checks=fail;errorsLeft=0;narrow=maybe",
        "keys=1;cycle=1;captions=1;checks=fail;errorsLeft=1;narrow=no",
        "keys=1;cycle=1;captions=1;checks=warn;errorsLeft=01;narrow=no",
        "cycle=1;keys=1;captions=1;checks=fail;errorsLeft=0;narrow=no",
        "keys=1;cycle=1;captions=1;checks=fail;unchecked=no;narrow=no", ""].all
        (MotionSummary.ofText? · |>.isNone)),
    ("motion record: a cycle the reader cannot read back cannot be recorded",
      !({ mo with cycle := 1 / (10 ^ 19 : Nat) } : MotionSummary).recordable &&
        (({ src with motion := some { mo with cycle := 1 / (10 ^ 19 : Nat) } } : Source).validate
          matches .error _) && mo.recordable),
    ("motion record: in every format's source record, written and read back",
      let svg := withSourceSvg "<svg xmlns=\"http://www.w3.org/2000/svg\"/>" src
      (svg.toOption.bind fun t => (Source.read? t.toUTF8).toOption) == some src),
    ("motion record: the manifest writes it after the standing",
      has text "\"standing\":\"illustration\",\"kind\":\"motion\",\"keys\":1,\"cycle\":\"59/10\",\
        \"captions\":1,\"checks\":\"fail\",\"errorsLeft\":0,\"narrow\":false}"),
    ("motion record: written to the manifest and read back", parsed == some es),
    ("motion record: a whole cycle is written without a denominator",
      cycleText 6 == "6" && cycleText (59 / 10) == "59/10" && cycleOfText? "6" == some 6),
    ("motion record: a cycle not in lowest terms, signed, with a leading zero, a zero \
        denominator or other characters is refused",
      ["2/4", "-1", "06", "1/0", "1/1", "1.5", "", "/2", "1/", "1/2/3", " 1", "1e3",
        "1234567890123456789"].all (cycleOfText? · |>.isNone)),
    ("motion record: malformed keys of a motion in the manifest are refused",
      refused "\"cycle\":\"59/10\"" "\"cycle\":\"118/20\"" &&
        refused "\"kind\":\"motion\"" "\"kind\":\"film\"" &&
        refused "\"kind\":\"motion\"," "" &&
        refused "\"keys\":1," "" &&
        refused "\"keys\":1" "\"keys\":0" &&
        refused "\"captions\":1" "\"captions\":\"1\"" &&
        refused "\"cycle\":\"59/10\"" "\"cycle\":59" &&
        refused "\"checks\":\"fail\"" "\"checks\":\"never\"" &&
        refused "\"narrow\":false" "\"narrow\":\"no\"" &&
        refused "\"errorsLeft\":0" "\"errorsLeft\":1" &&
        refused "\"errorsLeft\":0," ""),
    ("motion record: a key the format does not have is refused",
      refused "\"kind\":\"motion\"" "\"kind\":\"motion\",\"speed\":2" &&
        refused "\"path\"" "\"extra\":1,\"path\""),
    ("motion record: the files of one declaration must record the same motion",
      (Manifest.parse (Manifest.render (es.modify 1 ({ · with motion := some warnRecord }))).toUTF8)
        matches .error _ &&
      (Manifest.parse (Manifest.render (es.modify 1 ({ · with motion := none }))).toUTF8)
        matches .error _),
    ("motion record: the files of a motion must list exactly the key stills it counts",
      let twoKeys : MotionSummary := { mo with keys := 2 }
      let two := es.map ({ · with motion := some twoKeys })
      (Manifest.parse (Manifest.render two).toUTF8) matches .error _ &&
      (Manifest.parse (Manifest.render (es.pop)).toUTF8) matches .error _ &&
      (Manifest.parse (Manifest.render (es.push (motionEntry "M/d-key-1.svg" (some mo)))).toUTF8)
        matches .error _ &&
      (Manifest.parse (Manifest.render (es.map ({ · with motion := some narrowRecord }))).toUTF8)
        matches .error _ &&
      (Manifest.parse (Manifest.render ((es ++ narrowEs).map
        ({ · with motion := some narrowRecord }))).toUTF8).toOption.isSome &&
      (Manifest.parse (Manifest.render (es ++ narrowEs)).toUTF8) matches .error _ &&
      keyStillOf? "A/b-narrow-key-12.png" == some ("A/b-narrow", 12) &&
        keyStillOf? "A/b-keys.svg" == none),
    ("motion record: a manifest of the previous format is read, without motions",
      (edit manifestFormat previousManifestFormat).toOption ==
        some (es.map ({ · with motion := none }))),
    ("motion record: an unknown format is refused, so an older reader refuses this one",
      refused manifestFormat "pilean-manifest-5")]

/-- What the inert scanner says of what motions write. -/
def inertChecks : Array (String × Bool) :=
  let doc := fun (body : String) => "<svg xmlns=\"http://www.w3.org/2000/svg\">" ++ body ++ "</svg>"
  let turn := "<g data-pilean-actor=\"P\" data-pilean-anchor=\"1 2\"><animateTransform \
    attributeName=\"transform\" type=\"rotate\" values=\"0 160 120;0 160 120;-90 160 120\" \
    keyTimes=\"0;0.2;1\" calcMode=\"spline\" keySplines=\"0 0 1 1;0.42 0 0.58 1\" dur=\"5.9s\" \
    begin=\"0s\" repeatCount=\"indefinite\" fill=\"freeze\"/></g>"
  let fade := "<g opacity=\"0\"><animate attributeName=\"opacity\" values=\"0;1;1\" \
    keyTimes=\"0;0.5;1\" calcMode=\"discrete\" dur=\"2s\" begin=\"0s\" \
    repeatCount=\"indefinite\"/></g>"
  let upright := "<g data-pilean-upright=\"3 4\"><animateTransform attributeName=\"transform\" \
    type=\"translate\" values=\"0 0;1 0\" dur=\"1s\" begin=\"0s\" repeatCount=\"indefinite\"/></g>"
  let withEvent := fun (attr : String) =>
    doc ("<g><animateTransform attributeName=\"transform\" type=\"rotate\" values=\"0;90\" \
      dur=\"1s\" " ++ attr ++ " repeatCount=\"indefinite\"/></g>")
  #[("motion inert: turns with keyTimes, keySplines, calcMode and repeatCount are accepted",
      Svg.isInert (doc turn)),
    ("motion inert: opacity animations and data-pilean attributes are accepted",
      Svg.isInert (doc (fade ++ upright))),
    ("motion inert: the standalone file's style element is accepted",
      Svg.isInert (doc ("<style>.pilean-motion-poster{display:none}@media \
        (prefers-reduced-motion: reduce){.pilean-motion-poster{display:inline}\
        .pilean-motion-live{visibility:hidden;opacity:0}}</style>" ++ turn))),
    ("motion inert: a turn that an event starts or ends is refused",
      ["begin=\"click\"", "begin=\"0s;click\"", "begin=\"live.mouseover\"", "end=\"click\"",
        "end=\"focusin\"", "begin=\"accessKey(a)\"", "begin=\"poster.end\"",
        "begin=\"a.begin+1s\"", "BEGIN=\"click\"", "begin=\"&#99;lick\""].all fun a =>
        !Svg.isInert (withEvent a)),
    ("motion inert: a turn on the clock is accepted",
      ["begin=\"0s\"", "begin=\"0s\" end=\"indefinite\"", "begin=\"-1.5s\""].all fun a =>
        Svg.isInert (withEvent a)),
    ("motion ids: the scan finds the ids written twice, each once",
      duplicateIds "<g id=\"a\"/><g id=\"b\"/><g id=\"a\"/><g id=\"a\"/>" == #["a"] &&
        (duplicateIds "<g id=\"a\"/><g data-id=\"a\"/>").isEmpty)]

/-! ### Forgeries that do not compile

A checked motion is made only from a motion or a picture of panels (`Motion.checked`,
`MotionPanels.checked`): its constructor is private, and no function takes a report, so a report
with its problems removed cannot be turned into one. -/

/-- error: invalid {...} notation, constructor for `CheckedMotion` is marked as private -/
#guard_msgs in
example (c : CheckedMotion) : CheckedMotion := { c with stops := #[], errorsLeft := 0 }

/-- error: Invalid `⟨...⟩` notation: Constructor for `PILean.Trust.CheckedMotion` is marked as
private -/
#guard_msgs in
example (c : CheckedMotion) : CheckedMotion :=
  ⟨c.title, c.captions, c.poster, c.cycle, c.style, c.textAsShapes, c.checks, c.main, c.narrow,
    c.steps, c.crossfades, c.warnings, #[], 0, c.animation⟩

/-- error: Unknown constant `PILean.Trust.CheckedMotion.mk` -/
#guard_msgs in
example (c : CheckedMotion) : CheckedMotion :=
  CheckedMotion.mk c.title c.captions c.poster c.cycle c.style c.textAsShapes c.checks c.main
    c.narrow c.steps c.crossfades c.warnings #[] 0 c.animation

/--
error: Invalid field `checked`: The environment does not contain `PILean.Plane.MotionReport.checked`, so it is not possible to project the field `checked` from an expression
  r
of type `MotionReport`
-/
#guard_msgs in
example (m : Motion) : CheckedMotion :=
  let r : MotionReport := { m.report with problems := #[] }
  r.checked

/--
error: Invalid field `checked`: The environment does not contain `PILean.Plane.MotionPanelsReport.checked`, so it is not possible to project the field `checked` from an expression
  r
of type `MotionPanelsReport`
-/
#guard_msgs in
example (P : MotionPanels) : CheckedMotion :=
  let r : MotionPanelsReport := { P.report with problems := #[] }
  r.checked

/-- The checks that need no files. -/
def checks : Array (String × Bool) :=
  (golden.flatMap fun (n, m) => outputChecks n m) ++ panelChecks ++ sheetChecks ++ wordChecks ++
    routeChecks ++ unsoundChecks ++ recordChecks ++ inertChecks ++
    #[("renderer: the identity covers the motions, the panels and their outputs",
        ["PILean.Anim.Timeline", "PILean.Anim.Smil", "PILean.Plane.Motion",
          "PILean.Plane.MotionPlan", "PILean.Plane.MotionOutput", "PILean.Plane.MotionPanels",
          "PILean.Trust.Motion"].all (rendererSources.map (·.1)).contains)]

/-- The figure entries of the gallery's motions, as `figures%` gives them. -/
def entries : Array FigureEntry :=
  (figures% : Array FigureEntry).filter (·.module == "PILeanTest.MotionFigures")

/-- An entry of a motion that is not a registered figure, with the standing `s`. -/
def entryOf (decl : String) (m : Motion) (s : Standing) : FigureEntry :=
  { module := "PILeanTest.MotionTrust", decl := s!"PILeanTest.MotionTrust.{decl}",
    file := "PILeanTest/MotionTrust.lean", line := 1, column := 0,
    sourceHash := String.ofList (List.replicate 64 '0'),
    outputs := fun _ => withStanding s (ToOutputs.outputs m) }

/-- The result of `verifyDir`, as a list of `verdict path` words, or `error`. -/
def verdicts (dir : System.FilePath) : IO (List String) := do
  match ← verifyDir dir with
  | .ok vs => return vs.toList.map fun (p, v) => v.text ++ " " ++ p
  | .error _ => return ["error"]

/-- The report of `checkLines` of the directory for the entries. -/
def checkReport (es : Array FigureEntry) (dir : System.FilePath) : IO (List String) := do
  match ← renderAll es {} with
  | .ok files =>
    return (← checkLines files (Manifest.render (files.map (·.entry))).toUTF8 dir).toList
  | .error e => return [e]

/-- Flips the first byte of a file, runs `act`, and puts the byte back. -/
def tampered {α : Type} (p : System.FilePath) (act : IO α) : IO α := do
  let b ← IO.FS.readBinFile p
  IO.FS.writeBinFile p (b.set! 0 (b.get! 0 ^^^ 1))
  let r ← act
  IO.FS.writeBinFile p b
  return r

/-- Writes the manifest `ms` into `dir`, runs `act`, and puts the manifest `orig` back. -/
def withManifest {α : Type} (dir : System.FilePath) (ms orig : Array ManifestEntry) (act : IO α) :
    IO α := do
  IO.FS.writeFile (dir / manifestName) (Manifest.render ms)
  let r ← act
  IO.FS.writeFile (dir / manifestName) (Manifest.render orig)
  return r

/-- The message of a failed `renderAll`, or empty if it succeeded. -/
def renderError (es : Array FigureEntry) (opts : BuildOptions := {}) : IO String := do
  match ← renderAll es opts with
  | .ok _ => return ""
  | .error e => return e

/-- The checks that build the gallery's motions into a directory under `.lake` and damage it. -/
def ioChecks : IO (Array (String × Bool)) := do
  let root : System.FilePath := ".lake" / "pilean-test-motion"
  if ← root.pathExists then IO.FS.removeDirAll root
  let a := root / "a"
  let code ← build entries a { requireStanding := true }
  let manifest := (Manifest.parse (← IO.FS.readBinFile (a / manifestName))).toOption.getD #[]
  let dir := "PILeanTest/MotionFigures/"
  let turnPaths := (manifest.filter (·.decl == "PILeanTest.MotionFigures.turn")).map (·.path)
  let report0 ← checkReport entries a
  let verdict0 ← verdicts a
  let mut recordsOk := !manifest.isEmpty
  for m in manifest do
    let src := Source.read? (← IO.FS.readBinFile (a / m.path))
    if !(src.toOption.any fun s => m.motion.isSome && s.motion == m.motion && m.matches s) then
      recordsOk := false
  let turnText ← IO.FS.readFile (a / dir / "turn.svg")
  let firstTitle := ((turnText.splitOn "<title>")[1]?.map (·.splitOn "</title>" |>.headD "")).getD ""
  let anim := a / dir / "twoCentres.svg"
  let tamperAnim ← tampered anim do return (← verdicts a, ← checkReport entries a)
  let tamperStill ← tampered (a / dir / "twoCentres-key-2.png") do
    return (← verdicts a, ← checkReport entries a)
  let tamperSheet ← tampered (a / dir / "twoCentres-keys.pdf") do
    return (← verdicts a, ← checkReport entries a)
  let tamperNarrow ← tampered (a / dir / "panels-narrow-key-3.svg") do
    return (← verdicts a, ← checkReport entries a)
  -- the manifest's record changed on every file of a motion
  let recount := manifest.map fun m =>
    if m.decl == "PILeanTest.MotionFigures.turn" then
      { m with motion := m.motion.map fun mo => { mo with keys := 4, cycle := mo.cycle + 1 } }
    else m
  let verdictRecount ← withManifest a recount manifest (verdicts a)
  let recycle := manifest.map fun m =>
    if m.decl == "PILeanTest.MotionFigures.turn" then
      { m with motion := m.motion.map fun mo => { mo with cycle := mo.cycle + 1 } }
    else m
  let verdictRecycle ← withManifest a recycle manifest (verdicts a)
  let relevel := manifest.map fun m =>
    if m.decl == "PILeanTest.MotionFigures.turn" then
      { m with motion := m.motion.map fun mo => { mo with checks := "warn" } }
    else m
  let verdictRelevel ← withManifest a relevel manifest (verdicts a)
  let narrowGone := manifest.filter fun m => !has m.path "panels-narrow"
  let verdictNarrowGone ← withManifest a narrowGone manifest do
    let moved := (manifest.filter fun m => has m.path "panels-narrow").map (·.path)
    for p in moved do IO.FS.rename (a / p) (root / (p.replace "/" "_"))
    let v ← verdicts a
    for p in moved do IO.FS.rename (root / (p.replace "/" "_")) (a / p)
    return v
  -- a forged animated SVG that is not inert, listed with its size and hash
  let forged := root / "f"
  for m in manifest do
    let p := forged / m.path
    if let some par := p.parent then IO.FS.createDirAll par
    IO.FS.writeBinFile p (← IO.FS.readBinFile (a / m.path))
  let animText ← IO.FS.readFile anim
  let hostile := (animText.replace "<g class=\"pilean-motion-live\">"
    "<g class=\"pilean-motion-live\"><set attributeName=\"opacity\" to=\"0\" begin=\"click\"/>")
  IO.FS.writeFile (forged / dir / "twoCentres.svg") hostile
  let forgedManifest := manifest.map fun m =>
    if m.path == dir ++ "twoCentres.svg" then
      { m with bytes := hostile.utf8ByteSize, sha256 := Sha256.hex (Sha256.hashString hostile) }
    else m
  IO.FS.writeFile (forged / manifestName) (Manifest.render forgedManifest)
  let verdictForged ← verdicts forged
  -- the standing and the check level
  let unmarked := entryOf "unmarked" turnMotion (.illustration false)
  let marked := entryOf "marked" turnMotion (.illustration true)
  let warned := entryOf "warned" (atLevel broken .warn) (.illustration true)
  let requireBad ← renderError #[unmarked] { requireStanding := true }
  let requireOk ← renderError #[marked] { requireStanding := true }
  let requireWarned ← renderError #[warned]
  let allowed ← renderError #[warned] { allowUnchecked := true }
  let oneOutput := renderOutput warned (((warned.outputs ())[3]?).getD default) {}
  let argsDefault := parseArgs []
  let argsAllow := parseArgs ["--allow-unchecked"]
  let argsRequire := parseArgs ["--require-checked"]
  let failing ← renderError #[entryOf "broken" broken (.illustration true)]
  let failCode ← build #[entryOf "broken" broken (.illustration true)] (root / "g") {}
  let nothingWritten := !(← (root / "g" / manifestName).pathExists)
  -- the builder refuses an SVG that is not inert, and a record it could not read back
  let svgOutput := fun (body : String) (mo : Option MotionSummary) =>
    ({ name := "", format := .svg, spec := .empty, motion := fun _ => mo,
       bytes := fun _ => .ok ("<svg xmlns=\"http://www.w3.org/2000/svg\">" ++ body ++
         "</svg>").toUTF8 } : Output)
  let notInert ← renderError #[{ marked with outputs := fun _ =>
    #[svgOutput "<animate attributeName=\"opacity\" values=\"0;1\" dur=\"1s\" begin=\"click\"/>"
      none] }]
  let unrecordable ← renderError #[{ marked with outputs := fun _ =>
    #[svgOutput "" (some { keys := 1, cycle := 1 / (10 ^ 19 : Nat), captions := 1 })] }]
  IO.FS.removeDirAll root
  let linked := manifest.filter (·.decl == "PILeanTest.MotionFigures.linkedTurn")
  return #[
    ("motion build: exit 0 with --require-standing and --require-checked", code == 0),
    ("motion build: the files of a motion, sorted",
      turnPaths.toList == ["turn-key-0.png", "turn-key-0.svg", "turn-key-1.png", "turn-key-1.svg",
        "turn-key-2.png", "turn-key-2.svg", "turn-keys.pdf", "turn-keys.png", "turn-keys.svg",
        "turn-poster.pdf", "turn-poster.png", "turn.svg"].map (dir ++ ·)),
    ("motion build: every file records its motion in its source record and the manifest alike",
      recordsOk && manifest.size == 12 + 14 + 12 + 10 + 27),
    ("motion build: the motion's own title is the first title of the written file",
      firstTitle == "A quarter turn" && has turnText "<pilean:source"),
    ("motion build: the motions are illustrations, the linked one linked to its theorem",
      !linked.isEmpty &&
        manifest.all (fun m => m.standing == some "illustration" || m.decl == linked[0]!.decl) &&
        linked.all fun m => m.standing == some "linked" &&
          m.theorems == some #["PILeanTest.MotionFigures.linkedTurn_spec"]),
    ("motion check: a fresh build matches", report0 == []),
    ("motion verify: a fresh build is ok", verdict0.length == manifest.size &&
      verdict0.all (·.startsWith "ok ")),
    ("motion verify and check: a tampered animated SVG is changed and stale",
      tamperAnim.1.contains s!"changed {dir}twoCentres.svg" &&
        tamperAnim.2 == [s!"stale: {dir}twoCentres.svg"]),
    ("motion verify and check: a tampered key still is changed and stale",
      tamperStill.1.contains s!"changed {dir}twoCentres-key-2.png" &&
        tamperStill.2 == [s!"stale: {dir}twoCentres-key-2.png"]),
    ("motion verify and check: a tampered sheet is changed and stale",
      tamperSheet.1.contains s!"changed {dir}twoCentres-keys.pdf" &&
        tamperSheet.2 == [s!"stale: {dir}twoCentres-keys.pdf"]),
    ("motion verify and check: a tampered narrow still of the panels is changed and stale",
      tamperNarrow.1.contains s!"changed {dir}panels-narrow-key-3.svg" &&
        tamperNarrow.2 == [s!"stale: {dir}panels-narrow-key-3.svg"]),
    ("motion verify: a manifest that counts other keys for a motion is refused",
      verdictRecount == ["error"]),
    ("motion verify: a manifest that records another cycle or level for a motion differs from \
        every file's source record",
      [verdictRecycle, verdictRelevel].all fun v =>
        (v.filter (·.startsWith "source differs PILeanTest/MotionFigures/turn")).length == 12),
    ("motion verify: a folder without the narrow rendition a motion records is refused",
      verdictNarrowGone == ["error"]),
    ("motion verify: an SVG that waits for an event, listed with its size and hash, is not inert",
      verdictForged.contains s!"not inert {dir}twoCentres.svg" &&
        (verdictForged.filter (·.startsWith "ok ")).length == manifest.size - 1),
    ("motion standing: --require-standing refuses an unmarked motion, accepts a marked one",
      has requireBad "PILeanTest.MotionTrust.unmarked is an illustration without the marking" &&
        requireOk == ""),
    ("motion checked: a build refuses a motion built at warn with errors left, unless \
        --allow-unchecked",
      has requireWarned "PILeanTest.MotionTrust.warned is a motion built at the check level warn \
        with 1 error left at the strict level" && allowed == ""),
    ("motion checked: renderOutput itself refuses each output of such a motion (the route site \
        builds use)",
      match oneOutput with
      | .error e => has e "is a motion built at the check level warn"
      | .ok _ => false),
    ("motion checked: refusing is the default; --allow-unchecked opts out; --require-checked is \
        accepted",
      (argsDefault.toOption.any fun (_, o) => !o.allowUnchecked) &&
        (argsAllow.toOption.any fun (_, o) => o.allowUnchecked) &&
        (argsRequire.toOption.any fun (_, o) => !o.allowUnchecked)),
    ("motion build: a motion with errors fails the build with a readable message, writing nothing",
      has failing "PILeanTest/MotionTrust/broken.svg: problems: " &&
        has failing "PILeanTest/MotionTrust/broken-key-0.png: problems: " && failCode == 1 &&
        nothingWritten),
    ("motion build: an SVG output that is not inert is refused",
      has notInert "the SVG is not inert (the event-based timing begin=\"click\")"),
    ("motion build: a record whose cycle does not read back is refused",
      has unrecordable "does not read back")]

end PILeanTest.MotionTrust
