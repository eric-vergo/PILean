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

The outputs of a motion (`PILean.Trust.Motion`): their names, formats and order; the key stills
and the poster byte for byte the files of the key figures; the animated SVG that of the checked
route, and its body for a page (`MotionData.live`) the file without what the file adds for itself;
the stills with their captions (`MotionData.stills`); the contact sheet's grid and captions; the
step table; a motion with errors failing every output; the APNG and the GIF only when asked; the
dark style. The manifest of a motion (format `pilean-manifest-4`): its keys written and read back,
refused when malformed or when the files of one declaration disagree, the earlier format still
read. The inert scanner on what motions write. A build of the golden motions into a directory
under `.lake`: the files and the manifest, `pilean-verify` and `pilean-build --check` on them
fresh and after tampering with the animated SVG, a still and the sheet, a forged non-inert SVG,
`--require-standing` on an unmarked motion, and a motion with errors failing the build.
-/

namespace PILeanTest.MotionTrust

open PILean PILean.Trust PILean.Plane PILeanTest.MotionChecks

/-- Whether `t` occurs in `s`. -/
def has (s t : String) : Bool := (s.splitOn t).length > 1

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

/-- The motion with its first key turned by a wrong angle: a turn that misses its key. -/
def broken : Motion := missBy 0.5

/-- The texts of the `text` elements at the top of a drawing (not inside its groups), in order. -/
def top : Canvas.Shape → Array String
  | .group cs .. => cs.filterMap fun
    | .text s .. => some s
    | _ => none
  | _ => #[]

/-- The root of the motion's animated SVG file, rebuilt from its parts: the title, the
description, the reduced-motion style, the nodes a page puts inline (`live`) and the poster group
of the poster key's still. -/
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

/-- The checks of the outputs of one golden motion. -/
def outputChecks (name : String) (m : Motion) : Array (String × Bool) :=
  let os := ToOutputs.outputs m
  let n := m.keys.size
  let r := m.report
  let svg := match r.svg? with | .ok s => s | .error _ => ""
  let main := find os "" .svg
  let page := main.bind (·.motionPage ())
  let summary : MotionSummary := { keys := n, cycle := r.plan.timeline.cycle, captions := n }
  let keyNames := (List.range n).flatMap fun k => [s!"svg-key-{k}", s!"png-key-{k}"]
  #[(s!"motion outputs {name}: the files, in order",
      os.toList.map (fun o => o.format.name ++ o.name) ==
        ["svg", "png-poster", "pdf-poster", "svg-keys", "png-keys", "pdf-keys"] ++ keyNames),
    (s!"motion outputs {name}: every output renders and records the motion",
      os.all fun o => (o.bytes ()).toOption.isSome && o.motion () == some summary),
    (s!"motion outputs {name}: the animated SVG is the checked route's, and its specification",
      main.all fun o => bytesOf o == svg.toUTF8 && o.spec == svg.toUTF8 && !svg.isEmpty),
    (s!"motion outputs {name}: each key still is the key figure's SVG and PNG, byte for byte",
      (List.range n).all fun k =>
        (find os s!"-key-{k}" .svg).all (bytesOf · == (m.keyFigure k).toSvg.toUTF8) &&
        (find os s!"-key-{k}" .png).all (bytesOf · == ((m.keyFigure k).toPng).getD .empty)),
    (s!"motion outputs {name}: the poster is the poster key's PNG and PDF",
      (find os "-poster" .png).all (bytesOf · == ((m.keyFigure m.poster).toPng).getD .empty) &&
        (find os "-poster" .pdf).all (bytesOf · == (m.keyFigure m.poster).toPdf)),
    (s!"motion outputs {name}: every SVG output is inert",
      os.all fun o => o.format != .svg ||
        (String.fromUTF8? (bytesOf o)).any Svg.isInert),
    (s!"motion outputs {name}: the page data records the keys, the cycle and the captions",
      page.any fun d => d.summary == summary && d.steps.size == m.steps.size),
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
      page.any fun d => d.stills.frames.size == n && d.stills.stepCaptions == m.captions &&
        d.stills.poster == m.poster && (List.range n).all fun k =>
          (d.stills.frames[k]?.map (·.document.toUTF8)) == some (m.keyFigure k).toSvg.toUTF8),
    (s!"motion outputs {name}: the sheet's SVG is its inline picture, inert",
      (find os "-keys" .svg).any fun o =>
        (o.inline ()).any (·.document.toUTF8 == bytesOf o) &&
          (String.fromUTF8? (bytesOf o)).any Svg.isInert),
    (s!"motion outputs {name}: the sheet's PDF passes the structural check",
      (find os "-keys" .pdf).any fun o => (Pdf.check (bytesOf o)).toOption.isSome),
    (s!"motion outputs {name}: only the animated SVG reports the warnings",
      (os.filter fun o => o.name != "" || o.format != .svg).all fun o => (o.problems ()).isEmpty)]

/-- The contact sheet: its grid, the stills in it and the captions below them. -/
def sheetChecks : Array (String × Bool) :=
  let m := twoCentresMotion
  let c := m.report.checked
  let sh := c.sheet
  let w := (m.keyFigure 0).autoPlaced.frame.width.round
  let plain := sheetOf c.title c.captions (c.main.stills.map ({ · with textAsShapes := false }))
    c.style
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
      (sheetOf "" #["Only."] #[ExplorerFrame.ofPlane (m.keyFigure 0)] st).width ==
        2 * sheetGap + w)]

/-- The step table. -/
def stepChecks : Array (String × Bool) :=
  let rows := twoCentresMotion.stepRows
  let words := rows.map (·.moves.map (·.words))
  #[("motion steps: one row per step, with its duration in seconds, exactly",
      rows.size == 3 && rows.map (·.duration) == #[1, 1, 4 / 5] && rows.all (!·.idle)),
    ("motion steps: each move with its actor, kind, centre and exact fraction of a turn",
      words == #[#["turn about (0, 0) by 1/4 of a full turn (90°)",
          "turn about (0, 0) by 1/4 of a full turn (90°)",
          "turn about (0, 0) by 1/4 of a full turn (90°)",
          "turn about (0, 0) by 1/4 of a full turn (90°)"],
        #["turn about (1, 1) by 1/2 of a full turn (180°)", "appearance"],
        #["slide by (1, 0)"]] &&
        rows.map (·.moves.map (·.actor)) == #[#["A", "T1", "T2", "T3"], #["A", "B"], #["S"]]),
    ("motion steps: an idle step takes the pacing's idle time and has no move",
      turnMotion.stepRows.map (fun r => (r.idle, r.duration, r.moves.size)) ==
        #[(false, 1, 1), (true, 9 / 10, 0)]),
    ("motion steps: a turn's degrees are exact",
      turnDegreesWords (1 / 7) == "360/7°" && turnDegreesWords (-1 / 4) == "-90°"),
    ("motion page: the words of a motion's page",
      ((find (ToOutputs.outputs turnMotion) "" .svg).bind (·.motionPage ())).map (·.words) ==
        some "An animation drawn from 3 exact key frames. Between key frames the browser turns \
          or slides the drawn items about the stated centres; the key frames are the exact data.")]

/-- A motion with errors, the APNG and the GIF on request, the dark style. -/
def routeChecks : Array (String × Bool) :=
  let bad := ToOutputs.outputs broken
  let warned := ToOutputs.outputs (MotionChecks.warned broken)
  let rasters := ToOutputs.outputs ({ motion := turnMotion, rasters := true, fps := 10 } :
    MotionFigure Motion)
  let turnSvg := match turnMotion.svg? with | .ok s => s.toUTF8 | .error _ => .empty
  let darkStyle := turnMotion.style.darkTwin?
  let dark := darkStyle.map fun d => turnMotion.withStyle d
  #[("motion errors: every output of a motion with errors fails with the messages of its errors",
      !bad.isEmpty && !broken.report.errors.isEmpty && bad.all fun o =>
        errorOf o == "problems: " ++ "; ".intercalate broken.report.errors.toList),
    ("motion errors: a motion with errors writes no animated SVG and no page data",
      (find bad "" .svg).all fun o => o.spec.isEmpty &&
        (o.motionPage ()).all (·.live.nodes.isEmpty)),
    ("motion warnings: under the level warn the motion renders, its problems as warnings",
      warned.all (fun o => (o.bytes ()).toOption.isSome) &&
        (find warned "" .svg).any fun o => !(o.problems ()).isEmpty),
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
          (find os "-keys" .svg).any (fun o => has (String.fromUTF8! (bytesOf o)) bg))]

/-- A manifest entry of a motion's file. -/
def motionEntry (path : String) (motion : Option MotionSummary) : ManifestEntry :=
  { path, format := "svg", bytes := 1, sha256 := String.ofList (List.replicate 64 'a'),
    fingerprint := String.ofList (List.replicate 64 'b'), module := "M", decl := "M.d",
    file := "M.lean", line := 1, column := 0, version := "0.1.0", standing := some "illustration",
    motion }

/-- The manifest's keys of a motion. -/
def manifestChecks : Array (String × Bool) :=
  let mo : MotionSummary := { keys := 3, cycle := 59 / 10, captions := 3 }
  let es := #[motionEntry "M/d.svg" (some mo), motionEntry "M/d-key-0.svg" (some mo)]
  let text := Manifest.render es
  let parsed := (Manifest.parse text.toUTF8).toOption
  let edit := fun (a b : String) => Manifest.parse (text.replace a b).toUTF8
  let refused := fun (a b : String) => (edit a b) matches .error _
  #[("motion manifest: the format is pilean-manifest-4", manifestFormat == "pilean-manifest-4"),
    ("motion manifest: a motion's keys are written after the standing",
      has text "\"standing\":\"illustration\",\"kind\":\"motion\",\"keys\":3,\"cycle\":\"59/10\",\
        \"captions\":3}"),
    ("motion manifest: written and read back", parsed == some es),
    ("motion manifest: a whole cycle is written without a denominator",
      cycleText 6 == "6" && cycleText (59 / 10) == "59/10" && cycleOfText? "6" == some 6 &&
        cycleOfText? "59/10" == some (59 / 10)),
    ("motion manifest: a cycle not in lowest terms, with a sign, a leading zero, a zero \
        denominator or other characters is refused",
      ["2/4", "-1", "06", "1/0", "1/1", "1.5", "", "/2", "1/", "1/2/3", " 1", "1e3",
        "1234567890123456789"].all (cycleOfText? · |>.isNone)),
    ("motion manifest: malformed keys of a motion are refused",
      refused "\"cycle\":\"59/10\"" "\"cycle\":\"118/20\"" &&
        refused "\"kind\":\"motion\"" "\"kind\":\"film\"" &&
        refused "\"kind\":\"motion\"," "" &&
        refused "\"keys\":3," "" &&
        refused "\"keys\":3" "\"keys\":0" &&
        refused "\"captions\":3" "\"captions\":\"3\"" &&
        refused "\"cycle\":\"59/10\"" "\"cycle\":59"),
    ("motion manifest: a key the format does not have is refused",
      refused "\"kind\":\"motion\"" "\"kind\":\"motion\",\"speed\":2" &&
        refused "\"path\"" "\"extra\":1,\"path\""),
    ("motion manifest: the files of one declaration must record the same motion",
      (Manifest.parse (Manifest.render #[motionEntry "M/d.svg" (some mo),
        motionEntry "M/d-key-0.svg" (some { mo with keys := 4 })]).toUTF8) matches .error _ &&
      (Manifest.parse (Manifest.render #[motionEntry "M/d.svg" (some mo),
        motionEntry "M/d-key-0.svg" none]).toUTF8) matches .error _),
    ("motion manifest: a manifest of the previous format is read, without motions",
      (Manifest.parse (Manifest.render (es.map ({ · with motion := none }))
          |>.replace manifestFormat previousManifestFormat).toUTF8).toOption ==
        some (es.map ({ · with motion := none })) &&
      (edit manifestFormat previousManifestFormat).toOption ==
        some (es.map ({ · with motion := none }))),
    ("motion manifest: an unknown format is refused, so an older reader refuses this one",
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
        Svg.isInert (withEvent a))]

/-- The checks that need no files. -/
def checks : Array (String × Bool) :=
  (golden.flatMap fun (n, m) => outputChecks n m) ++ sheetChecks ++ stepChecks ++ routeChecks ++
    manifestChecks ++ inertChecks ++
    #[("renderer: the identity covers the motions and their outputs",
        ["PILean.Anim.Timeline", "PILean.Anim.Smil", "PILean.Plane.Motion",
          "PILean.Plane.MotionPlan", "PILean.Plane.MotionOutput", "PILean.Trust.Motion"].all
          (rendererSources.map (·.1)).contains)]

/-- The figure entries of the golden motions and the linked quarter turn, as `figures%` gives
them. -/
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

/-- The checks that build the golden motions into a directory under `.lake` and damage it. -/
def ioChecks : IO (Array (String × Bool)) := do
  let root : System.FilePath := ".lake" / "pilean-test-motion"
  if ← root.pathExists then IO.FS.removeDirAll root
  let a := root / "a"
  let code ← build entries a {}
  let manifest := (Manifest.parse (← IO.FS.readBinFile (a / manifestName))).toOption.getD #[]
  let dir := "PILeanTest/MotionFigures/"
  let turnPaths := (manifest.filter (·.decl == "PILeanTest.MotionFigures.turn")).map (·.path)
  let report0 ← checkReport entries a
  let verdict0 ← verdicts a
  let summaryOk := manifest.all fun m =>
    match m.motion, (entries.find? (·.decl == m.decl)) with
    | some mo, some e =>
      let mm := ((e.outputs ())[0]?.bind (·.motion ()))
      mm == some mo && mo.captions == mo.keys
    | _, _ => false
  let anim := a / "PILeanTest" / "MotionFigures" / "twoCentres.svg"
  let still := a / "PILeanTest" / "MotionFigures" / "twoCentres-key-2.png"
  let sheet := a / "PILeanTest" / "MotionFigures" / "twoCentres-keys.pdf"
  let tamperAnim ← tampered anim do return (← verdicts a, ← checkReport entries a)
  let tamperStill ← tampered still do return (← verdicts a, ← checkReport entries a)
  let tamperSheet ← tampered sheet do return (← verdicts a, ← checkReport entries a)
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
  -- the standing, and a motion with errors
  let unmarked := entryOf "unmarked" turnMotion (.illustration false)
  let marked := entryOf "marked" turnMotion (.illustration true)
  let requireBad ← renderAll #[unmarked] { requireStanding := true }
  let requireOk ← renderAll #[marked] { requireStanding := true }
  let failing ← renderAll #[entryOf "broken" broken (.illustration true)] {}
  let failCode ← build #[entryOf "broken" broken (.illustration true)] (root / "g") {}
  let nothingWritten := !(← (root / "g" / manifestName).pathExists)
  -- the builder refuses an SVG that is not inert
  let notInert ← renderAll #[{ marked with outputs := fun _ =>
    #[{ name := "", format := .svg, spec := .empty,
        bytes := fun _ => .ok ("<svg xmlns=\"http://www.w3.org/2000/svg\"><animate \
          attributeName=\"opacity\" values=\"0;1\" dur=\"1s\" begin=\"click\"/></svg>").toUTF8 }] }]
  IO.FS.removeDirAll root
  let linked := manifest.filter (·.decl == "PILeanTest.MotionFigures.linkedTurn")
  return #[
    ("motion build: exit 0", code == 0),
    ("motion build: the files of a motion, sorted",
      turnPaths.toList == ["turn-key-0.png", "turn-key-0.svg", "turn-key-1.png", "turn-key-1.svg",
        "turn-key-2.png", "turn-key-2.svg", "turn-keys.pdf", "turn-keys.png", "turn-keys.svg",
        "turn-poster.pdf", "turn-poster.png", "turn.svg"].map (dir ++ ·)),
    ("motion build: every file of a motion records it, as its outputs do",
      summaryOk && manifest.size == 50),
    ("motion build: the motions are illustrations, the linked one linked to its theorem",
      !linked.isEmpty &&
        manifest.all (fun m => m.standing == some "illustration" || m.decl == linked[0]!.decl) &&
        linked.all fun m => m.standing == some "linked" &&
          m.theorems == some #["PILeanTest.MotionFigures.linkedTurn_steps"]),
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
    ("motion verify: an SVG that waits for an event, listed with its size and hash, is not inert",
      verdictForged.contains s!"not inert {dir}twoCentres.svg" &&
        (verdictForged.filter (·.startsWith "ok ")).length == manifest.size - 1),
    ("motion standing: --require-standing refuses an unmarked motion, accepts a marked one",
      (match requireBad with
        | .error e => has e "PILeanTest.MotionTrust.unmarked is an illustration without the marking"
        | .ok _ => false) && requireOk matches .ok _),
    ("motion build: a motion with errors fails the build with a readable message, writing nothing",
      (match failing with
        | .error e => has e "PILeanTest/MotionTrust/broken.svg: problems: " &&
            has e "PILeanTest/MotionTrust/broken-key-0.png: problems: "
        | .ok _ => false) && failCode == 1 && nothingWritten),
    ("motion build: an SVG output that is not inert is refused",
      match notInert with
      | .error e => has e "the SVG is not inert (the event-based timing begin=\"click\")"
      | .ok _ => false)]

end PILeanTest.MotionTrust
