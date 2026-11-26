/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import ManualExample
import PILeanVersoManual

/-!
# The Manual-genre adapter's checks

`lake test` generates the example manual (`ManualExample`) twice into a scratch folder and
checks what a reader gets: the figure files and the manifest, every SVG inert, the pages' figures
(numbers, text alternatives, light and dark pictures, the source line, the theorem, a figure over
its backdrop, the reference), the figures page, the same bytes from both builds, and
`--check-figures` failing on a damaged copy. The checks of the argument values come first.
-/

open PILean PILeanVerso Verso.Genre.Manual

-- Every theorem linked to a figure of the example writes out the whole figure, with every
-- definition of the example it is built from (`PILean.Trust.figurePinProblem?`), except the three
-- figures whose theorems are weak on purpose, to show that a link is a pointer to a statement.
#assert_figures_pinned ManualExample except ManualExample.vacuousOr
  ManualExample.vacuousHypothesis ManualExample.vacuousBound

/-- A true statement about the points the plot uses, which does not name the plot. -/
theorem aboutPoints : ∀ p ∈ ManualExample.trianglePoints, 0 ≤ p.2 := by
  intro p hp
  simp only [ManualExample.trianglePoints, List.mem_map, List.mem_range] at hp
  obtain ⟨n, -, rfl⟩ := hp
  exact Int.natCast_nonneg _

-- The directive's check of `proves :=` accepts the theorems of the example and refuses a
-- statement that names only what a figure is built from, or another figure's theorem.
#guard_msgs in
open Lean Elab in
run_meta do
  let accepts (fig thm : Name) : CoreM Bool := do
    try discard <| PILeanVerso.checkTheorem fig (mkIdent thm); return true
    catch _ => return false
  for (f, t) in [(``ManualExample.trianglePlot, ``ManualExample.trianglePoints_spec),
      (``ManualExample.divisorGraph, ``ManualExample.covers_count)] do
    unless ← accepts f t do throwError "{t} was refused for {f}"
  for (f, t) in [(``ManualExample.trianglePlot, ``aboutPoints),
      (``ManualExample.trianglePlot, ``ManualExample.covers_count),
      (``ManualExample.trianglePlot, ``ManualExample.two_mul_triangle)] do
    if ← accepts f t then throwError "{t} was accepted for {f}"

/-- The example's configuration: its two backdrops. -/
def exampleConfig : RenderConfig :=
  let base : RenderConfig := {}
  let pic (bg : String) : ByteArray :=
    ("<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"320\" height=\"200\">" ++
      s!"<rect width=\"320\" height=\"200\" fill=\"{bg}\"/></svg>\n").toUTF8
  { base with extraDataFiles := base.extraDataFiles.insertMany #[
      { filename := "backdrop-light.svg", contents := pic "#e8ecf0" },
      { filename := "backdrop-dark.svg", contents := pic "#2a3039" }] }

/-- Generates the example manual with `args`. -/
def generate (args : List String) : IO UInt32 :=
  PILeanVerso.Manual.withFigures (%doc ManualExample) site_figures% args fun doc args =>
    manualMain doc (options := args) (config := exampleConfig)

/-- A figure whose theorem names it but is not linked to it by `figure_links`. -/
@[figure]
def unlinked : Plot.Figure := ManualExample.trianglePlot

/-- A statement that names `unlinked`; no `figure_links` links the two. -/
theorem unlinked_self : unlinked = ManualExample.trianglePlot := rfl

-- `figure_links` refuses a theorem whose statement does not name the figure, so a figure whose
-- theorem was weakened that way stops building rather than keeps its standing.
#guard_msgs in
run_meta do
  let some _ ← PILean.Trust.figureTheoremProblem? `unlinked ``ManualExample.two_mul_triangle
    | throwError "a statement that does not name the figure was accepted"

/-- The table of figures of this module's environment, with the page data. -/
def table : SiteFigures := site_figures%

/-- Whether `s`, its white space collapsed, contains `t` with its white space collapsed. -/
def hasWords (s t : String) : Bool :=
  let words := fun (x : String) => " ".intercalate ((x.split Char.isWhitespace).toList.map
    (·.toString) |>.filter (!·.isEmpty))
  ((words s).splitOn (words t)).length > 1

/-- The files below `dir`, relative to it, sorted. -/
partial def filesBelow (dir : System.FilePath) (rel : String := "") : IO (Array String) := do
  let mut out := #[]
  for e in ← dir.readDir do
    let r := if rel.isEmpty then e.fileName else rel ++ "/" ++ e.fileName
    if ← e.path.isDir then out := out ++ (← filesBelow e.path r) else out := out.push r
  return out.qsort (· < ·)

/-- Whether `s` contains `t`. -/
def has (s t : String) : Bool := (s.splitOn t).length > 1

/-- Whether `t` has an attribute that looks like an inline event handler (` on…=`). -/
def hasHandler (t : String) : Bool := ((t.splitOn " on").drop 1).any fun rest =>
  let name := (rest.takeWhile Char.isAlpha).toString
  !name.isEmpty && (rest.drop name.length).startsWith "="

/-- Runs the checks; exit status 0 when every one holds. -/
def main : IO UInt32 := do
  let check (ok : Bool) (what : String) : StateT (Nat × Nat) IO Unit := do
    modify fun (f, k) => (if ok then f else f + 1, k + 1)
    IO.println s!"{if ok then "ok" else "FAIL"}: {what}"
  let run : StateT (Nat × Nat) IO Unit := do
    check (validBackdrop "shots/window-{theme}.png") "a themed backdrop is accepted"
    check (!validBackdrop "../x.png" && !validBackdrop "/x.png" && !validBackdrop "a//b" &&
      !validBackdrop "a b.png" && !validBackdrop "") "unsafe or empty backdrops are refused"
    check (backdropUrl "s/w-{theme}.png" "dark" == "s/w-dark.png") "a backdrop's dark address"
    check (isCssLength "60%" && !isCssLength "60") "widths are CSS lengths"
    -- a figure whose SVG is refused gets that error alone, not one about how it is used
    let hostile : Plane.Figure :=
      { items := #[(Plane.point ⟨0, 0⟩).declRef (.mkSimple "javascript:x"),
        Plane.point ⟨1, 1⟩] }
    let src : Trust.SourceData :=
      { module := "M", decl := "M.hostile", file := "M.lean", line := 1, column := 0,
        sourceHash := "" }
    let entry : Trust.FigureEntry :=
      { src with outputs := fun _ => Trust.ToOutputs.outputs hostile }
    let refusals := fun (u : FigureUse) => match renderSite #[entry] #[u] {} with
      | .ok _ => #[]
      | .error e => (e.splitOn "\n").toArray
    check (#[({ decl := "M.hostile", explorer := true } : FigureUse),
        { decl := "M.hostile", inline := true }].all fun u =>
        let es := refusals u
        !es.isEmpty && es.all (has · "is not inert") && !es.any (has · "not an explorer") &&
          !es.any (has · "no inline picture"))
      "a refused SVG is the only error of its figure, shown as an explorer or inline"
    -- a motion that its checks did not stop, built at `warn`, is refused by default
    let keyAt (x : Float) : Plane.Figure :=
      { items := #[Plane.point ⟨-3, -3⟩, Plane.point ⟨3, 3⟩, (Plane.point ⟨x, 0⟩).actor "X"] }
    let motionOf (x : Float) (checks : CheckLevel) : Plane.Motion :=
      { keys := #[keyAt 0, keyAt x], captions := #["Before.", "After."],
        steps := #[{ moves := #[("X", .slide ⟨1, 0⟩)] }], checks,
        info := { title := "A slide", description := "The point X slides." } }
    let motionOutputs (m : Plane.Motion) : Array Trust.Output :=
      Trust.withStanding (.illustration true) (Trust.ToOutputs.outputs m)
    let motionEntry (decl : String) (m : Plane.Motion) : Trust.FigureEntry :=
      { src with decl := decl, outputs := fun _ => motionOutputs m }
    let siteError (decl : String) (m : Plane.Motion) : String :=
      match renderSite #[motionEntry decl m] #[(decl : FigureUse)] {} with
      | .ok _ => ""
      | .error e => e
    check (has (siteError "M.missed" (motionOf 1.5 .warn))
        "is a motion built at the check level warn with 1 error left")
      "a site build refuses a motion built at warn with an error left"
    check (siteError "M.landed" (motionOf 1 .fail) == "")
      "a site build accepts a motion checked strictly"
    let rendered := fun (opts : SiteOptions) (decl : String) (m : Plane.Motion) =>
      match renderSite #[motionEntry decl m] #[(decl : FigureUse)] opts with
      | .ok r => (r.figures[decl]?).bind fun f => motionOf? f.files
      | .error _ => none
    check ((rendered {} "M.landed" (motionOf 1 .fail)).map (·.1.unchecked) == some false)
      "a motion checked strictly is shown inline: the site keeps its page data, checked strictly"
    check (((rendered { allowUnchecked := true } "M.draft" (motionOf 1.5 .warn)).map
        fun (d, _) => (d.unchecked, d.checkWords.isSome)) == some (true, true))
      "with allowUnchecked (for drafts) a motion built at warn is rendered, and its page data \
        says it was not checked strictly"
    check ((parseWrapperArgs {} ["--figure-allow-unchecked", "--output", "o"]).toOption.map
        (fun w => (w.options.allowUnchecked, w.rest)) == some (true, ["--output", "o"]) &&
      figureFlags { allowUnchecked := true } == #["--figure-allow-unchecked"])
      "--figure-allow-unchecked is taken by the wrapper and repeated in the pages' commands"
    -- standing and page data
    let standingOf := fun (n : String) => (table.entries.find? (·.decl == n)).map (·.standing)
    check (standingOf "ManualExample.trianglePlot" ==
        some (.linked #["ManualExample.trianglePoints_spec"]))
      "a figure linked by figure_links has the standing linked, with its theorem"
    check (standingOf "unlinked" == some (.illustration false))
      "a figure whose theorem is not linked is an unmarked illustration"
    let pages := table.pages.toOption.getD {}
    check ((pages["ManualExample.trianglePlot"]?.map (·.theorems.map (·.decl.name))) ==
        some #["ManualExample.trianglePoints_spec"])
      "the page data holds the theorem of the standing"
    check ((pages["ManualExample.trianglePlot"]?.map (·.related.map (·.name))) ==
        some #["ManualExample.trianglePoints", "ManualExample.triangle"])
      "the page data holds the project's declarations the figure uses, nearest first"
    check ((pages["ManualExample.trianglePlot"]?.bind (·.theorems[0]?)).map (·.axioms) ==
        some #["Classical.choice", "Quot.sound", "propext"]) "the theorem's axioms are recorded"
    let unlinkedEntry := table.entries.filter (·.decl == "unlinked")
    let claim := renderSite unlinkedEntry #[{ decl := "unlinked", proves := some "unlinked_self" }] {}
    check (match claim with
        | .error e => has e "not linked to it" && has e "figure_links unlinked unlinked_self"
        | .ok _ => false)
      "a caption naming a theorem the standing does not record fails the build"
    check (!has (standingWords (.illustration false)) "Linked" &&
        standingWords (.linked #["T"]) == "Linked theorem:" &&
        standingWords (.linked #["T", "U"]) == "Linked theorems:")
      "only a linked standing is worded as a linked theorem"
    check (#[standingWords (.illustration false), standingWords (.linked #["T"]),
        theoremScopeText, theoremLinkText, linkCheckedText "T"].all fun w =>
          !has w "Tied" && !has w "tied" && !has w "roved by")
      "no sentence of a page says that a figure is tied to its object or proved"
    let trust ← IO.FS.readFile ("../../docs/TRUST.md" : System.FilePath)
    check (hasWords trust theoremScopeText && hasWords trust theoremLinkText &&
        hasWords trust (linkCheckedText "T"))
      "the pages' sentences on what a linked theorem covers are those of docs/TRUST.md"
    check (pageSlug "ManualExample.trianglePlot" == "ManualExample.trianglePlot" &&
        pageSlug "a «b»" != pageSlug "a_b_" && (pageSlug "x/../<y>").all
          (fun c => c.isAlphanum || c == '.' || c == '_' || c == '-') &&
        !(pageSlug "..").startsWith ".")
      "a page's address keeps a plain name and confines any other to safe characters"
    -- the link check on a planted site: a page with a `<base>` whose links name a missing file,
    -- a missing id, an id that exists (percent-escaped) and a link with a scheme
    let planted : System.FilePath := ".lake" / s!"pilean-links-{← IO.monoNanosNow}"
    IO.FS.createDirAll (planted / "A" / "B")
    IO.FS.writeFile (planted / "index.html") "<p id=\"top\">x</p>"
    IO.FS.writeFile (planted / "A" / "B" / "index.html") ("<base href=\"./../../\"/>" ++
      "<div><span class=\"pilean-figure-page-anchor\" id=\"r\u00e9\"></span>" ++
      "<a class=\"pilean-page-use\" " ++
      "href=\"A/B/#r%C3%A9\">a</a><a class=\"pilean-page-link\" href=\"A/B/#gone\">b</a>" ++
      "<a class=\"pilean-x\" href=\"C/\">c</a><a href=\"#nowhere\">d</a>" ++
      "<a class=\"pilean-x\" href=\"https://e.org/#y\">e</a>" ++
      "<a class=\"pilean-x\" href=\"#top\">f</a></div>")
    let (n1, p1) ← siteLinkProblems planted
    let (n2, p2) ← siteLinkProblems planted (all := true)
    IO.FS.removeDirAll planted
    check (n1 == 4 && p1.size == 2 && p1.any (has · "has no element with the id gone") &&
        p1.any (has · "no file C/index.html") && n2 == 5 && p2.size == 3 &&
        p2.any (has · "index.html has no element with the id nowhere"))
      "the link check resolves links against the page's <base> and reports a missing file or id"
    check (ciRunHrefOf (some "https://github.com") (some "o/r") (some "42") ==
        some "https://github.com/o/r/actions/runs/42" &&
        ciRunHrefOf (some "https://github.com") (some "o/r") none == none &&
        ciRunHrefOf (some "javascript:x") (some "o/r") (some "1") == none &&
        ciRunHrefOf (some "https://h/x") (some "o/r") (some "1") == none &&
        ciRunHrefOf (some "https://github.com") (some "o/../r") (some "1") == none &&
        ciRunHrefOf (some "https://github.com") (some "o/r\"><b>") (some "1") == none &&
        ciRunHrefOf (some "https://github.com") (some "o/r") (some "1;2") == none)
      "the run's link is made only from well-formed GitHub Actions values"
    let tmp := System.FilePath.mk ".lake" / s!"pilean-verso-manual-test-{← IO.monoNanosNow}"
    let out1 := tmp / "a"
    let out2 := tmp / "b"
    let c1 ← generate ["--output", out1.toString]
    check (c1 == 0) "the example manual is generated"
    let c2 ← generate ["--output", out2.toString]
    check (c2 == 0) "it is generated again"
    let figs := out1 / "html-multi" / "-verso-data" / figureFolder
    let files ← filesBelow figs
    check (files.contains "manifest.json") "the figures folder has its manifest"
    let svgs := files.filter (·.endsWith ".svg")
    check (svgs.size == 59)
      s!"59 SVG files: light, dark, narrow, the explorers' frames, and the motions' animated \
        pictures, key stills and contact sheets ({svgs.size})"
    for f in svgs do
      let t ← IO.FS.readFile (figs / f)
      check (Svg.isInert t) s!"{f} is inert"
    let files2 ← filesBelow (out2 / "html-multi" / "-verso-data" / figureFolder)
    let mut same := files == files2
    for f in files do
      if same then
        same := (← IO.FS.readBinFile (figs / f)) ==
          (← IO.FS.readBinFile (out2 / "html-multi" / "-verso-data" / figureFolder / f))
    check same "two builds write the same figure files"
    let numbers ← IO.FS.readFile (out1 / "html-multi" / "Numbers" / "index.html")
    let pages2 ← IO.FS.readFile (out2 / "html-multi" / "Numbers" / "index.html")
    check (numbers == pages2) "two builds write the same page"
    check (has numbers "Figure 1" && has numbers "Figure 2") "the figures are numbered"
    check (has numbers "alt=\"A line through the points") "the text alternative is the given one"
    check (has numbers "pilean-figure-has-dark" && has numbers "trianglePlot-dark.svg")
      "a figure has its dark picture"
    check (has numbers ">Linked theorem<" && !has numbers "Proved by" &&
      has numbers "ManualExample.trianglePoints_spec") "the theorem is named"
    check (has numbers "ManualExample/Figures.lean:") "the source line names the file and line"
    check (has numbers "class=\"pilean-figref\"") "the reference links to the figure"
    let marks ← IO.FS.readFile (out1 / "html-multi" / "Marks-over-a-picture" / "index.html")
    check (has marks "pilean-figure-stack" && has marks "-verso-data/backdrop-dark.svg" &&
      has marks "-verso-data/backdrop-light.svg") "a figure is drawn over its backdrop"
    check (has marks "aria-hidden=\"true\"") "the drawing over a backdrop is hidden from readers"
    let motion ← IO.FS.readFile (out1 / "html-multi" / "Motion" / "index.html")
    check ((motion.splitOn "data-bp-motion").length - 1 == 2 &&
        has motion "class=\"pilean-inline-svg pilean-motion-live pilean-motion-wide\"" &&
        has motion "class=\"pilean-inline-svg pilean-motion-live pilean-motion-narrow\"" &&
        has motion "Step 1 of 3: P on the unit circle at (1, 0)." &&
        has motion "ManualExample.quarterTurn-key-2-dark.svg" &&
        !has motion "bp_motion_link")
      "the motions are shown inline, with their narrow renditions and their captioned stills, \
        and without the Blueprint's link to its switch"
    -- each motion's wrapper: up to the end of its list of stills
    let motionParts := (motion.splitOn "data-bp-motion").drop 1 |>.map fun p =>
      (p.splitOn "</ol>").headD ""
    check (motionParts.length == 2 && motionParts.all (!has · "<script") &&
        motionParts.all (!hasHandler ·) && motionParts.all (!has · "<a "))
      "a motion's markup has no script, no event handler and no link"
    let figureParts := (numbers.splitOn "<figure").drop 1 |>.map fun p =>
      (p.splitOn "</figure>").headD ""
    check (figureParts.length == 2 && figureParts.all (!has · "<script") &&
      figureParts.all (!has · " on")) "the figures' markup has no script and no event handler"
    let list ← IO.FS.readFile (out1 / "html-multi" / "Figures" / "index.html")
    check (has list "pilean-figure-index" && has list "Figure 3") "the figures page lists them"
    check (has list "ManualExample.radiusSlider" && has list "ManualExample.wordSteps")
      "the figures page lists the explorers"
    check ((list.splitOn "pilean-standing pilean-standing-linked").length - 1 == 5 &&
        (list.splitOn "pilean-standing pilean-standing-illustration").length - 1 == 6)
      "the figures page shows each figure's standing"
    check ((list.splitOn "class=\"pilean-page-link\"").length - 1 == 11 &&
        has numbers "class=\"pilean-page-link\"")
      "the figures page and the source line link each figure's page"
    let (linksChecked, dead) ← siteLinkProblems (out1 / "html-multi")
    for d in dead do IO.println s!"  {d}"
    check (dead.isEmpty && linksChecked > 0)
      s!"each of the {linksChecked} links PILean writes reaches its file and element"
    let pageHref :=
      (((list.splitOn "class=\"pilean-page-link\" href=\"").getD 1 "").splitOn "\"").headD ""
    let (pagePath, pageFrag) := match pageHref.splitOn "#" with
      | [p, f] => (p, f)
      | _ => ("", "")
    let landing ← try IO.FS.readFile (out1 / "html-multi" / pagePath / "index.html")
      catch _ => pure ""
    let slug := ((pagePath.drop 8).toString.splitOn "/").headD ""
    check (pagePath.startsWith "Figures/" && !pageFrag.isEmpty &&
        has landing (s!"id=\"pilean-page-{slug}\"><span class=\"pilean-figure-page-anchor\" " ++
          s!"aria-hidden=\"true\" id=\"{pageFrag}\"></span><div class=\"pilean-page-picture\">"))
      s!"a link to a figure's page lands on the empty anchor at the start of the page ({pageHref})"
    -- the figures' pages
    let pageOf := fun (d : String) => IO.FS.readFile (out1 / "html-multi" / "Figures" / d /
      "index.html")
    let tri ← pageOf "ManualExample.trianglePlot"
    check (has tri "data-pilean-standing=\"linked\"" &&
        has tri "Linked theorem: " && !has tri "Tied to its object" &&
        hasWords tri (linkCheckedText "ManualExample.trianglePoints_spec") &&
        has tri "data-lean-decl=\"ManualExample.trianglePoints_spec\"" &&
        has tri "Axioms: Classical.choice, Quot.sound, propext.")
      "a linked figure's page names its theorem with its axioms and what PILean checked of it"
    check (has tri ">trianglePoints_spec</" && has tri "panels" && !has tri "two_mul_triangle n")
      "the theorem's statement is shown, not its proof"
    check (hasWords tri theoremScopeText && hasWords tri theoremLinkText)
      "the page says what a linked theorem covers"
    -- theorems that name their figure and say nothing of it: the page says linked, what PILean
    -- checked and that it did not check what the theorem says, and nothing more
    for d in ["vacuousOr", "vacuousHypothesis", "vacuousBound"] do
      let pg ← pageOf s!"ManualExample.{d}"
      let t := s!"ManualExample.{d}_spec"
      check (has pg "data-pilean-standing=\"linked\"" && has pg "Linked theorem: " &&
          has pg s!"data-lean-decl=\"{t}\"" && hasWords pg (linkCheckedText t) &&
          hasWords pg theoremScopeText && hasWords pg theoremLinkText &&
          !has pg "Tied to its object" && !has pg "Proved by" && !has pg "proved by" &&
          !has pg "data-pilean-standing=\"proved\"")
        s!"the page of {d}, linked to a theorem that says nothing of it, says only what was checked"
    check (has tri "data-lean-decl=\"ManualExample.trianglePoints\"" &&
        has tri "data-lean-decl=\"ManualExample.triangle\"" && has tri "hl lean")
      "the page shows the declarations the figure is built from, highlighted"
    check (has tri "ok [recorded: linked to ManualExample.trianglePoints_spec]" &&
        has tri "pilean-figure-light" && has tri "pilean-figure-dark" &&
        has tri " download " && has tri " bytes")
      "the page has both pictures, its files to download and pilean-verify's verdicts"
    check (has tri "lake exe pilean-verify _out/html-multi/-verso-data/pilean-figures")
      "the page says how to reproduce"
    let slider ← pageOf "ManualExample.radiusSlider"
    check (has slider "data-pilean-standing=\"illustration\"" &&
        has slider "Illustration: no theorem is linked to it" &&
        !has slider "Linked theorem" && has slider "pilean-explorer-frame")
      "an illustration's page says so, and an explorer is embedded"
    let triPage := (((tri.splitOn "class=\"pilean-figure-page").getD 1 "").splitOn "</main>").headD ""
    check (!triPage.isEmpty && !has triPage "<script" && !hasHandler triPage)
      "a figure's page adds no script and no event handler"
    -- explorers and inline pictures
    let ex ← IO.FS.readFile (out1 / "html-multi" / "Explorers" / "index.html")
    let frames := (ex.splitOn "<li class=\"pilean-explorer-frame").length - 1
    check (frames == 9) s!"every frame of both explorers is in the page ({frames})"
    check (has ex "data-poster=\"\"" && has ex "class=\"pilean-explorer-controls\" hidden=\"\"")
      "without script the frames are listed and the controls hidden"
    check (has ex ("<input type=\"range\" data-axis=\"value\" min=\"0\" max=\"4\" " ++
        "step=\"1\" value=\"2\"") &&
      has ex "aria-valuetext=\"8/10\"") "the slider starts at the poster, with its value"
    check (has ex "data-action=\"prev\"" && has ex "data-action=\"next\"" &&
      has ex "Step 1 of 4" && has ex "aria-live=\"polite\"") "the stepper's controls and caption"
    check (has ex "role=\"group\" aria-labelledby=\"radius-caption\"" &&
      has ex "id=\"radius-caption\"") "the explorer is labelled by its caption"
    check (has ex "<script src=\"-verso-data/pilean-explorer.js\" defer=\"defer\">")
      "the explorer's script is a file of the site"
    check (← (out1 / "html-multi" / "-verso-data" / "pilean-explorer.js").pathExists)
      "the script file is written"
    check (has ex "html[data-theme=\"dark\"] #radius-x-f0 [fill=\"#ffffff\"]{fill:#16181c}" &&
      has ex "@media (prefers-color-scheme: dark){html:not([data-theme=\"light\"])")
      "inline pictures carry their dark theme rules"
    check (has ex "pilean-has-narrow" && has ex "pilean-inline-narrow")
      "an inline figure carries its narrow rendition"
    check (has ex "<title>ζ^1</title>") "inline titles are in the page"
    let start := "<svg xmlns=\"http://www.w3.org/2000/svg\" class=\"pilean-inline-svg"
    let svgParts := (ex.splitOn start).drop 1 |>.map fun p =>
      start ++ (p.splitOn "</svg>").headD "" ++ "</svg>"
    check (svgParts.length == 11 && svgParts.all Svg.isInert)
      s!"every inline picture is inert ({svgParts.length})"
    check (has ex "data-pilean-file=\"ManualExample/Figures/ManualExample.windowInline.svg\"" &&
      has ex "data-pilean-file=\"ManualExample/Figures/ManualExample.windowInline-narrow.svg\"")
      "an inline picture names its file"
    check (has ex
        "data-pilean-file=\"ManualExample/Figures/ManualExample.radiusSlider-frame-4.svg\"")
      "an explorer's frame names its file"
    check (!has ex "class=\"pilean-decl-link\"" && !has numbers "class=\"pilean-lean-link\"" &&
      !has numbers "class=\"pilean-site-link\"")
      "by default this genre's figures link no declaration"
    let exFigures := (ex.splitOn "<figure").drop 1 |>.map fun p => (p.splitOn "</figure>").headD ""
    let handler := fun (t : String) => ((t.splitOn " on").drop 1).any fun rest =>
      let name := (rest.takeWhile Char.isAlpha).toString
      !name.isEmpty && (rest.drop name.length).startsWith "="
    check (exFigures.length == 3 && exFigures.all (!has · "<script") &&
      exFigures.all (!handler ·)) "the explorers' markup has no script and no event handler"
    IO.println s!"size: the explorers page is {ex.utf8ByteSize} bytes for \
      {svgParts.length} pictures"
    -- the link modes
    let out3 := tmp / "site"
    let c5 ← generate ["--output", out3.toString, "--figure-lean-links", "site"]
    check (c5 == 0) "the manual is generated with links into the site"
    let ex3 ← IO.FS.readFile (out3 / "html-multi" / "Explorers" / "index.html")
    let numbers3 ← IO.FS.readFile (out3 / "html-multi" / "Numbers" / "index.html")
    check (has ex3
        "<a href=\"Numbers/#ManualExample___trianglePoints\" class=\"pilean-decl-link\"" &&
      has numbers3 "id=\"ManualExample___trianglePoints\"")
      "an inline element links to its declaration's documentation, an anchor of the site"
    check (!has ex3 "lean:decl/") "with links into the site there is no lean: link"
    let list3 ← IO.FS.readFile (out3 / "html-multi" / "Figures" / "index.html")
    check (has list3 "class=\"pilean-site-link\" href=\"Numbers/#triangle\"")
      "the figures page links a figure's declaration to the figure"
    let (siteChecked, siteDead) ← siteLinkProblems (out3 / "html-multi")
    for d in siteDead do IO.println s!"  {d}"
    check (siteDead.isEmpty && siteChecked > linksChecked)
      s!"with links into the site, each of the {siteChecked} links PILean writes reaches its target"
    let out4 := tmp / "ideil"
    let c6 ← generate ["--output", out4.toString, "--figure-lean-links", "ideil"]
    let ex4 ← IO.FS.readFile (out4 / "html-multi" / "Explorers" / "index.html")
    check (c6 == 0 && has ex4 "href=\"lean:decl/ManualExample.trianglePoints\"")
      "the editor's links are written on request"
    -- a damaged copy is found
    let damaged := tmp / "damaged"
    IO.FS.createDirAll damaged
    for f in files do
      let dst := damaged / f
      if let some p := dst.parent then IO.FS.createDirAll p
      IO.FS.writeBinFile dst (← IO.FS.readBinFile (figs / f))
    if let some f := svgs[0]? then IO.FS.writeFile (damaged / (f : String)) "<svg/>"
    let c3 ← generate ["--check-figures", damaged.toString]
    check (c3 == 1) "--check-figures fails on a damaged copy"
    let c4 ← generate ["--check-figures", figs.toString]
    check (c4 == 0) "--check-figures passes on the written folder"
    IO.FS.removeDirAll tmp
  let ((), (fails, n)) ← run.run (0, 0)
  IO.println s!"checks: {n - fails} of {n} hold"
  return if fails == 0 then 0 else 1
