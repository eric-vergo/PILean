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
  PILeanVerso.Manual.withFigures (%doc ManualExample) site_figures% args fun args =>
    manualMain (%doc ManualExample) (options := args) (config := exampleConfig)

/-- The files below `dir`, relative to it, sorted. -/
partial def filesBelow (dir : System.FilePath) (rel : String := "") : IO (Array String) := do
  let mut out := #[]
  for e in ← dir.readDir do
    let r := if rel.isEmpty then e.fileName else rel ++ "/" ++ e.fileName
    if ← e.path.isDir then out := out ++ (← filesBelow e.path r) else out := out.push r
  return out.qsort (· < ·)

/-- Whether `s` contains `t`. -/
def has (s t : String) : Bool := (s.splitOn t).length > 1

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
    check (svgs.size == 12) s!"twelve SVG files, light, dark and narrow ({svgs.size})"
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
    check (has numbers ">Theorem<" && !has numbers "Proved by" &&
      has numbers "ManualExample.trianglePoints_spec") "the theorem is named"
    check (has numbers "ManualExample/Figures.lean:") "the source line names the file and line"
    check (has numbers "class=\"pilean-figref\"") "the reference links to the figure"
    let marks ← IO.FS.readFile (out1 / "html-multi" / "Marks-over-a-picture" / "index.html")
    check (has marks "pilean-figure-stack" && has marks "-verso-data/backdrop-dark.svg" &&
      has marks "-verso-data/backdrop-light.svg") "a figure is drawn over its backdrop"
    check (has marks "aria-hidden=\"true\"") "the drawing over a backdrop is hidden from readers"
    let figureParts := (numbers.splitOn "<figure").drop 1 |>.map fun p =>
      (p.splitOn "</figure>").headD ""
    check (figureParts.length == 2 && figureParts.all (!has · "<script") &&
      figureParts.all (!has · " on")) "the figures' markup has no script and no event handler"
    let list ← IO.FS.readFile (out1 / "html-multi" / "Figures" / "index.html")
    check (has list "pilean-figure-index" && has list "Figure 3") "the figures page lists them"
    check (has list "ManualExample.radiusSlider" && has list "ManualExample.wordSteps")
      "the figures page lists the explorers"
    -- explorers and inline pictures
    let ex ← IO.FS.readFile (out1 / "html-multi" / "Explorers" / "index.html")
    let frames := (ex.splitOn "<li class=\"pilean-explorer-frame").length - 1
    check (frames == 9) s!"every frame of both explorers is in the page ({frames})"
    check (has ex "data-poster=\"\"" && has ex "class=\"pilean-explorer-controls\" hidden=\"\"")
      "without script the frames are listed and the controls hidden"
    check (has ex "<input type=\"range\" min=\"0\" max=\"4\" step=\"1\" value=\"2\"" &&
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
    let svgParts := (ex.splitOn "<svg").drop 1 |>.map fun p =>
      "<svg" ++ (p.splitOn "</svg>").headD "" ++ "</svg>"
    check (svgParts.length == 11 && svgParts.all Svg.isInert)
      s!"every inline picture is inert ({svgParts.length})"
    let exFigures := (ex.splitOn "<figure").drop 1 |>.map fun p => (p.splitOn "</figure>").headD ""
    let handler := fun (t : String) => ((t.splitOn " on").drop 1).any fun rest =>
      let name := rest.takeWhile Char.isAlpha
      !name.isEmpty && (rest.drop name.length).startsWith "="
    check (exFigures.length == 3 && exFigures.all (!has · "<script") &&
      exFigures.all (!handler ·)) "the explorers' markup has no script and no event handler"
    IO.println s!"size: the explorers page is {ex.utf8ByteSize} bytes for \
      {svgParts.length} pictures"
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
