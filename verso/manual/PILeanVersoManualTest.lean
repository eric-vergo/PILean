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
    check (svgs.size == 6) s!"six SVG files, light and dark ({svgs.size})"
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
