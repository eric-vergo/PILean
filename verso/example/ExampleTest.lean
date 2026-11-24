/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanVerso
import PictureExample

/-!
# Checks of the adapter

`lake test` builds and runs this module. Building it checks what the directive checks on a
`links :=` theorem and on the declaration of `figure_explorer`; running it checks the options
the directive accepts, the dark variants, the rendering of a site's figures (an unknown name, bad
options, the files and the manifest, a figure used in a way it cannot be shown, the inline
limit), the sizes read from the files, the links and the wrapper's arguments.
-/

open Lean Elab PILean PILean.Trust PILeanVerso

/-- Whether `checkTheorem fig thm` accepts the theorem. -/
def accepts (fig thm : Name) : CoreM Bool := do
  try
    discard <| checkTheorem fig (mkIdent thm)
    return true
  catch _ => return false

/-- A theorem that says nothing about any figure. -/
theorem unrelated : 2 + 2 = 4 := rfl

/-- Not a theorem. -/
def notATheorem : Nat := 3

/-- A statement about a declaration the figure does not use. -/
theorem aboutDivisors : Example.divisors24.length = 8 := rfl

/-- A true statement about a series the plot uses, which does not name the plot. -/
theorem aboutSeries : Example.cubicSeries.points.size = 33 := PILean.Plot.Series.ofExact_size ..

-- The theorem of each example figure is accepted.
#guard_msgs in
run_meta do
  for (f, t) in [(``Example.cubicPlot, ``Example.cubicPlot_spec),
      (``Example.collatzPlot, ``Example.collatzPlot_spec),
      (``Example.divisorGraph, ``Example.divisorGraph_spec),
      (``Example.circleAnimation, ``Example.circleAnimation_spec)] do
    unless ← accepts f t do throwError "{t} was refused for {f}"

-- A theorem about something else, a definition, and a theorem of another figure are refused;
-- so is a theorem about a declaration of the figure's module, whether the figure uses it or not.
#guard_msgs in
run_meta do
  for (f, t) in [(``Example.cubicPlot, ``unrelated), (``Example.cubicPlot, ``notATheorem),
      (``Example.cubicPlot, ``Example.collatzPlot_spec),
      (``Example.collatzPlot, ``Example.divisorGraph_spec),
      (``Example.cubicPlot, ``aboutDivisors), (``Example.cubicPlot, ``aboutSeries)] do
    if ← accepts f t then throwError "{t} was accepted for {f}"

-- `figure_explorer` takes explorers only.
#guard_msgs in
run_meta do
  unless (← explorerProblem? ``Example.radiusExplorer).isNone do
    throwError "an explorer was refused"
  let some msg ← explorerProblem? ``Example.cubicPlot | throwError "a plot was taken"
  unless (← msg.toString).startsWith "Example.cubicPlot has the type" do
    throwError "unexpected message {msg}"

/-- The figures of the example, rendered for a site. -/
def table : Array FigureEntry := site_figures%

/-- The figures of the example with what their pages show of the code. -/
def siteTable : SiteFigures := site_figures%

/-- The standing of a figure of the example, as `site_figures%` sets it. -/
def standingOf (n : String) : Option Standing := (table.find? (·.decl == n)).map (·.standing)

/-- The page data of a figure of the example. -/
def pageOf (n : String) : Option FigurePageData := (siteTable.pages.toOption.getD {})[n]?

/-- The plot rendered with a repository and a commit: its files and the manifest. -/
def plotSite : Except String SiteRender :=
  renderSite table #["Example.cubicPlot", "Example.cubicPlot"]
    { repo := some "https://example.org/r", commit := some "abcd1234" }

/-- The paths of the plot's files. -/
def plotPaths : Array String :=
  #["PictureExample/Figures/Example.cubicPlot-dark.pdf",
    "PictureExample/Figures/Example.cubicPlot-dark.png",
    "PictureExample/Figures/Example.cubicPlot-dark.svg",
    "PictureExample/Figures/Example.cubicPlot.pdf",
    "PictureExample/Figures/Example.cubicPlot.png", "PictureExample/Figures/Example.cubicPlot.svg"]

/-- The bytes of inline SVG the inline figure puts in a page: its picture and its narrow
rendition. -/
def inlineBytes : Nat :=
  match renderSite table #[{ decl := "Example.windowInline", inline := true }] {} with
  | .ok s => match s.figures["Example.windowInline"]? with
    | some f => (inlinePictures { decl := "", inline := true } f.files).foldl
        (fun n i => n + i.document.utf8ByteSize) 0
    | none => 0
  | .error _ => 0

/-- Whether rendering `used` fails with a message that contains `what`. -/
def failsWith (used : Array FigureUse) (opts : SiteOptions) (what : String) : Bool :=
  match renderSite table used opts with
  | .ok _ => false
  | .error e => (e.splitOn what).length > 1

/-- A site's options with a repository and a commit. -/
def withRepo : SiteOptions := { repo := some "https://e.org/r", commit := some "abcd" }

/-- The checks that run code: a name and whether it holds. -/
def checks : Array (String × Bool) := #[
  ("width: lengths accepted",
    isCssLength "60%" && isCssLength "24rem" && isCssLength "480px" && isCssLength "12.5em"),
  ("width: anything else refused",
    !isCssLength "60" && !isCssLength "1e3px" && !isCssLength "calc(1px)" &&
      !isCssLength "-3px" && !isCssLength "%" && !isCssLength "1.2.3px" &&
      !isCssLength "10px;x"),
  ("dark: the light style has a dark variant", (Style.darkVariant? Style.light).isSome),
  ("dark: other colours have none",
    (Style.darkVariant? { Style.light with background := ⟨1, 2, 3, 255⟩ }).isNone),
  ("dark: sizes are kept",
    (Style.darkVariant? { Style.light with lineWidth := 3 }).map (·.lineWidth) == some 3),
  ("dark: the colours are the dark style's",
    (Style.darkVariant? Style.light).map (·.background) == some Style.dark.background),
  ("table: fifteen figures", table.size == 15),
  ("standing: a figure linked by figure_links has the standing linked, with its theorem",
    standingOf "Example.divisorHasse" == some (.linked #["Example.divisorHasse_spec"]) &&
    standingOf "Example.reductionSquare" == some (.linked #["Example.reductionSquare_spec"])),
  ("standing: a figure marked as an illustration is one, marked",
    standingOf "Example.sketch" == some (.illustration true)),
  ("standing: an explorer without a theorem is an unmarked illustration",
    standingOf "Example.radiusExplorer" == some (.illustration false)),
  ("standing: a name with markup keeps its theorem",
    standingOf "Example.«hasse <b>\"&'»" == some (.linked #["Example.«hasse <b>\"&'_spec»"])),
  ("pages: the table has the page data of every figure",
    table.all fun e => (pageOf e.decl).isSome),
  ("pages: the square's page shows the definitions of its object and of its theorem's statement",
    ((pageOf "Example.reductionSquare").map fun p => p.related.map (·.name)) ==
      some #["Example.reductions", "Example.reductionMaps", "Example.reduction"]),
  ("pages: nothing of other packages is shown in full, only named",
    table.all fun e => match pageOf e.decl with
      | some p => p.related.all (·.module.startsWith "PictureExample") &&
          p.external.all (!·.module.startsWith "PictureExample")
      | none => false),
  ("pages: a caption that names a theorem the standing does not record fails the build",
    failsWith #[{ decl := "Example.sketch", proves := some "Example.divisorHasse_spec" }] {}
      "not linked to it"),
  ("render: an unknown name is refused",
    (renderSite table #["Example.nope"] {}).toOption.isNone),
  ("render: a script address as repository is refused",
    (renderSite table #[] { repo := some "javascript:alert(1)" }).toOption.isNone),
  ("render: a commit that is not hexadecimal is refused",
    (renderSite table #[] { commit := some "HEAD" }).toOption.isNone),
  ("render: a prefix that climbs is refused",
    (renderSite table #[] { sourcePrefix := "../" }).toOption.isNone),
  ("render: a prefix without a final slash is refused",
    (renderSite table #[] { sourcePrefix := "a/b" }).toOption.isNone),
  ("render: a folder prefix is accepted",
    (renderSite table #[] { sourcePrefix := "a/b/" }).toOption.isSome),
  ("render: a plot gives six files, once, with the commit, inert SVG", match plotSite with
    | .ok s => s.files.map (·.entry.path) == plotPaths &&
        s.files.all (·.entry.commit == some "abcd1234") &&
        (s.manifest.splitOn "\"path\"").length == 7 &&
        s.files.all fun f => f.entry.format != "svg" ||
          ((String.fromUTF8? f.bytes).map Svg.isInert).getD false
    | .error _ => false),
  ("render: an animation gives its SVG, APNG, GIF and still frame",
    match renderSite table #["Example.circleAnimation"] {} with
    | .ok s => (s.figures["Example.circleAnimation"]?.map fun f =>
        f.files.map fun sf => (sf.name, sf.format.name)) ==
          some #[("", "svg"), ("", "apng"), ("", "gif"), ("-poster", "png"), ("-poster", "pdf")]
    | .error _ => false),
  ("use: figure_explorer on a plot fails the build",
    failsWith #[{ decl := "Example.cubicPlot", explorer := true }] {} "is not an explorer"),
  ("use: inline on a graph without an inline picture fails the build",
    failsWith #[{ decl := "Example.divisorGraph", inline := true }] {} "has no inline picture"),
  ("use: an explorer and an inline figure are accepted",
    (renderSite table #[{ decl := "Example.radiusExplorer", explorer := true },
      { decl := "Example.windowInline", inline := true }] {}).toOption.isSome),
  ("limit: a figure shown as a file is not counted",
    (renderSite table #["Example.windowInline", "Example.radiusExplorer"]
      { inlineLimit := 1 }).toOption.isSome),
  ("limit: one figure's pictures are counted once, together",
    inlineBytes > 0 &&
      (renderSite table #[{ decl := "Example.windowInline", inline := true },
        { decl := "Example.windowInline", inline := true }]
        { inlineLimit := inlineBytes }).toOption.isSome &&
      failsWith #[{ decl := "Example.windowInline", inline := true }]
        { inlineLimit := inlineBytes - 1 } "bytes of inline SVG"),
  ("links: lean:decl/ links are encoded as Verso Blueprint encodes them",
    [``Example.cubic, `Example.«odd "name" <a href=x> & 'more'», `α.β, `«a b/c?d#e»].all
      fun n => leanDeclHref n.toString == Informal.LeanSourceAnchor.declHref n),
  ("links: the modes' names", ["ideil", "site", "none"].map LeanLinks.ofString? ==
    [some .ideil, some .site, some .none] && LeanLinks.ofString? "IDEiL" == none),
  ("dom: ids are kept to letters, digits, - and _",
    domSafe "3d-odd" == "3d-odd" && domSafe "a\"b <c>é" == "a_b__c__"),
  ("theme: an id that starts with a letter is selected by id",
    themeCss "f3" #[("#000000", "#ffffff")] #[] |>.startsWith
      "html[data-theme=\"dark\"] #f3 [fill=\"#000000\"]{fill:#ffffff}"),
  ("theme: an id that starts with a digit is selected by its id attribute",
    themeCss "3d" #[("#000000", "#ffffff")] #[] ==
      "html[data-theme=\"dark\"] svg[id=\"3d\"] [fill=\"#000000\"]{fill:#ffffff}" ++
      "html[data-theme=\"dark\"] svg[id=\"3d\"] [stroke=\"#000000\"]{stroke:#ffffff}" ++
      "@media (prefers-color-scheme: dark){" ++
      "html:not([data-theme=\"light\"]) svg[id=\"3d\"] [fill=\"#000000\"]{fill:#ffffff}" ++
      "html:not([data-theme=\"light\"]) svg[id=\"3d\"] [stroke=\"#000000\"]{stroke:#ffffff}}"),
  ("prefix: an element inside a link is not linked again",
    let inner := Svg.el "g" #[("data-lean-decl", "B")] #[Svg.el "path" #[]]
    let outer := Svg.el "g" #[("data-lean-decl", "A")] #[inner]
    let out := Svg.render 0 (prefixNode "p-" (fun n => some s!"#{n}") false outer)
    (out.splitOn "<a ").length == 2),
  ("labels: a caption with the label's separators is kept whole",
    let fs : FrameSet :=
      { axisName := "x = y", axisValues := #["1 · 2"], stepCaptions := #["Step 9 of 9: a · b"],
        frames := #[default] }
    frameValue fs 0 == "1 · 2" && frameStep fs 0 == "Step 9 of 9: a · b" &&
      frameCounter fs 0 == "Step 1 of 1"),
  ("labels: the steps of a second parameter say its value, with no counter",
    let fs : FrameSet :=
      { axisName := "r", axisValues := #["1", "2"], stepName := "c", stepCaptions := #["0", "1/4"],
        frames := #[default, default, default, default] }
    frameCounter fs 3 == "" && frameStepText fs 3 == "c = 1/4" &&
      frameLabel fs 3 == "r = 2 · c = 1/4"),
  ("markup: a family of two parameters has a slider for each and names the played one",
    let fs : FrameSet :=
      { axisName := "r", axisValues := #["1", "2"], stepName := "c", stepCaptions := #["0", "1/4"],
        frames := #[default, default, default, default] }
    let h := explorerHtml "x" fs (fun _ => none) "alt" "Figure 1"
    (h.splitOn "type=\"range\"").length == 3 && (h.splitOn "data-axis=\"step\"").length == 2 &&
      (h.splitOn "aria-label=\"Play c\"").length == 2 &&
      (h.splitOn "data-step-say=\"c = 1/4\"").length == 3),
  ("size: read from the SVG and the PNG, none for the PDF", match plotSite with
    | .ok s => s.files.all fun f =>
        if f.entry.format == "pdf" then imageSize? .pdf f.bytes == none
        else imageSize? (if f.entry.format == "svg" then .svg else .png) f.bytes == some (640, 400)
    | .error _ => false),
  ("size: zero and missing refused",
    imageSize? .svg "<svg width=\"0\" height=\"3\"/>".toUTF8 == none &&
      imageSize? .png ByteArray.empty == none),
  ("link: file and line at the commit",
    repoHref withRepo "A/B.lean" 7 == some "https://e.org/r/blob/abcd/A/B.lean#L7"),
  ("link: none without a commit", repoHref { repo := some "https://e.org/r" } "A/B.lean" 7 == none),
  ("link: none for a name a link cannot carry", (repoHref withRepo "A/<x>.lean" 7).isNone),
  ("arguments: the wrapper's are taken out",
    (parseWrapperArgs {} ["--figure-repo", "https://e.org", "--output", "o", "--strict-figures"]
      |>.toOption.map fun w => (w.options.repo, w.strict, w.rest)) ==
        some (some "https://e.org", true, ["--output", "o"])),
  ("arguments: a missing value is refused",
    (parseWrapperArgs {} ["--check-figures"]).toOption.isNone),
  ("arguments: the link mode is taken out",
    (parseWrapperArgs {} ["--figure-lean-links", "site", "--output", "o"]
      |>.toOption.map fun w => (w.options.leanLinks, w.rest)) == some (.site, ["--output", "o"])),
  ("arguments: an unknown link mode is refused",
    (parseWrapperArgs {} ["--figure-lean-links", "web"]).toOption.isNone &&
      (parseWrapperArgs {} ["--figure-lean-links"]).toOption.isNone),
  ("arguments: the last output folder counts",
    outputDir ["--output", "a", "x", "--output", "b"] == "b" && outputDir [] == "_out")]

/-- Runs the checks; exit status 1 if one fails. -/
def main : IO UInt32 := do
  let failed := checks.filter (!·.2)
  for (n, _) in failed do IO.eprintln s!"FAIL {n}"
  IO.println s!"checks: {checks.size - failed.size} of {checks.size} hold"
  return if failed.isEmpty then 0 else 1
