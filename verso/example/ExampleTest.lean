/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanVerso
import Example

/-!
# Checks of the adapter

`lake test` builds and runs this module. Building it checks what the directive checks on a
`proves :=` theorem; running it checks the options the directive accepts, the dark variants, the
rendering of a site's figures (an unknown name, bad options, the files and the manifest), the
sizes read from the files, the links and the wrapper's arguments.
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

-- The theorem of each example figure is accepted.
#guard_msgs in
run_meta do
  for (f, t) in [(``Example.cubicPlot, ``Example.cubicPlot_spec),
      (``Example.collatzPlot, ``Example.collatzPlot_spec),
      (``Example.divisorGraph, ``Example.divisorGraph_spec),
      (``Example.circleAnimation, ``Example.circleAnimation_spec)] do
    unless ← accepts f t do throwError "{t} was refused for {f}"

-- A theorem about something else, a definition, and a theorem of another figure are refused;
-- so is a theorem about a declaration of the figure's module that the figure does not use.
#guard_msgs in
run_meta do
  for (f, t) in [(``Example.cubicPlot, ``unrelated), (``Example.cubicPlot, ``notATheorem),
      (``Example.cubicPlot, ``Example.collatzPlot_spec),
      (``Example.collatzPlot, ``Example.divisorGraph_spec),
      (``Example.cubicPlot, ``aboutDivisors)] do
    if ← accepts f t then throwError "{t} was accepted for {f}"

/-- The figures of the example, rendered for a site. -/
def table : Array FigureEntry := site_figures%

/-- The plot rendered with a repository and a commit: its files and the manifest. -/
def plotSite : Except String SiteRender :=
  renderSite table #["Example.cubicPlot", "Example.cubicPlot"]
    { repo := some "https://example.org/r", commit := some "abcd1234" }

/-- The paths of the plot's files. -/
def plotPaths : Array String :=
  #["Example/Figures/Example.cubicPlot-dark.png", "Example/Figures/Example.cubicPlot-dark.svg",
    "Example/Figures/Example.cubicPlot.png", "Example/Figures/Example.cubicPlot.svg"]

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
  ("table: four figures", table.size == 4),
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
  ("render: a plot gives four files, once, with the commit, inert SVG", match plotSite with
    | .ok s => s.files.map (·.entry.path) == plotPaths &&
        s.files.all (·.entry.commit == some "abcd1234") &&
        (s.manifest.splitOn "\"path\"").length == 5 &&
        s.files.all fun f => f.entry.format != "svg" ||
          ((String.fromUTF8? f.bytes).map Svg.isInert).getD false
    | .error _ => false),
  ("render: an animation gives its SVG, APNG, GIF and still frame",
    match renderSite table #["Example.circleAnimation"] {} with
    | .ok s => (s.figures["Example.circleAnimation"]?.map fun f =>
        f.files.map fun sf => (sf.name, sf.format.name)) ==
          some #[("", "svg"), ("", "apng"), ("", "gif"), ("-poster", "png")]
    | .error _ => false),
  ("size: read from the SVG and the PNG", match plotSite with
    | .ok s => s.files.all fun f =>
        imageSize? (if f.entry.format == "svg" then .svg else .png) f.bytes == some (640, 400)
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
  ("arguments: the last output folder counts",
    outputDir ["--output", "a", "x", "--output", "b"] == "b" && outputDir [] == "_out")]

/-- Runs the checks; exit status 1 if one fails. -/
def main : IO UInt32 := do
  let failed := checks.filter (!·.2)
  for (n, _) in failed do IO.eprintln s!"FAIL {n}"
  IO.println s!"checks: {checks.size - failed.size} of {checks.size} hold"
  return if failed.isEmpty then 0 else 1
