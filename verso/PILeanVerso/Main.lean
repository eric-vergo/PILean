/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanVerso.Index
import PILeanVerso.Table
import PILeanVersoManual.Wrapper
import VersoBlueprint.Commands.Comparator

/-!
# The generator wrapper

A site's generator renders its figures with `withFigures`, around the generator it already has:

```lean
def main (args : List String) : IO UInt32 :=
  PILeanVerso.withFigures (%doc MyProject.Blueprint) site_figures% args fun doc args =>
    Informal.PreviewManifest.blueprintMainWithPreviewData doc args
      (extensionImpls := by exact extension_impls%)
```

`withFigures` finds the figure blocks of the document, renders their figures (and nothing else)
with PILean, keeps the result for the blocks, adds a page for each figure below the figures page
(`PILeanVersoManual.Page`), runs the generator on that document, and then checks what it wrote: a
file of the figures folder that differs from a fresh render or is missing fails the build, a file
left from an earlier build is reported, and a figure's page that differs from the render, the
written manifest or `pilean-verify` fails the build (`PILeanVerso.withFiguresFor`).

Its own command-line options are taken out before the generator sees the rest:

* `--figure-repo URL`, `--figure-commit SHA`, `--figure-source-prefix DIR/`: the repository, the
  commit and the folder of the sources in it, recorded in every file and used for the links to
  the source (the commit defaults to `git rev-parse HEAD` when a repository is given);
* `--check-figures DIR`: render the figures and compare them with the folder `DIR` (a site's
  `-verso-data/pilean-figures`, a published copy) as `pilean-build --check` does, without
  building the site: exit status 0 if it holds exactly the render, 1 otherwise;
* `--strict-figures`: also fail when the written folder has a file the render does not make;
* `--figure-inline-limit BYTES`: the most bytes of inline SVG one figure may put in the pages;
* `--figure-code highlight|signatures`: whether the figures' pages show highlighted source (the
  default; one `lake build +M:highlighted …` with the `lake` of `LAKE`) or signatures only;
* `--figure-lean-links ideil|site|none`: where the links to Lean declarations lead
  (`PILeanVerso.LeanLinks`): `ideil` by default (`options.leanLinks`); with `site` the build
  warns about each declaration it finds no place for in the site.
-/

namespace PILeanVerso

open Lean Verso Doc Genre Manual PILean.Trust

/-- How a Blueprint gets the figures' pages: its figure block, its figures page's block, and its
page block. -/
def pageBlocks : PageBlocks where
  figures := #[``Block.figure]
  listName := ``Block.figureList
  list := .other Block.figureList #[]
  page := fun d => .other (Block.figurePage d) #[]

/-- The figures a document uses, in document order (repeated as often as used). -/
def usedFigures (p : Part Manual) : Array FigureUse := partFigures #[``Block.figure] p

/-- Renders the figures `doc` uses from the table `figures` (`site_figures%`), adds a page for
each below the figures page, runs the generator `generate` on that document and the remaining
arguments, and checks the figures folders and the pages it wrote (see the module doc). `options`
are the defaults of the command-line options. The pages link the continuous-integration run that
built the site as Verso Blueprint's Comparator pages find it (`Informal.Commands.ciRunHref?`). -/
def withFigures (doc : Part Manual) (figures : SiteFigures) (args : List String)
    (generate : Part Manual → List String → IO UInt32) (options : SiteOptions := {}) :
    IO UInt32 :=
  withFiguresFor pageBlocks doc figures args generate options Informal.Commands.ciRunHref?

end PILeanVerso
