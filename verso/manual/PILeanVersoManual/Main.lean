/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanVersoManual.Index
import PILeanVersoManual.Table

/-!
# The generator wrapper, in the Manual genre

A manual's generator renders its figures with `withFigures`, around `manualMain`:

```lean
def main (args : List String) : IO UInt32 :=
  PILeanVerso.Manual.withFigures (%doc MyManual) site_figures% args fun args =>
    manualMain (%doc MyManual) (options := args)
```

`withFigures` finds the figure blocks of the document, renders their figures (and nothing else)
with PILean, keeps the result for the blocks, runs the generator, and then checks that the
figures folder the generator wrote holds exactly the files of this render: a file that differs
from a fresh render or is missing fails the build; a file left from an earlier build is reported.
Its own command-line options are taken out before the generator sees the rest:

* `--figure-repo URL`, `--figure-commit SHA`, `--figure-source-prefix DIR/`: the repository, the
  commit and the folder of the sources in it, recorded in every file and used for the default
  links to the source (the commit defaults to `git rev-parse HEAD` when a repository is given);
* `--check-figures DIR`: render the figures and compare them with the folder `DIR` without
  building the site: exit status 0 if it holds exactly the render, 1 otherwise;
* `--strict-figures`: also fail when the written folder has a file the render does not make.

`declStyle` sets how the figures' source lines show a declaration and its place
(`defaultDeclStyle` when not given).
-/

namespace PILeanVerso.Manual

open Lean Verso Doc Genre Manual PILean.Trust PILeanVerso

/-- The figure declarations a document's figure blocks use, in document order. -/
def usedFigures (p : Part Manual) : Array String := partFigures #[``Block.figure] p

/-- Renders the figures `doc` uses from the table `figures` (`site_figures%`), runs the generator
`generate` on the remaining arguments, and checks the figures folders it wrote (see the module
doc). `options` are the defaults of the command-line options; `declStyle` is how the source lines
show declarations. -/
def withFigures (doc : Part Manual) (figures : Array FigureEntry) (args : List String)
    (generate : List String → IO UInt32) (options : SiteOptions := {})
    (declStyle : DeclStyle := defaultDeclStyle) : IO UInt32 := do
  declStyleRef.set declStyle
  withFiguresFor (usedFigures doc) figures args generate options

end PILeanVerso.Manual
