/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILean
import PILeanManual.Meta

open Verso.Genre Manual
open PILeanManual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Optional Packages" =>
%%%
tag := "packages"
%%%

The core library has no dependencies. What needs one lives in a package of its own, in a folder
of the repository, which depends on the core through the parent folder and pins its own
dependencies. A project requires such a package with the folder after the commit:

```
require «pilean-verso-manual» from git "https://github.com/eric-vergo/PILean" @ "<commit>" / "verso/manual"
```

:::table +header
*
  * Package
  * Folder
  * Adds
  * What it is for
*
  * `pilean-verso-manual`
  * {sourceFile}`verso/manual`
  * Verso
  * PILean figures in documents of Verso's Manual genre: the `:::figure` directive, references to
    figures, the figures page, and the generator wrapper that renders every figure a document
    uses, with its source record, fingerprint and manifest, and checks the files. This manual is
    built with it.
*
  * `pilean-verso`
  * {sourceFile}`verso`
  * Verso, Verso Blueprint
  * The same for Verso Blueprint sites.
*
  * `pilean-leantex`
  * {sourceFile}`leantex`
  * LeAnTeX
  * A text engine that typesets every label as LaTeX ({ref "text-engines"}[Other Engines]).
*
  * `pilean-mathlib`
  * {sourceFile}`mathlib`
  * Mathlib
  * A specification over the real numbers of what it means for a plotted polyline to be near the
    graph of a function, a general theorem about exact plots, and one figure with its theorem
    ({ref "proofs-real"}[Plots Against the Real Numbers]). It is an experiment.
:::

Each folder's `README.md` says how to use the package and what its tests check.

# Figures in a Verso Manual
%%%
tag := "packages-manual"
%%%

In a chapter, after `import PILeanVersoManual` and `open PILeanVerso.Manual`, a figure is a
directive naming a declaration with `@[figure]`:

```
:::figure MyManual.Figures.layers (alt := "The layers of the code, …") (label := "layers")
The layers of the code and the imports between them.
:::
```

The options are `alt` (required: what a reader who cannot see the picture needs to know), `label`
(for `{figref "…"}[]`), `title`, `format` (`svg` by default, `png`, `apng` or `gif`), `width` (a
CSS length), `backdrop` (a picture of the site the figure is drawn over) and `links` (a theorem
about the figure, accepted only under the rule of `figure_links`, {ref "proofs-link"}[Linking a
Theorem to a Picture], and only when a `figure_links` command links the two; `proves` is the same
option). An
empty body takes the declaration's docstring as the caption. The generator wraps `manualMain`,
and renders the document it is given, which has the figures' pages added:

```
def main (args : List String) : IO UInt32 :=
  PILeanVerso.Manual.withFigures (%doc MyManual) site_figures% args fun doc args =>
    manualMain doc (options := args)
```

When the manual is generated, every figure it uses is rendered by PILean, every SVG must pass
{name}`PILean.Svg.isInert`, and a file of the figures folder the generator wrote that is missing or
differs from this render fails the build (a leftover file is reported; `--strict-figures` makes it
fail too). Light and dark pictures are switched by the stylesheet alone, following the
page's theme, with no script. Every figure of this manual is made this way: its caption ends with
the declaration that made it, its file and line, the start of its fingerprint, and its theorem
when it has one, and a link to its page.

Every figure has a page of its own, below the page that lists them: the picture at full size with
its files to download; its number, caption and the places that show it; its standing, "Linked
theorem: T" with the statement of T as Lean, the axioms it rests on and what PILean checked of it,
or "Illustration: no theorem is linked to it", derived when the generator is built from the
`figure_links` links that pass their rule again there; the figure's declaration in full and the
definitions of the manual's own code that its value and the theorems' statements use, highlighted
with their hovers and linked to their source; the fingerprint, renderer, text engine and
`pilean-verify` verdict of each file, the toolchain, the packages, the commit and the
continuous-integration run; and the commands that build the files again and check them. After the
site is written, the generator checks every page against the files, the manifest and
`pilean-verify`, and fails when one differs. The links to a page (the caption's "code, standing and
provenance" and the list's) lead to an empty anchor at the start of the page, which takes no space
and is never highlighted, so the reader arrives at the top of the page with its title in view. The
Verso Blueprint adapter's `README.md` has the caps and the exact rules. `lake exe pilean-site-links
SITE` (from `pilean-verso-manual`) checks that every link PILean writes into a built site reaches
its file and the element its fragment names; `--all` holds every link of the site to that rule.
