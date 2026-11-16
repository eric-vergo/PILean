# PILean figures in Verso documents

`pilean-verso` puts PILean figures into Verso Manual-genre documents, in particular
[Verso Blueprint](https://github.com/leanprover/verso-blueprint) sites. A figure is the value of a
Lean declaration marked `@[figure]`; the site's build draws it, writes the files with their source
record and fingerprint and a manifest, and the page shows the picture with a caption that leads
back to the declaration and to a theorem about it.

PILean itself has no dependencies. This package, in its own folder, adds Verso and Verso
Blueprint (pinned in `lakefile.lean`) and depends on PILean through the parent folder. A plain
Verso manual without Verso Blueprint uses `pilean-verso-manual` (the folder
[`manual/`](manual/README.md)), on which this package builds.

## Use

In a project's `lakefile.lean`:

```lean
require «pilean-verso» from git "https://github.com/eric-vergo/PILean" @ "<commit>" / "verso"
```

A figure and a theorem about it, in an ordinary Lean module:

```lean
import PILean
import PILean.Trust.Attr

/-- The divisors of 24 ordered by divisibility. -/
@[figure]
def divisorGraph : PILean.Graph := Graph.ofRelation divisors24 covers toString

theorem divisorGraph_spec : ... divisorGraph ... := ...
```

In a Blueprint chapter (after `import PILeanVerso` and `open PILeanVerso`):

```
:::figure MyProject.divisorGraph (label := "divisors") (proves := MyProject.divisorGraph_spec)
The divisors of 24; an edge joins $`a` to $`b` when $`b` covers $`a`.
:::

As {figref "divisors"}[] shows, ...
```

and, in the document's root, `{figure_list}` for a page that lists every figure. The generator
wraps the one it has:

```lean
def main (args : List String) : IO UInt32 :=
  PILeanVerso.withFigures (%doc MyProject.Blueprint) site_figures% args fun args =>
    Informal.PreviewManifest.blueprintMainWithPreviewData (%doc MyProject.Blueprint) args
      (extensionImpls := by exact extension_impls%)
```

The directive's options: `label`, `alt` (the text alternative; the declaration's doc string by
default), `title`, `format` (`svg` by default, or `png`, `apng`, `gif`), `width` (a CSS length) and
`proves` (a theorem). An empty body takes the declaration's doc string as the caption.

## What a reader sees

* The picture, in the dark style when the page is dark (plots and graphs in PILean's light
  colours get a dark twin; other figures are shown as they are). An animation plays in its
  animated SVG, and a reader who asks for reduced motion sees its still frame instead. No script
  is involved: the pictures are `<img>` elements of files of the site.
* "Figure 1.2" and the caption, numbered as the Blueprint numbers its blocks
  (`verso.blueprint.numbering`, `verso.blueprint.subNumberingPrefix`), with a counter of its own.
* A source line: the declaration that made the picture and its file and line; the fingerprint
  (shortened, whole on hover and when copied); the theorem, if named. When the site is built with
  a repository (`--figure-repo URL`, and the commit from `--figure-commit` or `git rev-parse HEAD`)
  the file and line link to the repository at that commit. A viewer that sets `data-lean-links` on
  the page's root element (an editor showing the site next to the code) gets `lean:decl/<Name>`
  links instead of plain names, as Verso Blueprint's own Lean anchors.
* The figures page: every figure with a small picture, its source, fingerprint, files and theorem,
  and a link to the manifest.

## What the build checks

* When the chapter is elaborated: the declaration has `@[figure]`; the theorem named by `proves`
  exists, is a theorem, depends on no `sorry` and no axiom beyond `propext`, `Classical.choice` and
  `Quot.sound`, and its statement names the figure itself (PILean's rule, `figure_proves`: the
  figure's constant occurs in the statement; a statement about a definition the figure is built
  from is refused). The rule is about names: the link under the caption is a pointer to a
  statement to read, not a certificate that the picture is correct. `format` and `width` are
  valid.
* When the site is generated: every figure the document uses is rendered with PILean
  (`pilean-build`'s rendering, file names and manifest), every SVG must be inert
  (`PILean.Svg.inertProblem?`: no script, no event handler, nothing loaded from elsewhere), and
  after the generator has written the site, the figures folder
  (`<output>/html-multi/-verso-data/pilean-figures`) must hold exactly the files of this render: a
  missing or different file fails the build, a file left from an earlier build is reported
  (`--strict-figures` fails on it too).
* `--check-figures DIR` renders the figures and compares them with a folder (a published copy, a
  committed one) without building the site, as `pilean-build --check` does.
* `lake exe pilean-verify <output>/html-multi/-verso-data/pilean-figures` checks a folder against
  its manifest and the source records inside the files.

The output is deterministic: two builds of the same sources, with the same repository and
commit, write the same bytes.

## Limits

* Figures are rendered by the generator process. With `vbp build`, which runs the generator
  through Lean's interpreter, PILean's code runs interpreted unless the project builds the
  generator as an executable (as the example does): use a `lean_exe` for sites with many raster
  figures.
* A resident build session (`vbp build --resident`) renders the figures of the document it
  started with; a chapter that starts using a new figure needs `build --full`.
* The repository links have the form `<repo>/blob/<commit>/<prefix><file>#L<line>` (GitHub's);
  `--figure-source-prefix DIR/` names the folder of the sources within the repository.
* TeX and PDF output show a note in place of the picture.

## The example

`example/` is a small Blueprint with a function plot, a data plot, a graph of a relation and an
animation, each with its theorem:

```
cd example
lake build example-blueprint
lake exe example-blueprint --output _out/site
```

`example/tests/` has the checks run on it: `check-site.sh` (the build, the folder check, the
reproducibility of two builds, `--check-figures` on a damaged copy, `pilean-verify`) and
`browser_check.py` (the pages in a headless Chromium: both themes, reduced motion, the source
links, the figures page, narrow windows, a strict content policy).
