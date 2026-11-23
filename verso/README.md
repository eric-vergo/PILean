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
default), `title`, `format` (`svg` by default, or `png`, `apng`, `gif`), `width` (a CSS length),
`inline := true` (the picture as an `svg` element of the page, see below) and `proves` (a
theorem). An empty body takes the declaration's doc string as the caption.

An explorer (a declaration of type `PILean.Explorer`, made with `Plane.slider`, `Plane.stepper`
or `Explorer.grid`) has its own directive, with the same options:

```
:::figure_explorer MyProject.radiusExplorer (label := "radius") (alt := "A disk whose radius grows from 0.6 to 1.")
The disk as its radius grows.
:::
```

## Links to Lean

One option of the site decides where a declaration's name leads, in the source line, on the
figures page and on each element of an inline picture that names a declaration (`.declRef`,
`data-lean-decl`): `--figure-lean-links MODE` on the generator's command line, or
`options := { leanLinks := .site }` given to `withFigures` (`PILeanVerso.LeanLinks`).

* `ideil` (the default): `lean:decl/<Name>` links, for an editor that shows the site beside the
  code. In the source line they are shown only when the page's root has `data-lean-links`
  (plain names otherwise); in an inline picture each such element is a link.
* `site`: a link to the declaration's place in the built site: the row of the Lean panel of the
  Blueprint entry that names it (`(lean := "...")`), else an inline Lean block that defines it,
  else the figure it draws (on the figures page; under the figure itself the name is not a link
  to where the reader already is). A declaration with none of these is shown without a link,
  and the build prints `figures: warning: <Name> has no place in the site to link to`.
* `none`: no links; names are text, and an element of a picture keeps its hover text and is no
  tab stop.

A link is never put inside another.

## What a reader sees

* The picture, in the dark style when the page is dark (plots and graphs in PILean's light
  colours get a dark twin; other figures are shown as they are), centred and never wider than
  its column, also in the narrow text column of the side-by-side layout. An animation plays in
  its animated SVG, and a reader who asks for reduced motion sees its still frame instead. A
  figure shown as a file is an `<img>` of the site and needs no script; the stylesheet switches
  the light and dark files.
* With `inline := true`, the picture is an `svg` element of the page (its narrow rendition on
  screens up to 560 px wide, when it has one): the titles of its elements show on hover, the
  elements that name a declaration link to it (see "Links to Lean"), and one picture serves both
  themes through a `style` element inside it. A content policy must allow those `style`
  elements, with `style-src 'unsafe-inline'` or the hash of each; nothing else of a figure needs
  inline style except a `width :=`, which is a `style` attribute (`style-src-attr`). No script is
  needed for an inline picture.
* An explorer: every frame is in the page. The site's script `pilean-explorer.js` (a file of the
  site, loaded deferred; no network, no `eval`, no `innerHTML`) shows one frame at a time with a
  slider for the parameter (named "Value of <axis> in Figure <n>", its value said by the slider
  itself), previous, play and next for the steps (one polite status line says the step after
  previous or next; nothing is said on loading or while the steps play), and zoom in, zoom out
  and reset. The page keeps its own scrolling, as embedded maps do with cooperative gestures: the
  wheel and a one-finger swipe scroll the page; Ctrl or ⌘ with the wheel (a trackpad pinch) zooms
  the picture about the pointer, and wheel events within 400 ms of a zoom keep zooming; two
  fingers pinch and pan; a mouse drag pans; on the focused picture `+`, `-` and `0` zoom and
  reset and the arrows pan. Frames of different sizes keep their own view. Every control is at
  least 44 by 44 pixels. With reduced motion there is no play button. Without script the frames
  are a grid in their order, as many columns as fit, each with its value and step under it, the
  frame shown first with script outlined, and nothing in it is focusable.
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

* When the chapter is elaborated: the declaration has `@[figure]`, and for `figure_explorer` it is
  a `PILean.Explorer` (otherwise an error says its type and to use `figure`); the theorem named
  by `proves`
  exists, is a theorem, depends on no `sorry` and no axiom beyond `propext`, `Classical.choice` and
  `Quot.sound`, and its statement names the figure itself (PILean's rule, `figure_proves`: the
  figure's constant occurs in the statement once its `let`s and beta-redexes are reduced; a
  statement about a definition the figure is built from is refused). The rule is about names:
  the link under the caption is a pointer to a statement to read, not a certificate that the
  picture is correct. `format` and `width` are valid.
* When the site is generated: every figure the document uses is rendered with PILean
  (`pilean-build`'s rendering, file names and manifest), every SVG must be inert
  (`PILean.Svg.inertProblem?`: no script, no event handler, nothing loaded from elsewhere), so
  must every picture a page puts inline; a figure shown with `inline := true` must have an inline
  picture; one figure's inline SVG, counted once over all it puts in the pages, may not pass
  `--figure-inline-limit BYTES` (2,000,000 by default; figures shown as files are not counted);
  and
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

It also has explorers, inline pictures, a figure and an explorer inside a Blueprint entry, and
captions, names and ids that a page must escape. `example/tests/` has the checks run on it:

* `check-site.sh SCRATCH`: the build, the folder check, the reproducibility of two builds,
  `--check-figures` on a damaged copy, `pilean-verify`, the figures' markup
  (`markup_check.py`), every inline picture against its file and the manifest
  (`inline_check.py`, also on a page whose picture was changed), the three link modes and their
  warnings, `figure_explorer` on a plot. It leaves four sites in SCRATCH: `a` (the default
  links), `site`, `none` and `sbs` (side by side, links into the site).
* `browser_check.py SCRATCH/a/html-multi [SHOTS] --site-links SCRATCH/site/html-multi --no-links
  SCRATCH/none/html-multi --side-by-side SCRATCH/sbs/html-multi`: the pages in a headless
  Chromium under a strict content policy: both themes, reduced motion, the source links, the
  figures page, narrow windows, the explorers' controls, gestures, announcements and touch
  targets, no script, a policy that allows the pictures' `style` elements by hash only, clicks
  on the links of each mode, centring and overflow (wide, in the side-by-side text column, at
  360 px) and hostile strings.
