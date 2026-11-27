# PILean figures in Verso documents

`pilean-verso` puts PILean figures into Verso Manual-genre documents, in particular
[Verso Blueprint](https://github.com/leanprover/verso-blueprint) sites. A figure is the value of a
Lean declaration marked `@[figure]`; the site's build draws it, writes the files with their source
record and fingerprint and a manifest, and the page shows the picture with a caption that leads
back to the declaration and to a theorem about it.

PILean itself has no dependencies. This package, in its own folder, adds Verso and Verso
Blueprint (pinned in `lakefile.lean`) and depends on PILean through the parent folder. A
warning in this package's own modules (and in `manual/`'s) fails `lake build`
(`warningAsError`); `lake build --wfail` fails as well on the deprecation warnings of the pinned
Verso Blueprint, which are not PILean's. A plain
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

figure_links divisorGraph divisorGraph_spec
```

`figure_links` links the theorem to the figure (PILean's `docs/TRUST.md`, "Standing"); a caption
that names a theorem with `links :=` (or `proves :=`, the same option) needs that link, or the
site's build fails.

In a Blueprint chapter (after `import PILeanVerso` and `open PILeanVerso`):

```
:::figure MyProject.divisorGraph (label := "divisors") (links := MyProject.divisorGraph_spec)
The divisors of 24; an edge joins $`a` to $`b` when $`b` covers $`a`.
:::

As {figref "divisors"}[] shows, ...
```

and, in the document's root, `{figure_list}` for a page that lists every figure. The generator
wraps the one it has:

```lean
def main (args : List String) : IO UInt32 :=
  PILeanVerso.withFigures (%doc MyProject.Blueprint) site_figures% args fun doc args =>
    Informal.PreviewManifest.blueprintMainWithPreviewData doc args
      (extensionImpls := by exact extension_impls%)
```

The generator is given the document with the figures' pages added (`doc`); it must render that
document, not its own `%doc`.

The directive's options: `label`, `alt` (the text alternative; the declaration's doc string by
default), `title`, `format` (`svg` by default, or `png`, `apng`, `gif`), `width` (a CSS length),
`inline := true` (the picture as an `svg` element of the page, see below) and `links` (a linked
theorem; `proves` is the same option). An empty body takes the declaration's doc string as the caption.

An explorer (a declaration of type `PILean.Explorer`, made with `Plane.slider`, `Plane.stepper`
or `Explorer.grid`) has its own directive, with the same options:

```
:::figure_explorer MyProject.radiusExplorer (label := "radius") (alt := "A disk whose radius grows from 0.6 to 1.")
The disk as its radius grows.
:::
```

A motion of plane figures (a declaration of type `PILean.Plane.Motion` or
`PILean.Plane.MotionPanels`, marked `@[figure illustration]` or linked to a theorem by
`figure_links`) is shown with `:::figure` as any figure, and always inline:

```
:::figure MyProject.quarterTurn (label := "quarter") (alt := "A point P turns a quarter about the origin O.")
A point turned a quarter about the origin.
:::
```

The motion's own captions (`Motion.captions`, one per key) are the captions of its stills
("Step 2 of 3: …", counting the stills: a key that is not a still, `MotionKey.still := false`,
has none, and its caption may be empty); write them without a counter. Give the motion an `alt` (the doc string, without
its code marks, stands in otherwise). `width` sets the picture's width; `inline` is implied;
`format` does not apply. The caption ends with a note on what pointing and clicking do
(`PILeanVerso.motionHintText`) and the Blueprint's link to its motion switch, "Animations can be
turned off in the page menu.", shown only when scripts run. A motion that was
not checked strictly (built at the check level `warn` or `ignore`, or with errors left) fails the
build; `--figure-allow-unchecked` builds it, for drafts only, and its page then says what its
checks found.

A figure's files are named after its declaration, every character other than an ASCII letter,
a digit, `.`, `_` and `-` written as `_`: declarations that differ only there, such as `wordLoop₁`
and `wordLoop₂`, would share their files, and the build stops with `two outputs have the path …`.
Name such figures with ASCII digits (`wordLoop1`), or give them names that differ in those
characters.

## Links to Lean

One option of the site decides where a declaration's name leads, in the source line, on the
figures page and on each element of an inline picture that names a declaration (`.declRef`,
`data-lean-decl`): `--figure-lean-links MODE` on the generator's command line, or
`options := { leanLinks := .site }` given to `withFigures` (`PILeanVerso.LeanLinks`).

* `ideil` (the default): `lean:decl/<Name>` links, for an editor that shows the site beside the
  code. In the source line they are shown only when the page's root has `data-lean-links`
  (plain names otherwise); in an inline picture each such element is a link, which does nothing
  in an ordinary browser but is still a tab stop: a site published for browsers should use
  `site` or `none`.
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
* A motion moves inline, in the theme of the page, on its own clock, its caption saying
  "Animation; a still replaces it while you point at it or focus it, or after a click or tap until
  you click elsewhere." Hovering it (with a mouse) or focusing it (with the keyboard, a click or a
  tap, until the focus leaves) covers it with its poster key's still in the same place; the clock
  runs on under the still, so the picture is further on in its cycle when the still goes. With
  animations turned off (the Blueprint's switch beside the theme control), with the system's
  reduced motion, and in print, it shows its key frames as stills in a grid with their captions,
  which assistive technology reads after the picture's text alternative; the grid has as many
  columns as fit with every still at three quarters of its own width or more (one column for a
  wide picture, several for a small one), or a still as wide as the column, and never larger than
  its own width. A still keeps its box while it loads, at every width: its picture's `source` for
  small screens carries the narrow file's own `width` and `height`. The poster is the still shown
  under the pointer and the focus because no style rule can pause the picture's clock or know
  where it is ([`docs/DESIGN.md`](../docs/DESIGN.md), "Why the poster under hover and focus"). On small screens it shows its narrow rendition, when it has one. None of this
  needs a script ([`docs/DESIGN.md`](../docs/DESIGN.md), "A motion shown in a page").
* With `inline := true`, the picture is an `svg` element of the page (its narrow rendition on
  screens up to 560 px wide, when it has one): the titles of its elements show on hover, the
  elements that name a declaration link to it (see "Links to Lean"), and one picture serves both
  themes through a `style` element inside it. No script is needed for an inline picture.
* Content policy: the figures' stylesheets are `<style>` elements in the page's head (as Verso
  writes the CSS of its extensions), and each inline picture has its own `style` element; a
  policy must allow all of them, with `style-src 'unsafe-inline'` or the hash of each `<style>`
  element of the page (the example's browser check serves the pages so). A `width :=` is a
  `style` attribute (`style-src-attr`); Verso's own math markup has some too. A motion's grid of
  stills needs none: its widths are classes defined by a `style` element beside it. Scripts come
  from the site's files only.
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
  frame shown first with script outlined; nothing in it is focusable but the links of its
  pictures, in the link modes that have them. The play button is a toggle (`aria-pressed`); keys
  with Ctrl, ⌘ or Alt held are left to the browser.
* "Figure 1.2" and the caption, numbered as the Blueprint numbers its blocks
  (`verso.blueprint.numbering`, `verso.blueprint.subNumberingPrefix`), with a counter of its own.
* A source line: the declaration that made the picture and its file and line; the fingerprint
  (shortened, whole on hover and when copied); the theorem, if named. When the site is built with
  a repository (`--figure-repo URL`, and the commit from `--figure-commit` or `git rev-parse HEAD`)
  the file and line link to the repository at that commit. A viewer that sets `data-lean-links` on
  the page's root element (an editor showing the site next to the code) gets `lean:decl/<Name>`
  links instead of plain names, as Verso Blueprint's own Lean anchors.
* The figures page: every figure with a small picture, its source, fingerprint, files, standing
  and page, and a link to the manifest.
* A page for every figure (see "Figure pages").

## Figure pages

Each figure the document uses has a page of its own below the figures page (a part the wrapper adds;
a document without `{figure_list}` gets a "Figures" part at its end), at `Figures/<name>/`, where
`<name>` is the declaration's name when it has only `[A-Za-z0-9._-]`, and otherwise the name with
every other character replaced by `_`, cut to 100 characters and followed by `-` and the first 12
digits of the name's SHA-256. The source line under the figure ("Page": "code, standing and
provenance") and its entry on the figures page link to it, at the anchor Verso gives the page's
block (`figure-page-<name>`, made unique). The anchor is an empty element, the first child of the
page's own element: `<span class="pilean-figure-page-anchor" aria-hidden="true"
id="figure-page-…">`. Its stylesheet takes it out of the flow (absolutely positioned at the place it
would have) with no size, so it adds no space, and keeps a site's highlight of a link's target (a
background, a shadow, an outline, an animation) off it, and its `scroll-margin-top` of 12rem keeps
the page's title in view when the browser scrolls to it (Verso Blueprint's own script centres the
target, which on a figure's page leaves the title in view as well). The page's own element
(`div.pilean-figure-page`) and its sections have the ids `pilean-page-<name>`,
`pilean-page-<name>-standing`, `-code`, `-provenance` and `-reproduce`. From top to bottom:

1. The picture at full size: the light and the dark files, following the page's theme; an
   animation's still frame for readers who ask for reduced motion; an explorer embedded as it is
   where it is used. Then every file of the figure, to download, with its size in bytes.
2. Its number, its caption, and a link to every place the document shows it.
3. **Standing**, as `site_figures%` derived it with PILean's `figureStanding`, which checks each
   `figure_links` link again by its rule in the generator's environment: "Linked theorem: T",
   with each theorem's statement as Lean (from its source, highlighted; Lean's printing of it
   when the source is not available), the axioms it rests on, the sentence of `docs/TRUST.md` on
   what PILean checked of T and what it did not, and two sentences on what a linked theorem does
   and does not cover; or "Illustration: no theorem is linked to it", with whether the
   declaration marks it as one
   (`@[figure illustration]`).
4. **Code**, after everything about the picture (for a motion, after its animation's section):
   the figure's declaration in full; then the declarations of the project that its value
   and its theorems' statements use, and those that these use, to depth 2, nearest first, at
   most 16 in full (each at most 200 lines) and up to 200 more by name; a declaration is of the
   project when its module's first component is the figure module's, a theorem is followed by
   its statement and not its proof, and constructors, recursors and projections count as their
   type. Declarations of other packages that the value or a statement names directly are listed
   by name (at most 60; instances and Lean's `Init` left out), linked to the Lean and Mathlib
   documentation for `Init`, `Std`, `Lean`, `Lake`, `Mathlib` and `Batteries`. Each declaration is
   highlighted with the hovers of the genre's Lean code and linked to its source at the build's
   commit (`--figure-repo`, `--figure-commit`, `--figure-source-prefix`), over its lines. Code of
   more than 60 lines in all (the declarations' source lines) is folded in a closed `details`
   element, `details.pilean-page-code-fold`, whose summary ("Show the code: N declarations, L
   lines") opens it.
5. **Provenance**: for each file its fingerprint, SHA-256, renderer and text engine, and what
   `pilean-verify` says of it against the site's manifest, with the standing the file records;
   the Lean version, PILean's version, the revisions of `pilean` and `leantex` in the
   workspace's `lake-manifest.json`, the commit, and the continuous-integration run that built
   the site (in GitHub Actions, from `GITHUB_SERVER_URL`, `GITHUB_REPOSITORY` and
   `GITHUB_RUN_ID`, when all three are well formed, as Verso Blueprint's Comparator pages find
   it).
6. **How to reproduce**: the commands that build the site again from the commit, check the
   figures folder against its manifest with `pilean-verify`, and check that it holds exactly what
   the build draws now (`--check-figures`).

The code is read from SubVerso's `highlighted` module facet: the wrapper runs one `lake build
+M:highlighted …` for the modules the pages show, with the `lake` in the variable `LAKE` (which
`lake exe` sets), and reads `.lake/build/highlighted/<Module>.json` (a regular file of at most
64 MiB, for module names whose components are plain). Without `LAKE`, with
`--figure-code signatures`, or when that build fails, the pages show each declaration's signature
as Lean prints it and say so, and the build prints a warning.

Everything a page shows of the project (names, captions, code, paths) is text that the HTML
writer escapes; the pictures are the site's inert files. A page adds no script: an explorer uses
the script it uses where it is shown, and the code the hovers of the genre's Lean code.

## What the build checks

* When the chapter is elaborated: the declaration has `@[figure]`, and for `figure_explorer` it is
  a `PILean.Explorer` (otherwise an error says its type and to use `figure`); the theorem named
  by `links`
  exists, is a theorem, depends on no `sorry` and no axiom beyond `propext`, `Classical.choice` and
  `Quot.sound`, and its statement names the figure itself (PILean's rule, `figure_links`: the
  figure's constant occurs in the statement once its `let`s and beta-redexes are reduced; a
  statement about a definition the figure is built from is refused). The rule is about names:
  the link under the caption is a pointer to a statement to read, not a certificate that the
  picture is correct. `format` and `width` are valid.
* When the site is generated: every figure the document uses is rendered with PILean
  (`pilean-build`'s rendering, file names and manifest), every SVG must be inert
  (`PILean.Svg.inertProblem?`: no script, no event handler, nothing loaded from elsewhere), so
  must every picture a page puts inline; a figure shown with `inline := true` must have an inline
  picture; one figure's inline SVG, counted once over all it puts in the pages, may not pass
  `--figure-inline-limit BYTES` (2,000,000 by default; figures shown as files are not counted;
  a motion's moving picture and its narrow rendition are counted); a motion must have been
  checked strictly, unless `--figure-allow-unchecked` is given (for drafts); and
  after the generator has written the site, the figures folder
  (`<output>/html-multi/-verso-data/pilean-figures`) must hold exactly the files of this render: a
  missing or different file fails the build, a file left from an earlier build is reported
  (`--strict-figures` fails on it too).
* When the site is generated: a caption that names a theorem (`links :=`) the figure's standing
  does not record fails the build, as does a table whose page data does not hold exactly the
  standing's theorems. After the site is written, each figure must have its page, the page's
  file must carry its standing, and what the page states (the standing, the files with their
  sizes and SHA-256, every `pilean-verify` verdict `ok`) must agree with the fresh render, with
  the written manifest and with `pilean-verify` run on the written folder; otherwise the build
  fails.
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

`example/` is a small Blueprint with a function plot, a data plot, a graph of a relation, an
animation, a Hasse diagram and a commutative square, each with a linked theorem, and an
illustration (the library `PictureExample`, the chapters `ExampleBlueprint.Pictures` and
`ExampleBlueprint.Diagrams`):

```
cd example
lake build example-blueprint
lake exe example-blueprint --output _out/site
```

It also has explorers, inline pictures, a figure and an explorer inside a Blueprint entry, and
captions, names and ids that a page must escape (among them a figure whose declaration's name and
caption hold markup, and a motion whose title, captions, labels, panel titles and actor ids do),
and motions of plane figures on the pages "Motion" and "Escaping". `example/tests/` has the checks
run on it; those that are not about this example are PILean's site checks (below), which it runs
as one consumer:

* `check-site.sh SCRATCH`: the build, the expectations of both examples' motions written into
  `SCRATCH/motions` (`example-test --motion-out`, `pilean-verso-manual-test --motion-out`), the
  folder check, the reproducibility of two builds,
  `--check-figures` on a damaged copy, `pilean-verify`, the figures' markup (`markup_check.py`),
  every inline picture against its file and the manifest (`inline_check.py`, also on a page whose
  picture was changed), the three link modes and their warnings, `figure_explorer` on a plot; every
  figure's page against the manifest (`page_check.py`, also on pages whose standing, words or
  verdicts were changed), the page's theorem statement, code, source links and commands, the escaped
  page of the markup name; and a figure whose `figure_links` line is taken out: with the caption
  still naming the theorem the build fails, without it the page says it is an illustration; and a
  weakened theorem that no longer names the figure, which `figure_links` refuses. It leaves five
  sites in SCRATCH: `a` (the default links), `site`, `none`, `sbs` (side by side, links into the
  site) and `manual` (the Manual adapter's example, `pilean-verso-manual-example`). In each, every
  link PILean writes (a class that starts with `pilean-`) must reach its file and the element its
  fragment names (`pilean-site-links`, below), and in `a`, `sbs` and `manual` every link of the
  site; a page whose anchor was taken away must be reported; and a figure's page link must name the
  empty anchor at the start of the page. Each site check is also shown to fail on a page or a
  folder damaged where it looks (a motion's picture, poster, still, stills, style, poster group,
  record, step table, words, an added event, link or unescaped string).
* `python3 -I tests/browser_check.py SCRATCH/a/html-multi [SHOTS] --site-links
  SCRATCH/site/html-multi --no-links SCRATCH/none/html-multi --side-by-side SCRATCH/sbs/html-multi
  --manual SCRATCH/manual/html-multi --motions SCRATCH/motions`:
  the pages in a headless Chromium under a strict content policy: both themes, reduced motion, the
  source links, the figures page, narrow windows, the explorers' controls, gestures, announcements
  and touch targets, no script, a policy that allows the pictures' `style` elements by hash only,
  clicks on the links of each mode and on the links to a figure's page (in both themes: they must
  land on the anchor at the start of the page, of no size, with the page's title in view and the
  page's look unchanged, nothing highlighted), the anchor adding no space above a figure page's
  picture (at 1440 and 390 px, in both adapters' examples: the picture's place is the same with the
  anchor removed), centring and overflow (wide, in the side-by-side text column, at 360 px) and
  hostile strings; and, on every page of both examples that shows a motion, the motion checks of
  `tools/site/motion_browser.py` with the expectations in `SCRATCH/motions` (a motion without its
  expectations fails).

## Site checks

`tools/site/` (in the repository's root) holds the checks any site built with these adapters can
run on its published folder (the generator's `html-multi`); the example runs them as one site of
many. They read the site and its figures folder (`-verso-data/pilean-figures` with its
`manifest.json`, or `--figures DIR`), need Python 3 and, for the browser checks, the `playwright`
package with a Chromium it can find (nothing is installed or downloaded):

```
python3 -I tools/site/inline_check.py SITE      # each inline picture and moving picture is its file
python3 -I tools/site/markup_check.py SITE      # no script, handler or active markup in a figure
python3 -I tools/site/page_check.py SITE        # each figure's page agrees with the manifest
lake exe pilean-site-links SITE [--all]         # (verso/manual) every link reaches its target
python3 -I tools/site/motion_browser.py SITE --expect DIR [--shots DIR] [--workers N] \
    [--engine chromium|firefox]                                           # motions in a browser
```

`motion_browser.py` checks every page with a motion; DIR holds, for each motion the site shows,
`<decl>.json` (and `<decl>-narrow.json` for a narrow rendition) with the animated SVG, the keys'
stills and the poster's PNG beside it, as PILean's tests write them
(`PILeanTest.MotionChecks.expectations` for a `Plane.Motion`,
`PILeanTest.MotionPanelsChecks.expectations` for a `Plane.MotionPanels`; `example/ExampleTest.lean`,
`writeMotion` and `writePanels`, is a writer to copy): a site needs only its own writer. A motion
shown without expectations fails. The expectations list, besides the rests (with their start and
end) and the turns, the slides with three samples each, which the checks hold to the straight
segment between the actor's keys; a motion with no turn or no slide is checked for what it has;
and the opacity of every appearance and disappearance before, in and after its window (in a rest,
or in part of its step), so that a mark that never fades in fails. The rests' `from` and `until`
are the part of each rest in which its key is shown still (after the rest's fades), and each rest
says whether its key is a still (only stills have files). A
site's writer that calls the library's `expectations` gets them by rebuilding. `--workers N` checks
N pages at a time, each in a process with its own browser; a motion shown without its stills on
its figure's page and with them on another page gets on the figure's page the checks that differ
there (the ways of turning motion off, print, positions, the grids) and hover and keyboard focus
once more, while a click, a tap, a PDF print and the stills in both themes, which use the same
stage and rules, are checked where the stills are listed. Each section prints its duration
(`time: …`). Expectations of an older format, or listing other turns or slides than the motion
declares, fail with a message that says so. `tools/motion-browser-check.py` checks the same files
on their own, pixel by pixel against the stills.

Engines. The motion checks have been run in three engines; a continuous-integration gate runs
them in Chromium, and Firefox and WebKit are run locally:

* Chromium (the default): `motion_browser.py`, `motion-browser-check.py` and `browser_check.py`.
* Firefox, with Playwright's Firefox installed for Playwright (`python -m playwright install
  firefox`): `motion_browser.py SITE --expect DIR --engine firefox` and `motion-browser-check.py DIR
  --engine firefox`. Every check runs as in Chromium but two, which are reported as not applicable
  (`n/a:`): the freeze control, whose freeze is Chromium's (Firefox shows the fixture following its
  clock after `display: none`), and the PDF print, which Playwright makes in Chromium only; the
  check that every picture follows its clock after every hide runs in every engine. The pixel rule's
  tolerances were measured in Firefox too. `browser_check.py` is Chromium only: some of its sections
  drive Chromium's DevTools protocol (event listeners, touch and scroll gestures).
* WebKit, the engine of Safari, on macOS only: `python3 tools/webkit/webkit_check.py DIR` (or
  `motion-browser-check.py DIR --engine webkit`) on the files of the expectations: the positions
  at rests, turns, slides and the panels' phase, paused in the first and the second loop and
  free-running over both, failing when the clock does not run. It compiles a small runner with
  the system's `swiftc`, which loads files below DIR only, reaches no network and has no bridge
  from the page, and shows the page in a transparent window that lets every click through and
  never takes the focus (`tools/webkit/runner.swift` says exactly what it does to the desktop;
  `tools/webkit/runner_test.py` shows its limits hold); it needs a logged-in session and is no
  part of a Linux gate. The pages of a site are not checked in WebKit, only the motions' files.

A motion with no anchored actor (a morph alone) has no position to read: `webkit_check.py`
reports it as "positions not checked" (its clock is still checked), and the site check's
free-running reading says the same; `motion-browser-check.py` gives it its real check, its
pixels against its stills at every rest and a switch probe decided by its drawings.

A site with motions under its own Content-Security-Policy must allow the `style` element of every
inline picture, a motion's moving picture included (`style-src 'unsafe-inline'`, or the hash of
each), and, on a Blueprint site, the motion switch's inline head script by its hash. A site's own
stylesheet must not reach into the pictures: a rule on `.pilean-inline-svg` or its descendants
(`.pilean-inline-svg path`, `svg *`) also matches a motion's moving picture, and must not set
`display`, `visibility`, `opacity`, `transform` or `animation` there. Nor should it repaint `fill`
or `stroke` inside a picture: the live motion would then differ from its stills, which are image
files that no page rule reaches.
