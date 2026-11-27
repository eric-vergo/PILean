# PILean figures in Verso manuals

`pilean-verso-manual` puts PILean figures into documents of Verso's Manual genre. A figure is the
value of a Lean declaration marked `@[figure]`; the manual's build draws it, writes the files with
their source record and fingerprint and a manifest, and the page shows the picture, light or dark
with the page's theme, with a numbered caption that leads back to the declaration and to a
theorem about it. It needs Verso only; the Verso Blueprint adapter (`pilean-verso`, the parent
folder) builds on it.

## Use

In the manual's `lakefile.lean`:

```lean
require «pilean-verso-manual» from git "https://github.com/eric-vergo/PILean" @ "<commit>" / "verso/manual"
```

In a chapter (after `import PILeanVersoManual` and `open PILeanVerso.Manual`):

```
:::figure MyManual.Figures.layers (alt := "The layers of the code and the imports between them, ...") (label := "layers")
The layers of the code.
:::

As {figref "layers"}[] shows, ...
```

and `{figure_list}` in the document's root for a page that lists every figure. The generator wraps
`manualMain`:

```lean
def main (args : List String) : IO UInt32 :=
  PILeanVerso.Manual.withFigures (%doc MyManual) site_figures% args fun doc args =>
    manualMain doc (options := args)
```

The generator is given the document with the figures' pages added (`doc`) and must render it.

The directive's options: `alt` (required: the text alternative), `label`, `title`, `format` (`svg`
by default, or `png`, `apng`, `gif`), `width` (a CSS length), `backdrop` (a picture of the site,
with `{theme}` for `light` or `dark`, that the figure is drawn over: callouts over a screenshot)
`inline := true` (the picture as an `svg` element of the page, one picture for both themes) and
`links` (a theorem, which a `figure_links` command must link to the figure; `proves` is the same
option). An empty body takes the declaration's doc string as the caption.
`:::figure_explorer` shows a `PILean.Explorer` with its frames inline and its controls (the
same options; on another type it is an error). `withFigures`'s `declStyle` sets how the source
line shows a declaration and its file (by default the name as code and the file linked to the
repository when the build names one with `--figure-repo` and `--figure-commit`).

Where a declaration's name links is the site's link mode, `--figure-lean-links ideil|site|none`
or `options := { leanLinks := … }` (`PILeanVerso.LeanLinks`): `none` by default in this genre
(names are text, elements of a picture keep their hover text); `site` links to the declaration's
documentation in the manual (`{docstring}`) or to the figure it draws, and the build warns about
each declaration it has no place for; `ideil` writes `lean:decl/<Name>` links for an editor.
Inline pictures, explorers, motions, gestures, announcements, the behaviour without script and
the content policy they need are as described in the [Verso Blueprint adapter's
README](../README.md#what-a-reader-sees). A motion (`PILean.Plane.Motion`,
`PILean.Plane.MotionPanels`) is shown with `:::figure` and the same options, always inline, its
own captions under its stills; it follows the page's `data-motion="reduce"` and the reader's
reduced-motion setting by the stylesheet alone, so it works on a manual without the Blueprint's
switch (its caption ends with the note that a still replaces it while you point at it, or after
a click or tap until you click elsewhere; this genre adds no link to a switch). A motion not
checked strictly fails the build unless `--figure-allow-unchecked` is given (for drafts).

## Figure pages

Every figure the manual uses has a page of its own below the figures page (or below a part "Figures"
added at the end of a manual without `{figure_list}`): the picture at full size and its files, its
number, caption and uses, its standing ("Linked theorem: T" with T's statement, axioms and what
PILean checked of it, or "Illustration: no theorem is linked to it"), its code (the declaration and
the definitions of the manual's project it uses, highlighted with hovers and linked to their
source), its provenance and how to reproduce it. The source line under the figure and the figures
page link to it, at an empty anchor at the start of the page. What each section holds, the caps, how
the standing is derived and checked and where the code comes from are in the [Verso Blueprint
adapter's README](../README.md#figure-pages); the two adapters share the pages
(`PILeanVersoManual.Page`, `PILeanVersoManual.Wrapper`). `--figure-code signatures` shows signatures
instead of highlighted source and runs no `lake build`.

## What the build checks

* When the chapter is elaborated: the declaration has `@[figure]` (and is a `PILean.Explorer` for
  `figure_explorer`); the text alternative is given;
  the theorem named by `links` passes PILean's rule (`figure_links`): it is a theorem, depends
  on no `sorry` and no axiom beyond `propext`, `Classical.choice` and `Quot.sound`, and its
  statement names the figure itself: the figure's constant occurs in the statement once its
  `let`s and beta-redexes are reduced, and a statement about a definition the figure is built
  from is refused (a theorem about a function from elsewhere is linked through one that says
  what the figure holds and applies it to those values). The rule is about names: the link is a
  pointer to a statement to read, not a certificate that the picture is correct;
  `format`, `width` and `backdrop` are valid.
* When the manual is generated: every figure is rendered with PILean, every SVG and every picture
  a page puts inline must be inert (`PILean.Svg.inertProblem?`), a figure shown inline must have
  an inline picture, one figure's inline SVG may not pass `--figure-inline-limit`, and the
  figures folder the generator wrote
  (`<output>/html-multi/-verso-data/pilean-figures`) must hold exactly the files of this render.
  A caption that names a theorem the figure's standing does not record fails the build; so does
  a figure's page whose standing, files or `pilean-verify` verdicts differ from the render, the
  written manifest or `pilean-verify` run on the written folder.
* `--check-figures DIR` compares a folder with a fresh render without generating the manual.
* `lake exe pilean-site-links SITE [--all]` (`PILeanVerso.siteLinkProblems`) checks a built site
  (the `html-multi` folder): every link PILean writes (a class that starts with `pilean-`), or
  with `--all` every link of the site, must reach its file (a folder stands for its
  `index.html`) and the element its fragment names, resolved against the page and its
  `<base>` as a browser resolves it. It prints each link that does not and exits with status 1.

Two builds of the same sources write the same bytes. Light and dark files are switched by the
stylesheet alone (the page's `data-theme`, or the reader's system setting), with no script; an
inline picture is restyled by its own `style` element under the same rules.

## The example and the checks

`ManualExample` is a small manual with a plot, a graph, marks over a picture, two explorers, an
inline figure, the documentation of a declaration a picture links to, and three pictures that claim
false things linked to theorems that say nothing of them (their pages say only what PILean checked);
`lake exe pilean-verso-manual-example --output _out` generates it, and `lake test` generates it and
checks the pages and files (inert SVG, numbers, text alternatives, light and dark pictures, the
source line, the theorem, the backdrop, the figures page, the explorers' markup, the inline
pictures' theme rules and files, the link modes, identical bytes, `--check-figures` on a damaged
copy), the figures' standing and page data from `site_figures%` (also for a figure whose theorem is
not linked), the refusal of a caption naming an unlinked theorem, the pages' sentences against
`docs/TRUST.md`, the pages' addresses, every link PILean writes reaching its file and element (in
the default mode and with links into the site; the check itself on a planted site), a page link
landing on the empty anchor at the start of the page, and the pages themselves: the theorem with its
statement and axioms, the code, the files and verdicts, the commands, an illustration's words, no
script.
