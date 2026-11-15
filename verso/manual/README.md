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
  PILeanVerso.Manual.withFigures (%doc MyManual) site_figures% args fun args =>
    manualMain (%doc MyManual) (options := args)
```

The directive's options: `alt` (required: the text alternative), `label`, `title`, `format` (`svg`
by default, or `png`, `apng`, `gif`), `width` (a CSS length), `backdrop` (a picture of the site,
with `{theme}` for `light` or `dark`, that the figure is drawn over: callouts over a screenshot)
and `proves` (a theorem). An empty body takes the declaration's doc string as the caption.
`withFigures`'s `declStyle` sets how the source line shows a declaration and its file (by default
the name as code and the file linked to the repository when the build names one with
`--figure-repo` and `--figure-commit`).

## What the build checks

* When the chapter is elaborated: the declaration has `@[figure]`; the text alternative is given;
  the theorem named by `proves` passes PILean's rule (`figure_proves`): it is a theorem, depends
  on no `sorry` and no axiom beyond `propext`, `Classical.choice` and `Quot.sound`, and its
  statement mentions the figure or a declaration of the figure's module that the figure uses
  directly (a theorem about a function from elsewhere is linked through one of the figure's module
  that applies it to the figure's values);
  `format`, `width` and `backdrop` are valid.
* When the manual is generated: every figure is rendered with PILean, every SVG must be inert
  (`PILean.Svg.inertProblem?`), and the figures folder the generator wrote
  (`<output>/html-multi/-verso-data/pilean-figures`) must hold exactly the files of this render.
* `--check-figures DIR` compares a folder with a fresh render without generating the manual.

Two builds of the same sources write the same bytes. Light and dark pictures are switched by the
stylesheet alone (the page's `data-theme`, or the reader's system setting), with no script.

## The example and the checks

`ManualExample` is a small manual with a plot, a graph and marks over a picture;
`lake exe pilean-verso-manual-example --output _out` generates it, and `lake test` generates it
twice and checks the pages and files (inert SVG, numbers, text alternatives, light and dark
pictures, the source line, the theorem, the backdrop, the figures page, identical bytes,
`--check-figures` on a damaged copy).
