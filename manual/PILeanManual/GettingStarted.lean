/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILean
import PILean.Trust.Attr
import PILeanVersoManual
import PILeanManual.Meta
import PILeanManual.Pictures

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open PILeanVerso.Manual
open PILeanManual

#doc (Manual) "Getting Started" =>
%%%
tag := "getting-started"
htmlSplit := .never
%%%

```lean -show
namespace PILeanManual.Start
```

PILean is a library for making pictures in Lean: colours, geometry, vector paths, a drawing
canvas, plots, graphs of nodes and edges, animations, an anti-aliased rasteriser, and writers for
SVG, PNG, animated PNG and GIF. It is written in Lean alone. `import PILean` reaches Lean's `Init`
and `Std` and nothing else, so any Lean program can use it.

Every Lean example on this page and in the guide is elaborated by the manual's build; the results
printed under an example are what the build printed, and every picture is drawn by PILean from the
declaration shown, when the manual is generated. The examples of a page are elaborated one after
the other in a namespace the page does not show, so an example can use what an earlier one
defined; the whole program at the end of this page is a file of its own that needs nothing
hidden.

# Adding PILean to a Project
%%%
tag := "install"
%%%

In the project's `lakefile.lean`, require the repository at a commit (`<commit>` is a full commit
hash; `git ls-remote https://github.com/eric-vergo/PILean refs/heads/main` prints the newest):

```
require pilean from git "https://github.com/eric-vergo/PILean" @ "<commit>"
```

or, in a `lakefile.toml`:

```
[[require]]
name = "pilean"
git = "https://github.com/eric-vergo/PILean"
rev = "<commit>"
```

The project's `lean-toolchain` must name the toolchain of the repository's own `lean-toolchain`
at that commit; when this manual was built that was {toolchain}[]. Then `import PILean` in a file
of the project. The attribute `@[figure]` and
the commands of the trust layer ({ref "trust"}[Trust and Proofs]) are in `PILean.Trust.Attr`, which
imports
`Lean`; it is imported separately, only by the code that uses them.

The optional packages of the repository each sit in a folder of their own and are required with
the folder after the commit (`/ "verso/manual"`, `/ "leantex"`, …): see {ref "packages"}[Optional
Packages].

# A First Plot
%%%
tag := "first-plot"
%%%

A plot is a value of type {name}`PILean.Plot.Figure`: a size, a title, a style and panels, each
with two axes and a list of series. This one has two series, each the graph of a function:

```lean (name := firstPlotEx)
open PILean PILean.Plot in
/-- The sine and the cosine on one period. -/
@[figure]
def trig : Figure where
  title := "Trigonometric functions"
  panels := #[{
    x := { label := "x" }, y := { label := "y" },
    series := #[.function "sin x" Float.sin (-3.14) 3.14,
      .function "cos x" Float.cos (-3.14) 3.14] }]

#eval trig.toSvg.length
#eval (trig.toSvg.splitOn "\n").take 2
```

```leanResult firstPlotEx
```

{name}`PILean.Plot.Figure.toSvg` writes the SVG document as a string; the same value written
again gives the same bytes. The manual draws the figure from the declaration:

:::figure PILeanManual.Start.trig (alt := "Two curves on one plot, the sine and the cosine of x from -3.14 to 3.14, between -1 and 1, with a legend naming them.") (label := "first-plot")
:::

The `@[figure]` line is only needed for pictures that a build collects ({ref "trust"}[Trust and
Proofs]); the
definition alone is an ordinary Lean value. A program writes the files itself:

```lean
open PILean PILean.Plot in
def writeTrig : IO Unit := do
  IO.FS.writeFile "trig.svg" trig.toSvg
  IO.FS.writeFile "trig-dark.svg" { trig with style := Style.dark }.toSvg
  match trig.toPng with
  | some png => IO.FS.writeBinFile "trig.png" png
  | none => IO.eprintln "the figure could not be drawn as PNG"
```

This plot has no theorem: {name}`PILean.Plot.Series.function` samples a floating-point function
adaptively, which is tested, not proved. The plots that come with a theorem are those of exact
functions on the rationals and of exact data ({ref "plot-exact"}[Exact Functions],
{ref "proofs"}[What a Picture Proves]).

# A First PNG
%%%
tag := "first-png"
%%%

Images are drawn pixel by pixel with {name}`PILean.Raster.Draw`, in the spirit of Pillow's
`ImageDraw`: start from a canvas of a size and a background, draw shapes with paints, and take
the {name}`PILean.Image`.

```lean (name := firstPngEx)
open PILean PILean.Raster in
def banner : Image :=
  let d := Draw.new 300 200
  let d := d.rectangle 20 20 280 60 (fill := some (.linear ⟨20, 0⟩ ⟨280, 0⟩
    #[⟨0, ⟨230, 30, 30, 255⟩⟩, ⟨1, ⟨20, 60, 220, 255⟩⟩]))
  let d := d.line #[⟨20, 100⟩, ⟨120, 160⟩, ⟨200, 90⟩] (.solid ⟨0, 0, 0, 255⟩) 6
    .round .round
  let d := d.ellipse 220 110 280 170 (fill := some (.solid ⟨0, 158, 115, 255⟩))
  d.toImage

#eval (banner.width, banner.height, banner.getpixel 150 40)
#eval match banner.writePng with
  | .ok bytes => s!"{bytes.size} bytes, starting {(bytes.extract 0 8).toList}"
  | .error e => e.toString
```

```leanResult firstPngEx
```

The first eight bytes are PNG's signature. To show the image on this page, the manual wraps it
in a small type of its own that PILean can render ({name}`PILeanManual.Picture`); a program of
your own does not need this:

```lean
/-- The image of the first PNG example. -/
@[figure]
def bannerPicture : PILeanManual.Picture := ⟨banner⟩
```

:::figure PILeanManual.Start.bannerPicture (alt := "A horizontal bar fading from red to blue, a thick black line with round ends and a corner in it, and a green ellipse, on white.") (format := "png") (width := "300px")
:::

Writing the file is one more line in a program:

```lean
def writeBanner : IO Unit := do
  match banner.writePng with
  | .ok bytes => IO.FS.writeBinFile "banner.png" bytes
  | .error e => IO.eprintln e.toString
```

# A Whole Program
%%%
tag := "first-program"
%%%

The examples above are pieces of one program. As a file of its own, `Main.lean`, with nothing
left out:

```fileText "manual/FirstProgram/Main.lean"
```

In the project's `lakefile.lean`, beside the `require` line (the toml form is below):

```
lean_exe «first-plot» where
  root := `Main
```

Then `lake exe first-plot` builds it and writes `trig.svg`, `trig-dark.svg`, `trig.png` and
`banner.png` into the folder it is run from. The manual's `lake test` runs this file (with the
toolchain that runs the test, against the library built in the same checkout) and checks that it
writes those four files. In a `lakefile.toml`, the executable is `[[lean_exe]]` with `name =
"first-plot"` and `root = "Main"`.

# Where to Go Next
%%%
tag := "next"
%%%

* The {ref "guide"}[guide] takes the library part by part: colours and styles, the canvas and
  paths, every kind of plot, graphs, animations, raster images and the readers, text.
* {ref "trust"}[Trust and Proofs] says what a picture's source record, fingerprint and manifest
  establish, what
  the theorems about pictures say, and where floating point begins.
* The {ref "api"}[API reference] lists every public declaration of the library with its
  docstring.
