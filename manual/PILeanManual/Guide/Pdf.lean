/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILean
import PILean.Trust.Attr
import PILeanVersoManual
import PILeanManual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open PILeanVerso.Manual
open PILeanManual

#doc (Manual) "PDF for Papers" =>
%%%
tag := "pdf"
%%%

```lean -show
namespace PILeanManual.PdfGuide
open PILean PILean.Plot
```

Every picture PILean draws can be written as a one-page vector PDF, for a paper or a slide: a
plot ({name}`PILean.Plot.Figure.toPdf`), a plane figure or a diagram
({name}`PILean.Plane.Figure.toPdf`), a graph ({name}`PILean.Graph.toPdf`), a frame of an
explorer ({name}`PILean.ExplorerFrame.toPdf`) and an animation's poster
({name}`PILean.Animation.posterPdf`). The writer ({api}`PILean.Pdf.Write`) is pure Lean, in the
core library, and needs nothing installed. A build (`pilean-build`, and the Verso adapters) writes
a figure's PDF beside its SVG and PNG, with the same source record.

```lean
/-- The squares and the cubes of the integers from -3 to 3. -/
@[figure]
def powers : Figure where
  title := "Squares and cubes"
  width := 480
  height := 300
  panels := #[{
    x := { label := "n" }, y := { label := "value" },
    series := #[.ofIntPoints "n²" ((List.range 7).map fun k =>
        let n : Int := k - 3; (n, n ^ 2)),
      .ofIntPoints "n³" ((List.range 7).map fun k => let n : Int := k - 3; (n, n ^ 3))] }]
```

```lean (name := pdfEx)
#eval powers.toPdf.size
#eval (Pdf.check powers.toPdf).map (·.pages)
#eval powers.toSvg.length
```

```leanResult pdfEx
```

# The Page
%%%
tag := "pdf-page"
%%%

The page is the picture's box: a picture of `w × h` pixels is a page of `0.75 w × 0.75 h`
points, since a CSS pixel is `1/96` inch and a point `1/72` inch ({name}`PILean.Pdf.ptPerPx`). A
figure of the default width, 640 pixels, is a page 480 points (about 17 cm) wide; LaTeX scales it
to the width it is given.

```
\usepackage{graphicx}
...
\begin{figure}
  \centering
  \includegraphics[width=0.8\linewidth]{figures/MyPaper/Figures/powers.pdf}
  \caption{Squares and cubes.}
\end{figure}
```

The text is drawn as outlines of the style's text engine (the built-in lettering, or LeAnTeX's
New Computer Modern with `pilean-leantex`), so the PDF embeds no font and shows the same letters
in every viewer. The bytes are deterministic: the same picture gives the same file on every run,
with no date in it and a document ID computed from its content.

# What Is Kept
%%%
tag := "pdf-kept"
%%%

The PDF is written from the drawing the PNG is drawn from: the SVG nodes of the picture with its
text as shapes, read as PILean's rasteriser reads them.

* *Kept:* every path, with its fill (non-zero or even-odd) and its stroke (width, caps, joins,
  miter limit, dashes); colours and their opacities; the opacity of a group, as a transparency
  group; clipping paths; linear and radial gradients, as shadings through the same sampled stops
  as the SVG; the background of the style.
* *Not kept:* text as text (it cannot be selected or searched, and a screen reader does not find
  it), the accessible names and descriptions of the elements and the links to declarations that
  an SVG carries, colour profiles (the colours are the file's sRGB values in `DeviceRGB`). A
  gradient whose stops have different opacities is drawn at their mean opacity. There are no
  fonts to embed, and so no fonts are embedded.
* Colours are mixed as a PDF viewer mixes them, in the sRGB encoding, as a browser mixes an SVG;
  a plot's PNG mixes them in linear light, so the edges of curves can differ by a level or two.

A raster {name}`PILean.Image` is written as a page of its own ({name}`PILean.Image.toPdf`): its
pixels as an image compressed with PILean's DEFLATE, its alpha as a soft mask.

# Checking a PDF
%%%
tag := "pdf-check"
%%%

{name}`PILean.Pdf.check` reads a PDF through and reports the first fault of its structure: the
cross-reference table and its offsets, every object and the lengths of its streams, the page
tree, the operators of every content stream and the resources they name. `lake test` runs it on
the PDF of every picture of the gallery and plants a fault of each kind it checks. Two checks use
software already on a Mac: `tools/pdf-compare.py` renders the gallery's PDFs with Ghostscript and
with Quick Look and compares them pixel by pixel with PILean's PNGs, and with `--qpdf` runs
`qpdf --check` on each when it is installed.

# The Source and the Theorem
%%%
tag := "pdf-trust"
%%%

A PDF carries the source record of the other formats in its document information dictionary
(one key `/PILean:module`, `/PILean:decl`, … per field, added to the finished file by an
incremental update), so `pilean-info` prints it, `pilean-verify` checks it against the manifest,
and the manifest lists the PDF with its SHA-256, fingerprint and standing. Its specification, the
bytes its fingerprint covers, is the SVG with text as shapes, as for the PNG; a figure's PNG and
PDF have one fingerprint. Nothing changes in what a picture proves: a theorem linked by
`figure_proves` is about the figure, and the PDF, the SVG and the PNG are three renderings of it,
each tested, none proved.
