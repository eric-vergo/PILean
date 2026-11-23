/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Pdf.Write
import PILean.Explorer
import PILean.Graph.Draw

/-!
# Figures as PDF

The PDF of each kind of picture, written from the nodes its PNG is drawn from (text as shapes from
the style's text engine, on the style's background), so that the SVG, the PNG and the PDF show
one drawing (`PILean.Pdf.ofSvgNodes`).

## Main definitions

* `Plot.Figure.toPdf`, `Plane.Figure.toPdf`, `ExplorerFrame.toPdf`, `Graph.Layout.toPdf`,
  `Graph.toPdf`, `Animation.posterPdf`, `Image.toPdf`.
-/

namespace PILean

open Canvas

/-- The figure as a one-page PDF (`Pdf.ofSvgNodes`): its drawing with text as shapes, on its
style's background. -/
def Plot.Figure.toPdf (fig : Plot.Figure) : ByteArray :=
  Pdf.ofSvgNodes fig.width fig.height (fig.draw.render (.shapes fig.style.text)) fig.style.background

/-- The plane figure as a one-page PDF (its `auto` labels placed, text as shapes, on the style's
background), of the size of its SVG. -/
def Plane.Figure.toPdf (fig : Plane.Figure) : ByteArray :=
  let g := fig.autoPlaced
  Pdf.ofSvgNodes g.frame.width.round g.frame.height.round (g.draw.render (.shapes fig.style.text))
    fig.style.background

/-- The frame as a one-page PDF (text as shapes, on its style's background). -/
def ExplorerFrame.toPdf (f : ExplorerFrame) : ByteArray :=
  Pdf.ofSvgNodes f.width f.height (f.drawing.render (.shapes f.style.text)) f.style.background

/-- The layout as a one-page PDF of its size (text as shapes from the style's engine, on its
background). -/
def Graph.Layout.toPdf (l : Graph.Layout) (st : Style) : ByteArray :=
  Pdf.ofSvgNodes l.width l.height ((l.draw st).render (.shapes st.text)) st.background

/-- The layered layout of the graph as a one-page PDF. -/
def Graph.toPdf (g : Graph) (o : Graph.LayeredOptions := {}) (st : Style := {}) : ByteArray :=
  (g.layout o st).toPdf st

/-- The poster frame of the animation as a one-page PDF (text as shapes, on its background). -/
def Animation.posterPdf (a : Animation) : ByteArray :=
  Pdf.ofSvgNodes a.width.toFloat a.height.toFloat ((a.frame a.poster).render (.shapes a.text))
    a.background

/-- The image as a one-page PDF (`Pdf.ofImage`); `none` for an image without pixels. -/
def Image.toPdf (im : Image) : Option ByteArray := Pdf.ofImage im

end PILean
