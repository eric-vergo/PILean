/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Graph.Layered
import PILean.Canvas

/-!
# Drawing graphs

A `Layout` drawn on the vector canvas (`PILean.Canvas`), from which the SVG and the image are
written, so that both show the same picture. The craft follows the plots: one-pixel outlines on
pixel centres (boxes are on whole pixels), text measured by the style's text engine, nothing
drawn in a series colour but the clusters (faint tints of the palette).

Back to front: clusters, edges with their heads, labels on plates of the page colour, node
boxes, node labels.

## Main definitions

* `Layout.draw`, `Graph.draw`: the drawing.
* `Graph.toSvg`, `Graph.toImage`, `Graph.toPng`: the written forms.
* `roundRectPath`, `NodeBox.draw`, `RoutedEdge.draw`, `ClusterBox.draw`: the parts.
-/

namespace PILean.Graph

open PILean Canvas

/-- A closed rectangle with rounded corners of radius `r` (cubic quarter arcs). -/
def roundRectPath (b : Box) (r : Float) : Path :=
  let r := min r (min b.width b.height / 2)
  let k := Path.kappa * r
  let p := fun (x y : Float) => (⟨x, y⟩ : Point)
  let path := (Path.empty.moveTo (p (b.x0 + r) b.y0)).lineTo (p (b.x1 - r) b.y0)
  let path := path.cubicTo (p (b.x1 - r + k) b.y0) (p b.x1 (b.y0 + r - k)) (p b.x1 (b.y0 + r))
  let path := path.lineTo (p b.x1 (b.y1 - r))
  let path := path.cubicTo (p b.x1 (b.y1 - r + k)) (p (b.x1 - r + k) b.y1) (p (b.x1 - r) b.y1)
  let path := path.lineTo (p (b.x0 + r) b.y1)
  let path := path.cubicTo (p (b.x0 + r - k) b.y1) (p b.x0 (b.y1 - r + k)) (p b.x0 (b.y1 - r))
  let path := path.lineTo (p b.x0 (b.y0 + r))
  (path.cubicTo (p b.x0 (b.y0 + r - k)) (p (b.x0 + r - k) b.y0) (p (b.x0 + r) b.y0)).close

/-- The baseline that centres a line of text of `size` vertically at `cy`. -/
def baselineAt (cy size : Float) : Float := cy + size * 0.36

/-- The shape of a node: its outline (on pixel centres) and its label. -/
def NodeBox.draw (st : Style) (n : NodeBox) : Shape :=
  let b := n.box.inset 0.5 0.5 0.5 0.5
  let outline : Path := match n.shape with
    | .box => Path.rect b.x0 b.y0 b.width b.height
    | .round => roundRectPath b st.nodeRadius
    | .ellipse =>
      Path.ellipse ⟨(b.x0 + b.x1) / 2, (b.y0 + b.y1) / 2⟩ (b.width / 2) (b.height / 2)
  let cx := (n.box.x0 + n.box.x1) / 2
  let cy := (n.box.y0 + n.box.y1) / 2
  .group #[.path outline (some (.solid n.fill)) (some { ink := n.stroke, width := 1 }),
    .text n.label ⟨cx, baselineAt cy st.nodeLabelSize⟩ st.nodeLabelSize st.inkPrimary .middle]

/-- The shape of an edge: its curve, its arrowhead and its label on a plate of the page
colour. -/
def RoutedEdge.draw (st : Style) (e : RoutedEdge) : Shape :=
  let line : Line := { ink := st.edge, width := st.edgeWidth, cap := "round", join := "round" }
  let curve := Shape.path e.path none (some line)
  let head := match e.head with
    | some h => #[Shape.path h (some (.solid st.edge)) (some { line with width := 0.5 })]
    | none => #[]
  let label := match e.label with
    | some l =>
      let cx := (l.box.x0 + l.box.x1) / 2
      let cy := (l.box.y0 + l.box.y1) / 2
      #[Shape.path (roundRectPath l.box 3) (some (.solid st.background)) none,
        .text l.text ⟨cx, baselineAt cy st.noteSize⟩ st.noteSize st.inkSecondary .middle]
    | none => #[]
  .group (#[curve] ++ head ++ label)

/-- The shape of a cluster: a faint tint of a palette colour, a hairline, the title at the top
left. -/
def ClusterBox.draw (st : Style) (c : ClusterBox) : Shape :=
  let ink := (st.seriesColor c.index).1
  let b := c.box.inset 0.5 0.5 0.5 0.5
  let outline := roundRectPath b 8
  .group #[.path outline (some (.solid ink)) none (opacity := 0.09),
    .path outline none (some { ink, width := 1 }) (opacity := 0.55),
    .text c.name ⟨c.box.x0 + 12, c.box.y0 + 12 + st.noteSize * 0.72⟩ st.noteSize
      st.inkSecondary .start 1.15]

/-- The drawing of a layout on the page colour. -/
def Layout.draw (l : Layout) (st : Style) : Shape :=
  .group (#[.path (rect 0 0 l.width l.height) (some (.solid st.background)) none] ++
    l.clusters.map (·.draw st) ++ l.edges.map (·.draw st) ++ l.nodes.map (·.draw st))

/-- The layered layout of the graph, drawn. -/
def draw (g : Graph) (o : LayeredOptions := {}) (st : Style := {}) : Shape :=
  (g.layout o st).draw st

/-- A layout as an SVG document, text as SVG text (or as shapes when `outlines`). -/
def Layout.toSvg (l : Layout) (st : Style) (outlines : Bool := false) : String :=
  (l.draw st).toSvg l.width l.height st.fontFamily (if outlines then some st.text else none)

/-- A layout as an RGBA image `scale` times its size (text as shapes from the style's text
engine). -/
def Layout.toImage (l : Layout) (st : Style) (scale : Float := 1) : Image :=
  let w := (l.width * scale).ceil.toUInt64.toNat
  let h := (l.height * scale).ceil.toUInt64.toNat
  ((Shape.group #[l.draw st] (Affine.scale scale scale)).toImage w h st.text st.background)

/-- The layered layout of the graph as an SVG document. -/
def toSvg (g : Graph) (o : LayeredOptions := {}) (st : Style := {}) (outlines : Bool := false) :
    String :=
  (g.layout o st).toSvg st outlines

/-- The layered layout of the graph as an image `scale` times its size. -/
def toImage (g : Graph) (o : LayeredOptions := {}) (st : Style := {}) (scale : Float := 1) :
    Image :=
  (g.layout o st).toImage st scale

/-- The layered layout of the graph as PNG bytes. -/
def toPng (g : Graph) (o : LayeredOptions := {}) (st : Style := {}) (scale : Float := 1) :
    Except Png.PngError ByteArray :=
  (g.toImage o st scale).writePng

end PILean.Graph
