/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Graph.Draw
import PILean.Graph.Pack

/-!
# A layout as SVG for a web page

`Layout.toWebSvg` writes a layout as an SVG element meant to be put into a web page and styled
and scripted there: every node is a group with an `id`, classes and a title, every edge and
cluster a group with a class, and the colours are written as plain presentation attributes,
which a page's stylesheet overrides by class (light and dark themes, states). The text is SVG
text in the page's font, so the caller sizes the nodes for it (`Graph.Node.size`, with
`sansWidth` as the measure).

The output carries no script, link, style attribute or event handler: `Svg.isInert` accepts it.
Everything the caller passes (ids, classes, titles, labels, colours) is escaped as attribute
values or text.

The structure, back to front:

* `g.graph` holds everything;
* `g.cluster`: a `path` (the box) and a `text` (the title);
* `g.edge` (with the edge's classes): a `path` (the curve) and, for a directed edge, a
  `path.head` (the arrowhead);
* `g.node` (with the node's `id` and classes): a `title` (the node's name), a `desc` (its
  tooltip, when it has one), the outline (a `path`, or an `ellipse`) and one `text` per line.

## Main definitions

* `sansWidth`: the width of a line of text in a sans-serif face of Helvetica's metrics.
* `WebShape`, `WebNode`, `WebEdge`, `WebOptions`, `Layout.toWebSvg`.
-/

namespace PILean.Graph

/-- The advance of a character in thousandths of the font size, in a sans-serif face with the
metrics of Helvetica (Arial and Liberation Sans share them); a character outside ASCII counts
as a wide letter, and one of the wide scripts as a full square. -/
def sansAdvance (c : Char) : Nat :=
  if c.val ≥ 0x2E80 then 1000
  else if c.val ≥ 0x80 then 667
  else match c with
  | ' ' | '.' | ',' | ':' | ';' | '!' | '/' | '\\' | '[' | ']' | 'f' | 't' | 'I' => 278
  | 'i' | 'j' | 'l' => 222
  | '\'' => 191 | '|' => 260 | '"' => 355
  | '-' | '(' | ')' | 'r' | '`' => 333
  | '{' | '}' => 334 | '*' => 389 | '^' => 469
  | 'c' | 'k' | 's' | 'v' | 'x' | 'y' | 'z' | 'J' => 500
  | '+' | '<' | '=' | '>' | '~' => 584
  | 'F' | 'T' | 'Z' => 611
  | 'A' | 'B' | 'E' | 'K' | 'P' | 'S' | 'V' | 'X' | 'Y' | '&' => 667
  | 'C' | 'D' | 'H' | 'N' | 'R' | 'U' | 'w' => 722
  | 'G' | 'O' | 'Q' => 778
  | 'M' | 'm' => 833 | '%' => 889 | 'W' => 944 | '@' => 1015
  | _ => 556

/-- The width of a line of text of `size` in a sans-serif face of Helvetica's metrics. -/
def sansWidth (s : String) (size : Float) : Float :=
  (s.foldl (fun n c => n + sansAdvance c) 0).toFloat * size / 1000

/-- The outline of a node on a web page. -/
inductive WebShape where
  /-- A rectangle with square corners. -/
  | box
  /-- A rectangle with rounded corners. -/
  | round
  /-- An ellipse. -/
  | ellipse
  /-- A rectangle with a small tab on its top left corner (a folder). -/
  | tab
  deriving BEq, Inhabited, Repr

/-- The page's side of a node. Colours are CSS colours, written as given. -/
structure WebNode where
  /-- The element's `id` (none when empty). -/
  id : String := ""
  /-- Classes beside `node`, separated by spaces. -/
  classes : String := ""
  /-- The node's name, the text of its `title`. -/
  name : String := ""
  /-- A tooltip, the text of its `desc` (none when empty). -/
  tooltip : String := ""
  /-- The lines of the label. -/
  lines : Array String := #[]
  /-- The outline. -/
  shape : WebShape := .round
  /-- The fill colour. -/
  fill : String := "#ffffff"
  /-- The outline colour. -/
  stroke : String := "#6b7280"
  /-- The text colour. -/
  ink : String := "#0f172a"
  /-- The outline's width. -/
  strokeWidth : Float := 1
  /-- The outline's dashes (`stroke-dasharray`; solid when empty). -/
  dash : String := ""
  deriving Inhabited

/-- The page's side of an edge. -/
structure WebEdge where
  /-- Classes beside `edge`, separated by spaces. -/
  classes : String := ""
  /-- The curve's width. -/
  width : Float := 1
  /-- The curve's dashes (`stroke-dasharray`; solid when empty). -/
  dash : String := ""
  deriving Inhabited

/-- What `Layout.toWebSvg` writes besides the layout. -/
structure WebOptions where
  /-- Classes of the `svg` element. -/
  classes : String := ""
  /-- More attributes of the `svg` element. -/
  attrs : Array (String × String) := #[]
  /-- The size of the node labels. -/
  fontSize : Float := 10
  /-- The font family. -/
  fontFamily : String := "Helvetica, Arial, sans-serif"
  /-- The colour of edges. -/
  edge : String := "#6b7280"
  /-- The colour of the clusters' boxes. -/
  cluster : String := "#cbd5e1"
  /-- The colour of the clusters' titles. -/
  label : String := "#334155"
  /-- The radius of the corners of a rounded node. -/
  radius : Float := 5
  /-- Whether the clusters' titles stand at the bottom of their boxes (a layout mirrored upside
  down has its room for them there). -/
  titlesBelow : Bool := false
  deriving Inhabited

/-- A rectangle with a tab on its top left corner. -/
def tabPath (b : Box) : Path :=
  let t := min 6 (b.height / 4)
  let w := min 22 (b.width / 3)
  let p := fun (x y : Float) => (⟨x, y⟩ : Point)
  (((((((Path.empty.moveTo (p b.x0 (b.y0 - t))).lineTo (p (b.x0 + w) (b.y0 - t))).lineTo
    (p (b.x0 + w + t) b.y0)).lineTo (p b.x1 b.y0)).lineTo (p b.x1 b.y1)).lineTo
    (p b.x0 b.y1)).close)

/-- The layout as an SVG element for a web page (see the module docstring). `nodes` gives the
page's side of every node, by number, and `edges` that of every edge, by its position in the
graph's `edges`; a node or edge without an entry gets the defaults. The element has the layout's
size and a view box from the origin. -/
def Layout.toWebSvg (l : Layout) (nodes : Array WebNode) (edges : Array WebEdge)
    (o : WebOptions := {}) : String :=
  let num := fun (x : Float) => fmtNum x 1
  let dashAttr := fun (d : String) => if d.isEmpty then #[] else #[("stroke-dasharray", d)]
  let clusterNodes := l.clusters.map fun c =>
    let b := c.box.inset 0.5 0.5 0.5 0.5
    let ty := if o.titlesBelow then c.box.y1 - 8 else c.box.y0 + 8 + o.fontSize * 0.8
    Svg.el "g" #[("class", "cluster")] #[
      Svg.el "path" #[("d", Svg.pathData (roundRectPath b 8) 1), ("fill", "none"),
        ("stroke", o.cluster), ("stroke-width", "1.2"), ("stroke-dasharray", "5 4")],
      Svg.el "text" #[("x", num (c.box.x0 + 10)), ("y", num ty), ("fill", o.label)]
        #[.text c.name]]
  let edgeNodes := l.edges.map fun e =>
    let w := edges.getD e.index {}
    let cls := if w.classes.isEmpty then "edge" else "edge " ++ w.classes
    let curve := Svg.el "path" (#[("d", Svg.pathData e.path 1), ("fill", "none"),
      ("stroke", o.edge), ("stroke-width", fmtNum w.width 2)] ++ dashAttr w.dash)
    let head := match e.head with
      | some h => #[Svg.el "path" #[("class", "head"), ("d", Svg.pathData h 1), ("fill", o.edge),
          ("stroke", "none")]]
      | none => #[]
    Svg.el "g" #[("class", cls)] (#[curve] ++ head)
  let nodeNodes := l.nodes.map fun n =>
    let w := nodes.getD n.index {}
    let half := w.strokeWidth / 2
    let b := n.box.inset half half half half
    let cx := (n.box.x0 + n.box.x1) / 2
    let cy := (n.box.y0 + n.box.y1) / 2
    let paint := #[("fill", w.fill), ("stroke", w.stroke),
      ("stroke-width", fmtNum w.strokeWidth 2)] ++ dashAttr w.dash
    let outline := match w.shape with
      | .ellipse => Svg.el "ellipse" (#[("cx", num cx), ("cy", num cy), ("rx", num (b.width / 2)),
          ("ry", num (b.height / 2))] ++ paint)
      | .box => Svg.el "path" (#[("d", Svg.pathData (Path.rect b.x0 b.y0 b.width b.height) 1)] ++
          paint)
      | .round => Svg.el "path" (#[("d", Svg.pathData (roundRectPath b o.radius) 1)] ++ paint)
      | .tab => Svg.el "path" (#[("d", Svg.pathData (tabPath b) 1)] ++ paint)
    let count := w.lines.size.toFloat
    let lineHeight := o.fontSize * 1.2
    let texts := w.lines.mapIdx fun i s =>
      let y := cy + (i.toFloat - (count - 1) / 2) * lineHeight + o.fontSize * 0.36
      Svg.el "text" #[("x", num cx), ("y", num y), ("fill", w.ink)] #[.text s]
    let cls := if w.classes.isEmpty then "node" else "node " ++ w.classes
    Svg.el "g" ((if w.id.isEmpty then #[] else #[("id", w.id)]) ++ #[("class", cls)])
      (#[Svg.el "title" #[] #[.text w.name]] ++
        (if w.tooltip.isEmpty then #[] else #[Svg.el "desc" #[] #[.text w.tooltip]]) ++
        #[outline] ++ texts)
  let root := Svg.el "svg" (#[("xmlns", "http://www.w3.org/2000/svg")] ++
    (if o.classes.isEmpty then #[] else #[("class", o.classes)]) ++
    #[("width", fmtNum l.width 0), ("height", fmtNum l.height 0),
      ("viewBox", s!"0 0 {fmtNum l.width 0} {fmtNum l.height 0}")] ++ o.attrs)
    #[Svg.el "g" #[("class", "graph"), ("font-family", o.fontFamily),
        ("font-size", fmtNum o.fontSize 2), ("text-anchor", "middle")]
      (#[Svg.el "g" #[("class", "clusters"), ("text-anchor", "start")] clusterNodes,
         Svg.el "g" #[("class", "edges")] edgeNodes,
         Svg.el "g" #[("class", "nodes")] nodeNodes])]
  Svg.render 0 root ++ "\n"

end PILean.Graph
