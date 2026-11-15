/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILeanTest.GraphQuality

/-!
# Checks of the DOT reader and writer

The reader on the statements it supports (defaults, chains of edges, nested clusters, quoted IDs,
comments), the graph it builds, the writer's laid out DOT read back by the reader (every node's
position at its box's centre, every edge with its control points, every cluster's box), and the
reader refusing hostile and malformed inputs with an error rather than a partial graph.
-/

namespace PILeanTest.GraphDot

open PILean PILean.Graph

/-- A DOT graph with most of what the reader supports. -/
def sample : String := "/* a comment */
strict digraph \"deps\" {
  graph [rankdir=TB]; nodesep=0.4
  node [shape=box, style=\"rounded,filled\", fillcolor=\"#eef2ff\"];
  edge [color=gray]
  // nodes
  a [label=\"Alpha \\\"one\\\"\"]; b; c [shape=ellipse, color=\"#336699\"]
  subgraph cluster_one {
    label=\"Part one\"
    d -> e
    subgraph cluster_inner { graph [label=Inner]; f }
  }
  subgraph plain { g }
# a line comment
  a -> b -> c [label=uses]
  c -> d; e -> f; f -> g; a -> g
  h [label=\"\\N\"]
}
"

/-- The checks of the reader on `sample`. -/
def readChecks : Array (String × Bool) :=
  match Dot.parse sample with
  | .error e => #[(s!"dot: the sample is read ({e})", false)]
  | .ok d =>
    let g := d.toGraph
    let idx := fun (s : String) => d.nodes.idxOf s
    #[("dot: the sample's header", d.directed && d.strict && d.name == "deps"),
      ("dot: nodes in order of first mention",
        d.nodes == #["a", "b", "c", "d", "e", "f", "g", "h"]),
      ("dot: a chain of edges is one edge per step, with the defaults",
        d.edges.size == 7 && (d.edges.getD 2 (0, 0, #[])).2.2.get? "label" == some "uses" &&
        (d.edges.getD 0 (0, 0, #[])).2.2.get? "color" == some "gray"),
      ("dot: a quoted label with escaped quotes",
        (g.nodes.getD 0 default).label == "Alpha \"one\""),
      ("dot: \\N is the node's name", (g.nodes.getD 7 default).label == "h"),
      ("dot: shapes and colours", (g.nodes.getD 0 default).style.shape == some .round &&
        (g.nodes.getD 2 default).style.shape == some .ellipse &&
        (g.nodes.getD 2 default).style.stroke == Rgba.ofHex? "#336699" &&
        (g.nodes.getD 1 default).style.fill == Rgba.ofHex? "#eef2ff"),
      ("dot: clusters nest, a plain subgraph is no cluster", g.clusters.size == 2 &&
        (g.clusters.getD 1 default).parent == some 0 &&
        (g.clusters.getD 0 default).name == "Part one"
        && (g.clusters.getD 1 default).name == "Inner"),
      ("dot: a node belongs to the cluster it was first named in",
        (g.clusters.getD 0 default).members == #[idx "d", idx "e"] &&
        (g.clusters.getD 1 default).members == #[idx "f"]),
      ("dot: graph attributes", d.attrs.get? "nodesep" == some "0.4")]

/-- A decimal number `[-]d[.ddd]`. -/
def decimal? (s : String) : Option Float :=
  let t := s.trimAscii.toString
  let neg := t.startsWith "-"
  let t := if neg then (t.drop 1).toString else t
  let sign : Float := if neg then -1 else 1
  match t.splitOn "." with
  | [w] => w.toNat?.map fun n => sign * n.toFloat
  | [w, f] => do
    let wn ← (if w.isEmpty then some 0 else w.toNat?)
    let fn ← f.toNat?
    return sign * (wn.toFloat + fn.toFloat / (10 : Float) ^ f.length.toFloat)
  | _ => none

/-- Reads the numbers of a `x,y` text. -/
def pair? (s : String) : Option (Float × Float) :=
  match s.splitOn "," with
  | [a, b] => do return (← decimal? a, ← decimal? b)
  | _ => none

/-- The checks of the writer: the laid out sample read back. -/
def writeChecks : Array (String × Bool) :=
  match layoutDot sample with
  | .error e => #[(s!"dot: the sample is laid out ({e})", false)]
  | .ok out =>
    match Dot.parse out, Dot.parse sample with
    | .ok d2, .ok d =>
      let l := d.toGraph.layout d.options
      let back := fun (i : Nat) => d2.nodeAttrs.getD (d2.nodes.idxOf (d.nodes.getD i "")) #[]
      let centreOk := (Array.range d.nodes.size).all fun i =>
        match (back i).get? "pos" >>= pair?, l.nodes[i]? with
        | some (x, y), some nb =>
          ((nb.box.x0 + nb.box.x1) / 2 - x).abs < 0.01 &&
            ((l.height - (nb.box.y0 + nb.box.y1) / 2) - y).abs < 0.01
        | _, _ => false
      #[("dot: the laid out graph reads back with the same nodes and edges",
          d2.nodes.qsort (· < ·) == d.nodes.qsort (· < ·) && d2.edges.size == d.edges.size &&
            d2.clusters.size == 2 && (back 7).get? "label" == some "\\N"),
        ("dot: every node's pos is its box's centre, origin at the bottom", centreOk),
        ("dot: the graph's bounding box", d2.attrs.get? "bb" ==
          some s!"0,0,{Dot.num l.width},{Dot.num l.height}"),
        ("dot: every edge has control points, 3n+1 of them after the arrow's tip",
          d2.edges.all fun (_, _, a) => match a.get? "pos" with
            | some p =>
              let ws := (p.splitOn " ").filter (!·.isEmpty)
              let pts := ws.filter (!·.startsWith "e,")
              ws.any (·.startsWith "e,") && pts.length % 3 == 1 && pts.length ≥ 4
            | none => false),
        ("dot: the edge label's place", (d2.edges.getD 2 (0, 0, #[])).2.2.get? "lp" |>.isSome),
        ("dot: every cluster's box", d2.clusters.all (·.attrs.get? "bb" |>.isSome)),
        ("dot: the attributes read are written back",
          (back 2).get? "color" == some "#336699"),
        ("dot: the same output twice", (layoutDot sample).toOption == (layoutDot sample).toOption)]
    | _, _ => #[("dot: the laid out sample reads back", false)]

/-- Whether reading `s` with limits `lim` fails. -/
def refused (s : String) (lim : Dot.Limits := {}) : Bool :=
  match Dot.parse s lim with
  | .error _ => true
  | .ok _ => false

/-- Hostile and malformed inputs. -/
def hostileChecks : Array (String × Bool) :=
  let deep := String.join (List.replicate 100 "subgraph cluster_x { ") ++
    String.join (List.replicate 100 "} ")
  let many := String.join ((List.range 50).map (s!"n{·}; "))
  #[("dot: an unterminated string is refused", refused "digraph { a [label=\"x] }"),
    ("dot: an unterminated comment is refused", refused "digraph { a /* b }"),
    ("dot: an HTML label is refused", refused "digraph { a [label=<b>x</b>] }"),
    ("dot: a port is refused", refused "digraph { a:n -> b }"),
    ("dot: a subgraph as an edge end is refused", refused "digraph { a -> {b c} }"),
    ("dot: blocks nested too deep are refused", refused s!"digraph \{ {deep} }"),
    ("dot: a hundred levels within a larger limit are read",
      !refused s!"digraph \{ {deep} }" { maxDepth := 200 }),
    ("dot: too many nodes are refused", refused s!"digraph \{ {many} }" { maxItems := 10 }),
    ("dot: an input over the size limit is refused",
      refused s!"digraph \{ {many} }" { maxBytes := 100 }),
    ("dot: a string over the length limit is refused",
      refused s!"digraph \{ a [label=\"{String.ofList (List.replicate 300 'x')}\"] }"
        { maxString := 200 }),
    ("dot: too many attributes are refused",
      refused s!"digraph \{ a [{", ".intercalate ((List.range 20).map (s!"k{·}=1"))}] }"
        { maxAttrs := 10 }),
    ("dot: a missing closing brace is refused", refused "digraph { a -> b"),
    ("dot: text after the graph is refused", refused "digraph { a } b"),
    ("dot: no header is refused", refused "{ a -> b }"),
    ("dot: an attribute without a value is refused", refused "digraph { a [label=] }"),
    ("dot: a stray character is refused", refused "digraph { a -> b ! }"),
    ("dot: an edge operator without a node is refused", refused "digraph { a -> }"),
    ("dot: a lone minus is refused", refused "digraph { - }"),
    ("dot: an empty input is refused", refused ""),
    ("dot: binary noise is refused", refused "digraph { \x01\x02 }"),
    ("dot: an empty graph is read and laid out", (layoutDot "graph {}").toOption.isSome)]

/-- A blueprint graph written as DOT by the quality harness, read back and laid out: the same
nodes, edges and nested clusters, and a layout that keeps the cluster rules. -/
def harnessChecks : Array (String × Bool) :=
  let g := GraphQuality.blueprint Fixtures.blueprintANodes Fixtures.blueprintAEdges
    Fixtures.blueprintASections 2
  match Dot.parse (GraphQuality.dotText g {} {}) with
  | .error e => #[(s!"dot: the harness's DOT is read ({e})", false)]
  | .ok d =>
    let h := d.toGraph
    #[("dot: the harness's DOT has the graph's nodes, edges and clusters",
        h.nodes.size == g.nodes.size && h.edges.size == g.edges.size &&
          h.clusters.size == g.clusters.size),
      ("dot: its layout keeps the cluster rules", (clusterProblems h h.layout).isEmpty)]

/-- All the DOT checks. -/
def checks : Array (String × Bool) := readChecks ++ writeChecks ++ hostileChecks ++ harnessChecks

end PILeanTest.GraphDot
