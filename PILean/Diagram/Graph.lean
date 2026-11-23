/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Diagram.Basic
import PILean.Graph.Spec

/-!
# Finite graphs and digraphs

A `FinGraph` is an adjacency relation on `Fin n`, directed or not, with names for the vertices.
It is drawn at exact positions (`Layout`: on a circle, on a grid, or given) as a `Diagram`, or
with the layered layout of `PILean.Graph` (`FinGraph.toGraph`).

The edges drawn are `edgePairs`: for a directed graph every pair `(i, j)` with `adj i j`, a loop
`(i, i)` included; for an undirected one every pair `(i, j)` with `i ≤ j` and `adj i j` or
`adj j i`, so each edge of a symmetric relation once. A loop is drawn as a circle through its
vertex.

## Main definitions

* `FinGraph`, `FinGraph.drawn`, `FinGraph.edgePairs`, `FinGraph.label`
* `circlePoint`, `Layout.circular`, `Layout.grid`: exact layouts
* `FinGraph.draw`, `FinGraph.figure`, `FinGraph.Faithful`, `FinGraph.toGraph`
* `FinGraph.maxVertices`: the cap on the vertices a figure draws

## Main results

* `FinGraph.mem_edgePairs`: a pair is drawn exactly when its two vertices exist and are adjacent
  (in the sense of `drawn`); `edgePairs_nodup`: each once.
* `FinGraph.draw_faithful`, `FinGraph.builder_faithful`: the diagram draws exactly the edges
  `edgePairs`, in order, and the vertices `0, …, n - 1`, each mark where the layout puts its part.
* `FinGraph.toGraph_layout_edges`: the layered layout has one route for each pair of
  `edgePairs`, in order.
-/

namespace PILean.Diagram

/-- A finite graph on the vertices `0, …, n - 1`: an adjacency relation, whether it is directed,
and the vertices' names (vertex `i` is named `names[i]`, or its number when there is none). -/
structure FinGraph where
  /-- The number of vertices. -/
  n : Nat
  /-- The adjacency relation. -/
  adj : Fin n → Fin n → Bool
  /-- Whether the graph is directed. -/
  directed : Bool := false
  /-- Whether a directed edge is drawn with an arrowhead (a Hasse diagram's covers are not: their
  direction is up the page). -/
  arrowheads : Bool := true
  /-- The vertices' names. -/
  names : Array String := #[]

/-- The exact positions of the vertices: vertex `i` at `pos i`. -/
structure Layout where
  /-- The position of vertex `i`. -/
  pos : Nat → QPoint
  /-- The radius of a loop's circle. -/
  loop : Rat := 1 / 8

/-- The centre of the circle of a loop at `p` with radius `r`: straight above `p`, so the circle
passes through `p`. -/
def loopCentre (p : QPoint) (r : Rat) : QPoint := (p.1, p.2 + r)

/-- A point of the unit circle with rational coordinates near the angle `θ` (radians,
counterclockwise from the `x` axis): the rational parametrisation
`((1 - t²) / (1 + t²), 2t / (1 + t²))` at `t`, the tangent of a quarter of the angle's remainder
by quarter turns rounded to a multiple of `10⁻⁶`, turned by those quarter turns exactly. The
point is on the unit circle exactly; its angle is `θ` up to the rounding, computed in floating
point. -/
def circlePoint (θ : Float) : QPoint :=
  let quarter := 1.5707963267948966
  let k := (θ / quarter).round
  let φ := θ - k * quarter
  let tF := (Float.tan (φ / 2) * 1000000).round
  let t : Rat := (if tF < 0 then -((-tF).toUInt64.toNat : Rat) else (tF.toUInt64.toNat : Rat)) /
    1000000
  let p : QPoint := ((1 - t * t) / (1 + t * t), 2 * t / (1 + t * t))
  let turns := (if k < 0 then 4 - ((-k).toUInt64.toNat % 4) else k.toUInt64.toNat) % 4
  match turns with
  | 1 => (-p.2, p.1)
  | 2 => (-p.1, -p.2)
  | 3 => (p.2, -p.1)
  | _ => p

namespace Layout

/-- The `n` vertices on a circle of radius `radius`, vertex 0 at the top and the others
clockwise at (nearly) equal angles (`circlePoint`), every point exactly on the circle. -/
def circular (n : Nat) (radius : Rat := 1) : Layout where
  pos i :=
    let θ := 3.141592653589793 / 2 - 2 * 3.141592653589793 * i.toFloat / n.toFloat
    let p := circlePoint θ
    (radius * p.1, radius * p.2)

/-- The vertices on a grid of `cols` columns, `gap` apart, row by row from the top left. -/
def grid (cols : Nat) (gap : Rat := 1) : Layout where
  pos i := (gap * ((i % max cols 1 : Nat) : Rat), -gap * ((i / max cols 1 : Nat) : Rat))

/-- The vertices at the given positions (the origin for a vertex without one). -/
def given (ps : Array QPoint) : Layout where
  pos i := ps.getD i (0, 0)

end Layout

namespace FinGraph

/-- The most vertices `figure` draws; a larger graph is drawn as nothing but a note. The work of
`edgePairs` is the square of the number of vertices. -/
def maxVertices : Nat := 256

/-- The name of vertex `i`: `names[i]`, or the number `i` when there is none. -/
def label (g : FinGraph) (i : Nat) : String := g.names.getD i (toString i)

/-- Whether the pair `(i, j)` is drawn as an edge: `adj i j` for a directed graph; for an
undirected one, `i ≤ j` and `adj i j` or `adj j i`. -/
def drawn (g : FinGraph) (i j : Fin g.n) : Bool :=
  if g.directed then g.adj i j else decide (i ≤ j) && (g.adj i j || g.adj j i)

/-- The pairs drawn as edges, in the order of the first vertex and then the second
(`Graph.relationPairs` of `drawn` on `0, …, n - 1`). -/
def edgePairs (g : FinGraph) : List (Nat × Nat) :=
  Graph.relationPairs (List.finRange g.n) g.drawn

/-- A pair is in `edgePairs` exactly when both its vertices exist and the pair is drawn. -/
theorem mem_edgePairs (g : FinGraph) (i j : Nat) :
    (i, j) ∈ g.edgePairs ↔ ∃ (hi : i < g.n) (hj : j < g.n), g.drawn ⟨i, hi⟩ ⟨j, hj⟩ = true := by
  rw [edgePairs, Graph.mem_relationPairs]
  constructor
  · rintro ⟨a, b, ha, hb, h⟩
    rw [List.getElem?_eq_some_iff] at ha hb
    obtain ⟨hi, rfl⟩ := ha
    obtain ⟨hj, rfl⟩ := hb
    simp only [List.length_finRange] at hi hj
    exact ⟨hi, hj, by simpa using h⟩
  · rintro ⟨hi, hj, h⟩
    exact ⟨⟨i, hi⟩, ⟨j, hj⟩, by simp [hi], by simp [hj], h⟩

/-- Each pair is drawn once. -/
theorem edgePairs_nodup (g : FinGraph) : g.edgePairs.Nodup :=
  Graph.relationPairs_nodup _ _

/-- The mark of an edge: a circle through the vertex for a loop, an arrow for a directed edge
drawn with arrowheads, a segment otherwise. -/
def edgeMark (g : FinGraph) (L : Layout) (e : Nat × Nat) : Mark :=
  { part := .edge e.1 e.2, ink := .faint,
    shape := if e.1 = e.2 then .circle (loopCentre (L.pos e.1) L.loop) L.loop
      else if g.directed && g.arrowheads then .arrow (L.pos e.1) (L.pos e.2)
      else .segment (L.pos e.1) (L.pos e.2) }

/-- Whether a mark is placed where the layout puts its part: a vertex's dot at its position and
its name there, an edge's shape as `edgeMark` makes it. A mark of any other part is refused. -/
def placed (g : FinGraph) (L : Layout) (m : Mark) : Bool :=
  match m.part, m.shape with
  | .vertex i, .dot p => p == L.pos i
  | .vertex i, .text s p _ => s == g.label i && p == L.pos i
  | .vertex _, _ => false
  | .edge i j, s => s == (g.edgeMark L (i, j)).shape
  | _, _ => false

/-- The diagram of the graph at the layout `L`: the edges (`edgeMark`, in the order of
`edgePairs`), then a dot for each vertex, then each vertex's name beside it. -/
def draw (g : FinGraph) (L : Layout) : Diagram where
  marks := g.edgePairs.map (g.edgeMark L) ++
    (List.range g.n).map (fun i => { part := .vertex i, shape := .dot (L.pos i) }) ++
    (List.range g.n).map (fun i =>
      { part := .vertex i, shape := .text (g.label i) (L.pos i) .auto })

/-- The names as the diagram writes them: vertex `i`'s name at its position, for each `i`. -/
def nameTexts (g : FinGraph) (L : Layout) : List (Part × String × QPoint) :=
  (List.range g.n).map fun i => (.vertex i, g.label i, L.pos i)

/-- The diagram draws the graph faithfully at the layout `L`: its edges are exactly `edgePairs`,
in order; its vertex dots are `0, …, n - 1`, in order; its texts are exactly the vertices' names
at their positions (`nameTexts`), in order; it has no decoration (`Diagram.decorations`); and
every mark is placed where `L` puts its part (`placed`). -/
def Faithful (g : FinGraph) (L : Layout) (d : Diagram) : Prop :=
  d.edges = g.edgePairs ∧ d.vertices = List.range g.n ∧ d.marks.all (g.placed L) = true ∧
    d.texts = g.nameTexts L ∧ d.decorations = []

instance (g : FinGraph) (L : Layout) (d : Diagram) : Decidable (g.Faithful L d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The diagram of a graph is faithful at every layout. -/
theorem draw_faithful (g : FinGraph) (L : Layout) : g.Faithful L (g.draw L) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Diagram.edges, draw, edgeMark, List.filterMap_append, List.filterMap_map,
      Function.comp_def]
  · simp [Diagram.vertices, draw, edgeMark, List.filterMap_append, List.filterMap_map,
      Function.comp_def]
  · simp only [draw, List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true,
      Function.comp_apply]
    refine ⟨⟨fun e _ => ?_, fun i _ => ?_⟩, fun i _ => ?_⟩ <;> simp [placed, edgeMark]
  · have h : ∀ e, (match (g.edgeMark L e).shape with
        | .text s p _ => some ((g.edgeMark L e).part, s, p)
        | _ => none) = none := fun e => by
      unfold edgeMark
      by_cases h1 : e.1 = e.2 <;> by_cases h2 : (g.directed && g.arrowheads) = true <;>
        simp [h1, h2]
    simp [Diagram.texts, draw, List.filterMap_append, List.filterMap_map, nameTexts,
      Function.comp_def]
    intro a b _
    exact h (a, b)
  · simp [Diagram.decorations, draw, edgeMark, List.filterMap_append, List.filterMap_map,
      Function.comp_def]

/-- The layout of `figure`: the vertices on the unit circle. -/
def layout (g : FinGraph) : Layout := Layout.circular g.n

/-- The figure of a graph: its diagram on the circle (`layout`), or, for more than `maxVertices`
vertices, a diagram with a note only. -/
def figure (g : FinGraph) : Diagram :=
  if g.n ≤ maxVertices then g.draw g.layout
  else
    let note := s!"{g.n} vertices: too many to draw"
    { marks := [{ part := .note 0, shape := .text note (0, 0) .center }] }

/-- A graph with at most `maxVertices` vertices is drawn faithfully by `figure`. -/
theorem builder_faithful (g : FinGraph) (h : g.n ≤ maxVertices) :
    g.Faithful g.layout g.figure := by
  unfold figure
  split
  · exact g.draw_faithful _
  · contradiction

/-- The graph for the layered layout of `PILean.Graph`: node `i` named `label i`, an edge for
every pair of `edgePairs`. -/
def toGraph (g : FinGraph) : Graph :=
  Graph.ofRelation (List.finRange g.n) g.drawn (fun i => g.label i) g.directed

/-- The layered layout of `toGraph` has one route for each pair of `edgePairs`, in order, with
that pair's ends. -/
theorem toGraph_layout_edges (g : FinGraph) (o : Graph.LayeredOptions) (st : Style) :
    (g.toGraph.layout o st).edges.toList.map (fun e => (e.index, e.src, e.dst)) =
      (List.range g.edgePairs.length).zip g.edgePairs :=
  Graph.ofRelation_layout_edges _ _ _ _ o st

end FinGraph

/-- The hypotheses can be met: the directed 2-cycle on two vertices draws the edges `(0, 1)` and
`(1, 0)`. -/
example : (FinGraph.mk 2 (fun i j => i != j) true true #[]).edgePairs = [(0, 1), (1, 0)] := by
  decide

end PILean.Diagram
