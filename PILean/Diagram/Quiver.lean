/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Diagram.CommDiagram

/-!
# Quivers and dimension vectors

A `FinQuiver` is a finite set of vertices and a list of arrows between them: several arrows may
join the same two vertices, and an arrow may be a loop. It is drawn as a `CommDiagram`
(`FinQuiver.toCommDiagram`): arrows joining the same two vertices stand side by side, loops at
one vertex grow in size, and each arrow carries its name. With a dimension vector (the dimensions
of the spaces of a representation), vertex `i` is labelled by its dimension instead of its name.

Its faithfulness is that of `CommDiagram`: the drawn arrows are exactly the quiver's arrows with
their sources and targets, in order, and the texts exactly the vertex labels and arrow names
(`FinQuiver.Faithful`, `FinQuiver.arrows_figure`).

## Main definitions

* `FinQuiver`, `FinQuiver.vertexLabel`, `FinQuiver.toCommDiagram`, `FinQuiver.figure`,
  `FinQuiver.Faithful`

## Main results

* `FinQuiver.draw_faithful`, `FinQuiver.builder_faithful`
* `FinQuiver.arrows_toCommDiagram`: the arrows of the diagram are the quiver's.
-/

namespace PILean.Diagram

/-- A finite quiver: vertices `0, …, n - 1` with names and positions, arrows `(src, tgt, name)`,
and optionally a dimension vector. -/
structure FinQuiver where
  /-- The names of the vertices. -/
  vertices : Array String
  /-- The positions of the vertices. -/
  pos : Array QPoint
  /-- The arrows: source, target, name. -/
  arrows : List (Nat × Nat × String)
  /-- The dimension vector (empty for none): `dims[i]` is the dimension at vertex `i`. -/
  dims : Array Nat := #[]
  deriving Inhabited

namespace FinQuiver

/-- The label of vertex `i`: its dimension when there is a dimension vector, else its name. -/
def vertexLabel (Q : FinQuiver) (i : Nat) : String :=
  if Q.dims.isEmpty then Q.vertices.getD i "" else toString (Q.dims.getD i 0)

/-- The number of loops at `v` among the first `k` arrows: the bend that sets loop number `j`
at a vertex apart from the others (each one larger). -/
def loopsBefore (Q : FinQuiver) (k v : Nat) : Nat :=
  ((Q.arrows.take k).filter fun (s, t, _) => s = v && t = v).length

/-- The arrow of the diagram for arrow `k`: its ends and name, a loop bent by the number of
loops before it at its vertex. -/
def cdArrow (Q : FinQuiver) (k : Nat) (a : Nat × Nat × String) : CDArrow :=
  { src := a.1, tgt := a.2.1, label := a.2.2,
    bend := if a.1 = a.2.1 then (Q.loopsBefore k a.1 : Int) else 0 }

/-- The quiver as a diagram: its vertices (labelled by `vertexLabel`) and its arrows. -/
def toCommDiagram (Q : FinQuiver) : CommDiagram where
  objects := ((List.range Q.vertices.size).map Q.vertexLabel).toArray
  pos := Q.pos
  arrows := Q.arrows.zipIdx.map fun (a, k) => Q.cdArrow k a

/-- The diagram draws the quiver faithfully at `L` (`CommDiagram.Faithful`). -/
def Faithful (Q : FinQuiver) (L : CDLayout) (d : Diagram) : Prop := Q.toCommDiagram.Faithful L d

instance (Q : FinQuiver) (L : CDLayout) (d : Diagram) : Decidable (Q.Faithful L d) :=
  inferInstanceAs (Decidable (Q.toCommDiagram.Faithful L d))

/-- The figure of the quiver (`CommDiagram.figure`). -/
def figure (Q : FinQuiver) : Diagram := Q.toCommDiagram.figure

/-- The layout of `figure`. -/
def layout (Q : FinQuiver) : CDLayout := Q.toCommDiagram.layout

/-- The arrows of the diagram of `Q` are its arrows: `(k, src, tgt)` for arrow `k`. -/
theorem arrows_toCommDiagram (Q : FinQuiver) :
    Q.toCommDiagram.arrowTriples = Q.arrows.zipIdx.map fun (a, k) => (k, a.1, a.2.1) := by
  apply List.ext_getElem
  · simp [toCommDiagram, CommDiagram.arrowTriples]
  · intro i h₁ h₂
    simp [toCommDiagram, CommDiagram.arrowTriples, cdArrow]

/-- The quiver is drawn faithfully at every layout. -/
theorem draw_faithful (Q : FinQuiver) (L : CDLayout) : Q.Faithful L (Q.toCommDiagram.draw L) :=
  Q.toCommDiagram.draw_faithful L

/-- A well-formed quiver within the caps is drawn faithfully by `figure`. -/
theorem builder_faithful (Q : FinQuiver)
    (h : (Q.toCommDiagram.objects.size ≤ CommDiagram.maxObjects &&
      Q.toCommDiagram.arrows.length ≤ CommDiagram.maxArrows &&
      Q.toCommDiagram.twoCells.length ≤ CommDiagram.maxTwoCells && Q.toCommDiagram.Valid) = true) :
    Q.Faithful Q.layout Q.figure :=
  Q.toCommDiagram.builder_faithful h

end FinQuiver

end PILean.Diagram
