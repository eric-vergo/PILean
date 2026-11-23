/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Diagram.Graph

/-!
# Rooted trees and forests

A `Forest` gives each vertex `0, …, n - 1` its parent (`none` for a root) and orders each vertex's
children by number. It is drawn with the tidy layout of Reingold and Tilford: every subtree is
laid out on its own, the subtrees of a vertex's children are put side by side, each as far left
as its left contour allows at a distance of at least 1 from the right contour of those before it,
and the vertex is centred above its first and last child; the trees of a forest are put side by
side the same way. Depth `d` is drawn at height `-d`, the roots at the top. All positions are
exact rationals.

A binary tree (`BinTree`) gives each vertex an optional left and right child; a lone child is
drawn to its side, as if its missing sibling took a place.

The edges drawn are the parent links `(p, c)`, from parent to child, as a `FinGraph` (directed,
no arrowheads), so the faithfulness of graphs carries over: the drawn edges are exactly the pairs
`(parent c, c)`.

A vertex that no root reaches (the parent links of the data have a cycle) is drawn in a row below
the forest; `Forest.IsForest` says whether that happens.

## Main definitions

* `Forest`, `Forest.children`, `Forest.IsForest`, `Forest.toFinGraph`, `Forest.figure`
* `tidy`: the Reingold–Tilford layout
* `BinTree`, `BinTree.toForest`

## Main results

* `Forest.mem_edges`: a drawn edge is exactly a parent link.
* `Forest.draw_faithful`, `Forest.builder_faithful`.

## References

* E. M. Reingold, J. S. Tilford, *Tidier drawings of trees*, IEEE Transactions on Software
  Engineering 7 (1981), 223–228.
-/

namespace PILean.Diagram

/-- A laid-out subtree: each vertex with its abscissa relative to the subtree's root and its depth
below it, and the leftmost and rightmost abscissae at each depth (the contours). -/
structure SubLayout where
  /-- The vertices with their relative abscissae and depths. -/
  pos : List (Nat × Rat × Nat)
  /-- The left contour, from the root's depth down. -/
  left : List Rat
  /-- The right contour. -/
  right : List Rat

/-- A single vertex. -/
def SubLayout.leaf (v : Nat) : SubLayout := ⟨[(v, 0, 0)], [0], [0]⟩

/-- A place without a vertex (the missing child of a binary tree). -/
def SubLayout.gap : SubLayout := ⟨[], [0], [0]⟩

/-- The shift that puts the subtree `s` at a distance of at least 1 right of the contour `r` at
every depth both have. -/
def placeShift (r : List Rat) (s : SubLayout) : Rat :=
  (r.zip s.left).foldl (fun m (a, b) => max m (a - b + 1)) (r.headD 0 - s.left.headD 0 + 1)

/-- Two contours joined: `a` where it is defined, `b` below. -/
def joinContour (a b : List Rat) : List Rat := a ++ b.drop a.length

/-- The subtrees side by side, each as far left as `placeShift` allows: their offsets, the left
and the right contour of the whole. -/
def sideBySide (subs : List SubLayout) : List Rat × List Rat × List Rat :=
  match subs with
  | [] => ([], [], [])
  | s :: rest =>
    rest.foldl (fun (offs, l, r) t =>
      let o := placeShift r t
      (offs ++ [o], joinContour l (t.left.map (· + o)), joinContour (t.right.map (· + o)) r))
      ([0], s.left, s.right)

/-- The subtrees as the children of `v`: placed side by side, `v` centred above the first and
the last. -/
def underRoot (v : Nat) (subs : List SubLayout) : SubLayout :=
  if subs.isEmpty then .leaf v else
  let (offs, l, r) := sideBySide subs
  let mid := (offs.headD 0 + offs.getLastD 0) / 2
  ⟨(v, 0, 0) :: (offs.zip subs).flatMap (fun (o, s) => s.pos.map fun (w, x, d) => (w, x + o - mid,
      d + 1)), 0 :: l.map (· - mid), 0 :: r.map (· - mid)⟩

/-- The tidy layout of the subtree of `v`, with the children of each vertex given by `kids`
(`none` for a missing child's place), at most `fuel` levels deep. -/
def tidySub (kids : Nat → List (Option Nat)) : Nat → Nat → SubLayout
  | 0, v => .leaf v
  | fuel + 1, v =>
    let ks := kids v
    if ks.isEmpty then .leaf v
    else underRoot v (ks.map fun | some c => tidySub kids fuel c | none => .gap)

/-- The tidy layout of a forest of `n` vertices with the roots `roots`: the trees side by side,
depth `d` at height `-d`, and every vertex no root reaches in a row below. -/
def tidy (n : Nat) (kids : Nat → List (Option Nat)) (roots : List Nat) : Array QPoint := Id.run do
  let subs := roots.map (tidySub kids n)
  let (offs, _, _) := sideBySide subs
  let mut pos : Array (Option QPoint) := Array.replicate n none
  let mut deepest := 0
  for (o, s) in offs.zip subs do
    for (w, x, d) in s.pos do
      if w < n && (pos.getD w none).isNone then
        pos := pos.set! w (some (x + o, -(d : Rat)))
        deepest := max deepest d
  let mut k : Nat := 0
  let mut out : Array QPoint := #[]
  for i in [0:n] do
    match pos.getD i none with
    | some p => out := out.push p
    | none =>
      out := out.push ((k : Rat), -((deepest : Rat) + 2))
      k := k + 1
  return out

/-- A rooted forest on the vertices `0, …, n - 1`: the parent of each vertex (`none` for a root;
a parent `≥ n` is read as none), and the vertices' names. -/
structure Forest where
  /-- The number of vertices. -/
  n : Nat
  /-- The parent of each vertex. -/
  parent : Nat → Option Nat
  /-- The vertices' names. -/
  names : Array String := #[]

namespace Forest

/-- The most vertices `figure` draws. -/
def maxVertices : Nat := 512

/-- The parent of `c`, when it is a vertex. -/
def parentOf (F : Forest) (c : Nat) : Option Nat := (F.parent c).filter (· < F.n)

/-- The children of `v`, in order. -/
def children (F : Forest) (v : Nat) : List Nat :=
  (List.range F.n).filter fun c => F.parentOf c == some v

/-- The roots, in order. -/
def roots (F : Forest) : List Nat := (List.range F.n).filter fun c => (F.parentOf c).isNone

/-- Whether every vertex reaches a root by at most `n` parent links: the parent links have no
cycle. -/
def IsForest (F : Forest) : Prop :=
  (List.range F.n).all (fun v =>
    ((List.range F.n).foldl (fun c _ => c.bind F.parentOf) (some v)).isNone) = true

instance (F : Forest) : Decidable F.IsForest := inferInstanceAs (Decidable (_ = _))

/-- The graph of the parent links: an edge `(p, c)` for each vertex `c` with parent `p`, directed,
drawn without arrowheads. -/
def toFinGraph (F : Forest) : FinGraph where
  n := F.n
  adj p c := F.parentOf c.val == some p.val
  directed := true
  arrowheads := false
  names := F.names

/-- The tidy layout of the forest. -/
def layout (F : Forest) : Layout :=
  Layout.given (tidy F.n (fun v => (F.children v).map some) F.roots)

/-- The diagram at a layout. -/
def draw (F : Forest) (L : Layout) : Diagram := F.toFinGraph.draw L

/-- The diagram draws the forest faithfully at `L`: the graph of its parent links, faithful at
`L` (`FinGraph.Faithful`). -/
def Faithful (F : Forest) (L : Layout) (d : Diagram) : Prop := F.toFinGraph.Faithful L d

instance (F : Forest) (L : Layout) (d : Diagram) : Decidable (F.Faithful L d) :=
  inferInstanceAs (Decidable (F.toFinGraph.Faithful L d))

/-- The diagram of a forest is faithful at every layout. -/
theorem draw_faithful (F : Forest) (L : Layout) : F.Faithful L (F.draw L) := by sorry

/-- A drawn edge is exactly a parent link: `(p, c)` with `c` a vertex whose parent is the vertex
`p`. -/
theorem mem_edges (F : Forest) (L : Layout) (p c : Nat) :
    (p, c) ∈ (F.draw L).edges ↔ p < F.n ∧ c < F.n ∧ F.parentOf c = some p := by sorry

/-- The figure: the diagram at the tidy layout, or a note for more than `maxVertices`
vertices. -/
def figure (F : Forest) : Diagram :=
  if F.n ≤ maxVertices then { F.draw F.layout with width := min 560 (48 * F.n.toFloat + 24) }
  else { marks := [{ part := .note 0, shape := .text "too many vertices to draw" (0, 0) .center }] }

/-- A forest the figure draws is drawn faithfully. -/
theorem builder_faithful (F : Forest) (h : F.n ≤ maxVertices) : F.Faithful F.layout F.figure := by sorry

end Forest

/-- A binary tree on the vertices `0, …, n - 1`: each vertex's left and right child (a child
`≥ n` is read as none), and the vertices' names. -/
structure BinTree where
  /-- The number of vertices. -/
  n : Nat
  /-- The left child of each vertex. -/
  left : Nat → Option Nat
  /-- The right child of each vertex. -/
  right : Nat → Option Nat
  /-- The vertices' names. -/
  names : Array String := #[]

namespace BinTree

/-- The children's places of `v`: none without children, otherwise the left and the right place
(`none` for a missing child). -/
def places (B : BinTree) (v : Nat) : List (Option Nat) :=
  let l := (B.left v).filter (· < B.n)
  let r := (B.right v).filter (· < B.n)
  if l.isNone && r.isNone then [] else [l, r]

/-- The parent of `c`: the first vertex that has it as a child. -/
def parent (B : BinTree) (c : Nat) : Option Nat :=
  (List.range B.n).find? fun v => (B.places v).contains (some c)

/-- The forest of the binary tree: its parent links. -/
def toForest (B : BinTree) : Forest := ⟨B.n, B.parent, B.names⟩

/-- The layout: the tidy layout with the children's places, so a lone child stands to its
side. -/
def layout (B : BinTree) : Layout :=
  Layout.given (tidy B.n B.places B.toForest.roots)

/-- The figure: the forest's diagram at the binary layout (faithful by `Forest.draw_faithful`), or
a note for more than `Forest.maxVertices` vertices. -/
def figure (B : BinTree) : Diagram :=
  if B.n ≤ Forest.maxVertices then
    { B.toForest.draw B.layout with width := min 560 (48 * B.n.toFloat + 24) }
  else { marks := [{ part := .note 0, shape := .text "too many vertices to draw" (0, 0) .center }] }

/-- A binary tree the figure draws is drawn faithfully, as the forest of its parent links. -/
theorem builder_faithful (B : BinTree) (h : B.n ≤ Forest.maxVertices) :
    B.toForest.Faithful B.layout B.figure := by sorry

end BinTree

/-- The hypotheses can be met: the path `0 → 1 → 2` is a forest whose only root is `0`. -/
example : (Forest.mk 3 (fun c => if c = 0 then none else some (c - 1)) #[]).IsForest ∧
    (Forest.mk 3 (fun c => if c = 0 then none else some (c - 1)) #[]).roots = [0] := by sorry

end PILean.Diagram
