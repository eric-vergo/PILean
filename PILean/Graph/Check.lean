/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Graph.Layout
import PILean.Graph.Compound

/-!
# Checks of a finished layout

Two conditions on the geometry of a `Layout`, stated as functions that list every violation, so
that a test (or a caller) can check a drawing after the fact:

* **Clusters** (`clusterProblems`): every cluster box contains the boxes of exactly the nodes the
  cluster holds (its own and those of the clusters inside it) and no part of any other node's
  box; two cluster boxes are nested when one cluster holds the other and apart otherwise; the
  title fits the top of its box.
* **Clearance** (`clearanceProblems`): no edge passes through or within `margin` of the box of a
  node it does not end at; an edge between nodes that a cluster does not hold does not enter
  that cluster's box. The edges are flattened to polylines first.

Work: `O(C · (V + C))` for the clusters; for the clearance, the segments of the flattened edges
are bucketed on a grid of the boxes' size, so the work is the segments times the boxes that share
their cells.

## Main definitions

* `boxWithin`, `boxesMeet`, `clusterProblems`, `clearanceProblems`, `segmentHitsBox`.
-/

namespace PILean.Graph

/-- Whether the box `a` lies inside the box `b` (borders may touch). -/
def boxWithin (a b : Box) : Bool := b.x0 ≤ a.x0 && a.x1 ≤ b.x1 && b.y0 ≤ a.y0 && a.y1 ≤ b.y1

/-- Whether the boxes share area (touching borders do not count). -/
def boxesMeet (a b : Box) : Bool := a.x0 < b.x1 && b.x0 < a.x1 && a.y0 < b.y1 && b.y0 < a.y1

/-- The problems with the cluster boxes of a layout of `g` (see the module docstring); empty
when there is none. Clusters without a box and nodes without a box are skipped. -/
def clusterProblems (g : Graph) (l : Layout) : Array String := Id.run do
  let t := ClusterTree.of g
  let mut out : Array String := #[]
  for cb in l.clusters do
    let c := cb.index
    for nb in l.nodes do
      let holds := t.holdsOpt c (t.nodeCluster.getD nb.index none)
      if holds && !boxWithin nb.box cb.box then
        out := out.push s!"cluster {c} does not contain its node {nb.index}"
      if !holds && boxesMeet nb.box cb.box then
        out := out.push s!"cluster {c} overlaps node {nb.index}, not one of its nodes"
    for db in l.clusters do
      let d := db.index
      if c < d then
        if t.holds c d then
          if !boxWithin db.box cb.box then out := out.push s!"cluster {c} does not contain {d}"
        else if t.holds d c then
          if !boxWithin cb.box db.box then out := out.push s!"cluster {d} does not contain {c}"
        else if boxesMeet cb.box db.box then
          out := out.push s!"clusters {c} and {d} overlap"
  return out

/-- Whether the segment from `p` to `q` meets the box `b` (inside or on its border), by
clipping it to the box (Liang and Barsky). -/
def segmentHitsBox (p q : Point) (b : Box) : Bool := Id.run do
  let dx := q.x - p.x
  let dy := q.y - p.y
  let mut t0 : Float := 0
  let mut t1 : Float := 1
  for (pk, qk) in [(-dx, p.x - b.x0), (dx, b.x1 - p.x), (-dy, p.y - b.y0), (dy, b.y1 - p.y)] do
    if pk == 0 then
      if qk < 0 then return false
    else
      let r := qk / pk
      if pk < 0 then t0 := max t0 r else t1 := min t1 r
  return t0 ≤ t1

/-- The problems with the edges' clearance in a layout of `g` (see the module docstring): every
edge that comes within `margin` of the box of a node it does not end at, and every edge that
enters the box of a cluster holding neither of its ends. Self-loops are skipped. -/
def clearanceProblems (g : Graph) (l : Layout) (margin : Float := 2) : Array String := Id.run do
  let t := ClusterTree.of g
  let cell : Float := 96
  let key := fun (i j : Int) => s!"{i},{j}"
  -- the boxes by grid cell: (true for a node, its number, its box)
  let mut grid : Std.HashMap String (Array (Bool × Nat × Box)) := {}
  let entries : Array (Bool × Nat × Box) :=
    l.nodes.map (fun nb => (true, nb.index, nb.box.inset (-margin) (-margin) (-margin) (-margin)))
      ++ l.clusters.map fun cb => (false, cb.index, cb.box.inset 1 1 1 1)
  for e in entries do
    let b := e.2.2
    let at_ := fun (f : Float) => (f / cell).floor.toInt64.toInt.toNat
    for i in [at_ b.x0:at_ b.x1 + 1] do
      for j in [at_ b.y0:at_ b.y1 + 1] do
        grid := grid.insert (key i j) ((grid.getD (key i j) #[]).push e)
  let mut out : Array String := #[]
  for e in l.edges do
    if e.src == e.dst then continue
    let ends := fun (v : Nat) => v == e.src || v == e.dst
    let cs := t.nodeCluster.getD e.src none
    let cd := t.nodeCluster.getD e.dst none
    let pts := (e.path.flatten 0.5).foldl (fun acc pl => acc ++ pl.points) #[]
    let mut hit : Array (Bool × Nat) := #[]
    for k in [1:pts.size] do
      let p := pts.getD (k - 1) ⟨0, 0⟩
      let q := pts.getD k ⟨0, 0⟩
      let cx0 := (min p.x q.x / cell).floor.toInt64.toInt.toNat
      let cx1 := (max p.x q.x / cell).floor.toInt64.toInt.toNat
      let cy0 := (min p.y q.y / cell).floor.toInt64.toInt.toNat
      let cy1 := (max p.y q.y / cell).floor.toInt64.toInt.toNat
      for i in [cx0:cx1 + 1] do
        for j in [cy0:cy1 + 1] do
          for (isNode, idx, b) in grid.getD (key i j) #[] do
            if hit.contains (isNode, idx) then continue
            let relevant := if isNode then !ends idx
              else !t.holdsOpt idx cs && !t.holdsOpt idx cd
            if relevant && segmentHitsBox p q b then hit := hit.push (isNode, idx)
    for (isNode, idx) in hit do
      out := out.push (if isNode then s!"edge {e.index} passes node {idx}"
        else s!"edge {e.index} enters cluster {idx}")
  return out

end PILean.Graph
