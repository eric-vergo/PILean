/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Explorer
import PILean.Graph.Model
import PILean.Exact.Plane

/-!
# Graphs and animations in plane figures

* `Plane.graph g pos`: a graph drawn among the other elements of a plane figure, its node `i` a
  point at the world position `pos[i]` with the node's label beside it (placed `auto`), its edges
  segments (arrows when the graph and the edge are directed), an edge's label at its middle.
  Every node carries its label as its title, every edge `src → dst`. `Plane.Exact.graph` takes
  exact points.
* `Plane.animation steps`: the steps of a sequence of plane figures as an `Animation`, all drawn
  in one frame (the world box that holds every step), so that nothing moves but what changes.
* `Plane.stepper`, `Plane.slider`: explorers (`Explorer`) whose frames are plane figures, in one
  frame likewise.

## Main definitions

* `Plane.graph`, `Plane.Exact.graph`, `Plane.commonView`, `Plane.animation`, `Plane.stepper`,
  `Plane.slider`.
-/

namespace PILean.Plane

/-- The graph `g` as plane items: node `i` a point at `pos[i]` (the origin when missing) with its
label beside it, the edges as segments or arrows between the points (see the module docstring);
self-loops are left out. -/
def graph (g : PILean.Graph) (pos : Array Point) : Item :=
  let at_ := fun (i : Nat) => pos.getD i ⟨0, 0⟩
  let edges := g.validEdges.filterMap fun (_, e) =>
    if e.src == e.dst then none
    else
      let a := at_ e.src
      let b := at_ e.dst
      let base := if g.directed && e.directed then arrow a b else segment a b
      let title := s!"{(g.nodes.getD e.src default).label} → {(g.nodes.getD e.dst default).label}"
      let item := base.faint.named title
      some (if e.label.isEmpty then #[item]
        else #[item, label e.label (a.mid b) .auto |>.faint])
  let nodes := g.nodes.mapIdx fun i nd =>
    let p := at_ i
    if nd.label.isEmpty then #[point p]
    else #[point p |>.named nd.label, label nd.label p .auto]
  group (edges.flatten ++ nodes.flatten)

/-- The graph `g` with node `i` at the exact point `pos[i]`, converted (see `Plane.graph`). -/
def Exact.graph {α : Type} [Exact.PlanePoint α] (g : PILean.Graph) (pos : Array α) : Item :=
  Plane.graph g (pos.map Exact.PlanePoint.toPoint)

/-- The figures with one view: the world box that the figure of every item of every step shows
(steps that have a `view` keep it). -/
def commonView (figs : Array Figure) : Array Figure :=
  match figs[0]? with
  | none => figs
  | some f0 =>
    let all : Figure := { f0 with items := figs.flatMap (·.items), view := none }
    let v := all.frame.view
    figs.map fun f => if f.view.isSome then f else
      { f with view := some v, height := some all.frame.height, padding := 0 }

/-- The steps as an animation of `secondsPerStep` each (see the module docstring). -/
def animation (steps : Array Figure) (secondsPerStep : Float := 1) : Animation :=
  (Explorer.stepper ((commonView steps).map fun f => ("", ExplorerFrame.ofPlane f))).toAnimation 0
    secondsPerStep

/-- A step sequence of plane figures with their captions, in one frame. -/
def stepper (steps : Array (String × Figure)) (poster : Nat := 0) : Explorer :=
  let figs := commonView (steps.map (·.2))
  Explorer.stepper ((steps.map (·.1)).zip (figs.map ExplorerFrame.ofPlane)) poster

/-- A parameter axis named `name` of plane figures with their value labels, in one frame. -/
def slider (name : String) (values : Array (String × Figure)) (poster : Nat := 0) : Explorer :=
  let figs := commonView (values.map (·.2))
  Explorer.slider name ((values.map (·.1)).zip (figs.map ExplorerFrame.ofPlane)) poster

end PILean.Plane
