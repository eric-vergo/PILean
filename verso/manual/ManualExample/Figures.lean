/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Trust.Attr
import PILeanVersoManual.Themes
import ManualExample.Defs

/-!
# The example manual's figures

* `trianglePlot`: the triangular numbers 0 to 12, from `ManualExample.triangle` (another
  module), linked to `trianglePoints_spec`, which applies `two_mul_triangle` to its points;
* `divisorGraph`: the divisors of 12 joined by the covering relation of divisibility;
* `marks`: two numbered marks drawn over a picture of the site (`backdrop`), in each theme.
-/

namespace ManualExample

open PILean PILean.Plot PILean.Trust

/-- The points `(n, triangle n)` for `n` from 0 to 12. -/
def trianglePoints : List (Int × Int) :=
  (List.range 13).map fun n => (Int.ofNat n, Int.ofNat (triangle n))

/-- The triangular numbers 0 to 12. -/
@[figure]
def trianglePlot : Figure where
  title := "Triangular numbers"
  panels := #[{
      x := { label := "n" }, y := { label := "0 + 1 + … + n" },
      series := #[.ofIntPoints "triangle n" trianglePoints,
        .scatterOfIntPoints "n" trianglePoints] }]

/-- The figure `trianglePlot` has one panel, whose series are a line and markers over
`trianglePoints` and no other; the points of both are that list converted point for point; and
every point of the list satisfies the closed form of `two_mul_triangle`: twice its height is
`n (n + 1)`. -/
theorem trianglePoints_spec :
    trianglePlot.panels.map (·.series) =
        #[#[.ofIntPoints "triangle n" trianglePoints,
          .scatterOfIntPoints "n" trianglePoints]] ∧
      (Series.ofIntPoints "triangle n" trianglePoints).points =
        (trianglePoints.map fun p => Exact.toPoint (Exact.ofIntPair p)).toArray ∧
      (Series.scatterOfIntPoints "n" trianglePoints).points =
        (trianglePoints.map fun p => Exact.toPoint (Exact.ofIntPair p)).toArray ∧
      ∀ p ∈ trianglePoints, 2 * p.2 = p.1 * (p.1 + 1) := by
  refine ⟨by simp [trianglePlot], Series.ofIntPoints_points ..,
    Series.scatterOfIntPoints_points .., fun p hp => ?_⟩
  simp only [trianglePoints, List.mem_map, List.mem_range] at hp
  obtain ⟨n, -, rfl⟩ := hp
  show (2 : Int) * (triangle n : Int) = (n : Int) * ((n : Int) + 1)
  exact_mod_cast two_mul_triangle n

/-- The divisors of 12. -/
def divisors12 : List Nat := [1, 2, 3, 4, 6, 12]

/-- `b` covers `a` in divisibility among the divisors of 12. -/
def covers (a b : Nat) : Bool :=
  a < b && b % a == 0 &&
    divisors12.all fun c => !(a < c && c < b && c % a == 0 && b % c == 0)

/-- The divisors of 12 ordered by divisibility. -/
@[figure]
def divisorGraph : PILean.Graph := Graph.ofRelation divisors12 covers toString

/-- The edges of `divisorGraph` are exactly the covering pairs among the divisors of 12, in
order, and there are 7 of them. -/
theorem covers_count :
    divisorGraph.edges.toList.map (fun e => (e.src, e.dst)) =
        Graph.relationPairs divisors12 covers ∧
      (Graph.relationPairs divisors12 covers).length = 7 :=
  ⟨Graph.ofRelation_edge_pairs divisors12 covers toString true, by decide +kernel⟩

/-- Numbered marks to be drawn over a picture: the picture's size and the marks' centres. -/
structure Marks where
  /-- The width of the picture the marks are drawn over. -/
  width : Float
  /-- Its height. -/
  height : Float
  /-- The centres of the marks, numbered from 1. -/
  centres : Array Point

/-- The marks as a drawing, a ring of `ink` around each number. -/
def Marks.shape (m : Marks) (ink : Rgba) : Canvas.Shape :=
  .group (m.centres.zipIdx.map fun (c, i) => .group #[
    .path (Canvas.circle c 14) (some (.solid ink)),
    .text (toString (i + 1)) ⟨c.x, c.y + 6⟩ 16 ⟨255, 255, 255, 255⟩ .middle 1.4])

/-- The SVG of the marks in the colour `ink`. -/
def Marks.svg (m : Marks) (ink : Rgba) : String :=
  (m.shape ink).toSvg m.width m.height "Helvetica, Arial, sans-serif"

/-- The SVG output of the marks in `ink`, with the file name suffix `name`. -/
def Marks.output (m : Marks) (name : String) (ink : Rgba) : Output :=
  let svg := (m.svg ink).toUTF8
  { name, format := .svg, bytes := fun _ => .ok svg, spec := svg }

/-- Marks are drawn as an SVG. -/
instance : ToOutputs Marks where
  outputs m := #[m.output "" ⟨11, 108, 116, 255⟩]

/-- Marks are drawn in a light and a dark colour. -/
instance : PILeanVerso.SiteOutputs Marks where
  siteOutputs m := #[m.output "" ⟨11, 108, 116, 255⟩, m.output "-dark" ⟨92, 196, 203, 255⟩]

/-- Two marks on the example's picture of a window. -/
@[figure]
def marks : Marks := { width := 320, height := 200, centres := #[⟨60, 40⟩, ⟨240, 150⟩] }

end ManualExample
