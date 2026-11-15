/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanTest.Examples

/-!
# Checks of the exact layers

Values and edge cases of the exact rationals and sample grids (`PILean.Exact`), the exact series
(`PILean.Plot.Exact`), the graph of a relation (`PILean.Graph.Spec`) and the exact frame times
(`PILean.Anim.Proofs`), and the hypotheses of their theorems on the gallery's pictures: that
every converted point has a position on its panel, so that the theorems about the drawing
apply.
-/

namespace PILeanTest.ExactChecks

open PILean PILean.Plot PILeanTest.ProvedExamples

/-- A grid point as `(numerator, denominator)` reduced by the greatest common divisor. -/
def reduced (q : Q) : Int × Nat :=
  let g := Nat.gcd q.num.natAbs q.den
  (q.num / g, q.den / g)

/-- The reduced grid of `n` steps from `lo` to `hi`. -/
def gridOf (lo hi : Q) (n : Nat) : List (Int × Nat) := (Q.grid lo hi n).map reduced

/-- The panel layouts of a figure and its style. -/
def layoutsOf (fig : Figure) : Array PanelLayout := fig.layout

/-- Whether every point of the series has a position on the first panel of the figure. -/
def allPositioned (fig : Figure) (s : Series) : Bool :=
  match (layoutsOf fig)[0]? with
  | some l => s.points.all fun p => (l.pos p).isSome
  | none => false

/-- The pixel positions of a series' points on the first panel of a figure. -/
def pixels (fig : Figure) (s : Series) : Array Point :=
  match (layoutsOf fig)[0]? with
  | some l => s.points.map fun p => (l.pos p).getD ⟨0, 0⟩
  | none => #[]

/-- The checks. -/
def checks : Array (String × Bool) :=
  let zero := Q.ofInt 0
  let one := Q.ofInt 1
  let third := Q.ofFrac 1 3
  let l := (layoutsOf provedFunction)[0]!
  let st := provedFunction.style
  let cubicDraw := drawSeries st l cubicSeries 0
  let dataLine := Series.ofIntPoints "line" residues
  let dataDots := Series.scatterOfIntPoints "points" residues
  let rel := Graph.ofRelation [1, 2, 3] (fun _ _ => false) toString
  let refl := Graph.ofRelation [1, 2] (fun a b => a == b) toString
  let cyc := Graph.ofRelation [1, 2] (fun a b => a != b) toString
  let noFps : Animation := { provedClock with fps := 0 }
  #[("grid: four steps on [0, 1]",
      gridOf zero one 4 == [(0, 1), (1, 4), (1, 2), (3, 4), (1, 1)]),
    ("grid: one step is its two ends", gridOf zero one 1 == [(0, 1), (1, 1)]),
    ("grid: no steps is the single point lo", gridOf third one 0 == [(1, 3)]),
    ("grid: a descending interval", gridOf one zero 2 == [(1, 1), (1, 2), (0, 1)]),
    ("grid: a degenerate interval repeats its point",
      gridOf third third 3 == [(1, 3), (1, 3), (1, 3), (1, 3)]),
    ("grid: a negative start with a fractional end",
      gridOf (Q.ofFrac (-3) 2) (Q.ofFrac 3 2) 3 == [(-3, 2), (-1, 2), (1, 2), (3, 2)]),
    ("grid: n + 1 points", (Q.grid zero one 24).length == 25),
    ("samples: the cubic at -3/2, 0 and 3/2",
      ((Q.samples cubic lo hi steps).map (fun (x, y) => (reduced x, reduced y))).take 1 ==
        [((-3, 2), (-15, 8))] &&
      (reduced (cubic zero) == (0, 1)) && (reduced (cubic hi) == (15, 8))),
    ("samples: the parabola at its end",
      reduced (parabola hi) == (5, 4)),
    ("Q: sums and products by cross multiplication",
      reduced (Q.ofFrac 1 2 + Q.ofFrac 1 3) == (5, 6) &&
      reduced (Q.ofFrac 2 3 * Q.ofFrac (-3) 4) == (-1, 2) &&
      reduced (Q.ofFrac 1 2 - Q.ofFrac 1 3) == (1, 6)),
    ("Q: equivalence and order of unreduced fractions",
      decide (Q.Equiv (Q.ofFrac 2 4) (Q.ofFrac 1 2)) &&
        decide (Q.lt (Q.ofFrac 1 3) (Q.ofFrac 1 2)) &&
        !decide (Q.lt (Q.ofFrac 1 2) (Q.ofFrac 2 4))),
    ("toFloat: exact for dyadic fractions, nearest otherwise",
      (Q.ofFrac (-15) 8).toFloat == -1.875 && third.toFloat == 1.0 / 3.0 &&
      (Q.ofInt (-7)).toFloat == -7.0),
    ("ofExact: 25 points from -1.5 to 1.5 in equal steps",
      cubicSeries.points.size == 25 && (cubicSeries.points[0]?.map (·.x)) == some (-1.5) &&
      (cubicSeries.points[24]?.map (·.x)) == some 1.5 &&
      (cubicSeries.points[1]?.map (·.x)) == some (-1.375)),
    ("ofExact: the values are those of the function at the grid",
      (cubicSeries.points[0]?.map (·.y)) == some (-1.875) &&
      (cubicSeries.points[12]?.map (·.y)) == some 0 &&
      (parabolaSeries.points[12]?.map (·.y)) == some (-1.0)),
    ("ofExact: n = 0 is the single sample at lo",
      (Series.ofExact "p" cubic lo hi 0).points.size == 1 &&
      ((Series.ofExact "p" cubic lo hi 0).points[0]?.map (·.x)) == some (-1.5)),
    ("ofExact: a single sample draws nothing, a line draws one polyline",
      (drawSeries st l (Series.ofExact "p" cubic lo hi 0) 0).size == 0 &&
      cubicDraw.size == 1),
    ("ofExact: the polyline is the conversion of the exact samples, pixel by pixel",
      allPositioned provedFunction cubicSeries &&
      l.polylines cubicSeries.points == #[pixels provedFunction cubicSeries]),
    ("ofExact: the figure draws the pixels of the samples on its axes (first and last)",
      (pixels provedFunction cubicSeries).size == 25 &&
      (match (pixels provedFunction cubicSeries)[0]?, (pixels provedFunction cubicSeries)[24]? with
       | some a, some b => a.x < b.x && a.x ≥ l.area.x0 - 0.5 && b.x ≤ l.area.x1 + 0.5
       | _, _ => false)),
    ("data: the integer list is converted point for point",
      dataLine.points.size == residues.length &&
      (dataLine.points.toList.zip residues).all fun (p, (a, b)) =>
        p.x == Float.ofInt a && p.y == Float.ofInt b),
    ("data: every point has a position; the line is one polyline of all 25 pixels",
      allPositioned provedData dataLine && allPositioned provedData dataDots &&
      (layoutsOf provedData)[0]!.polylines dataLine.points ==
        #[pixels provedData dataLine]),
    ("data: one marker per point",
      (drawSeries provedData.style (layoutsOf provedData)[0]! dataDots 1).size == 25),
    ("data: empty list", (Series.ofIntPoints "e" []).points.size == 0 &&
      (drawSeries st l (Series.ofIntPoints "e" []) 0).size == 0 &&
      (drawSeries st l (Series.scatterOfIntPoints "e" []) 0).size == 0),
    ("data: one point is a marker and no line",
      (drawSeries provedData.style (layoutsOf provedData)[0]! (.ofIntPoints "one" [(3, 4)]) 0).size
        == 0 &&
      (drawSeries provedData.style (layoutsOf provedData)[0]! (.scatterOfIntPoints "one" [(3, 4)])
        0).size == 1),
    ("data: a figure of an empty data series draws",
      ({ panels := #[{ series := #[.ofIntPoints "e" []] }] } : Figure).toSvg.length > 0),
    ("data: negative and large integers",
      (Series.ofIntPoints "x" [(-5, 7), (1000000, -1000000)]).points ==
        #[⟨-5, 7⟩, ⟨1000000, -1000000⟩]),
    ("breaks: a missing position splits the polyline and drops a lone point",
      runs [some 1, some 2, none, some 3, none, some 4, some 5, some 6] [] ==
        [[1, 2], [4, 5, 6]]),
    ("graph: the relation on three nodes with nothing related has no edges",
      rel.nodes.size == 3 && rel.edges.size == 0 &&
      (rel.layout {} {}).edges.size == 0 && (rel.layout {} {}).nodes.size == 3),
    ("graph: the empty list of nodes", (Graph.ofRelation ([] : List Nat) (fun _ _ => true)
      toString).nodes.size == 0 &&
      (Graph.relationPairs ([] : List Nat) (fun _ _ => true)) == []),
    ("graph: a reflexive relation is the self-loops",
      Graph.relationPairs [1, 2] (fun a b => a == b) == [(0, 0), (1, 1)] &&
      (refl.layout {} {}).edges.size == 2),
    ("graph: the 2-cycle keeps both directions",
      Graph.relationPairs [1, 2] (fun a b => a != b) == [(0, 1), (1, 0)] &&
      (cyc.layout {} {}).edges.toList.map (fun e => (e.index, e.src, e.dst)) ==
        [(0, 0, 1), (1, 1, 0)]),
    ("graph: duplicate nodes are different nodes",
      Graph.relationPairs [1, 1] (fun a b => a == b) == [(0, 0), (0, 1), (1, 0), (1, 1)]),
    ("graph: divisibility has 23 edges and each is one route, in order",
      (Graph.relationPairs numbers properDivisor).length == 23 &&
      (provedGraph.layout {} {}).edges.toList.map (fun e => (e.src, e.dst)) ==
        Graph.relationPairs numbers properDivisor &&
      (provedGraph.layout {} {}).edges.toList.map (·.index) == List.range 23),
    ("graph: labels are the nodes' texts",
      provedGraph.nodes.toList.map (·.label) == (List.range 12).map (fun i => toString (i + 1))),
    ("graph: ofNames edges are the pairs and are all routed",
      ((Graph.ofNames #["a", "b", "c"] [(0, 1), (1, 2), (0, 2)]).layout {} {}).edges.toList.map
        (fun e => (e.index, e.src, e.dst)) == [(0, 0, 1), (1, 1, 2), (2, 0, 2)]),
    ("animation: ten frames at the times 0, 1/10, …, 9/10",
      provedClock.frameSeq.frames.size == 10 && provedClock.frameCount == 10 &&
      provedClock.time 3 == 0.3 && provedClock.time 0 == 0 &&
      (provedClock.exactTime 3).num == 3 && (provedClock.exactTime 3).den == 10),
    ("animation: a frame rate of zero counts as one",
      (noFps.exactTime 5).den == 1 && noFps.time 5 == 5),
    ("animation: the frames are the drawings at those times",
      (provedClock.frameSeq.frames[3]?.map (·.data)) ==
        some ((clockFrame (provedClock.time 3)).toImage 200 200 Style.light.text
          ⟨255, 255, 255, 255⟩).data)]

end PILeanTest.ExactChecks
