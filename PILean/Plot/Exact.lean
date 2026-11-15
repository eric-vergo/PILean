/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Exact
import PILean.Plot.Figure

/-!
# Plots with an exact specification

Two kinds of series whose plotted points are specified exactly, before any floating-point number
exists:

* **Function plots.** `Series.ofExact label f lo hi n` plots an exact function `f : Rat → Rat` on
  the grid of `n + 1` points `lo + k (hi - lo) / n` (`Exact.grid`). The exact samples are
  `Exact.samples f lo hi n`.
* **Data plots.** `Series.ofSamples` plots a list of exact points, `Series.ofIntPoints` a list of
  integer pairs; the list is plotted point for point.

Floating point begins at `Exact.toFloat`: `Exact.toPoint` converts one exact sample to a data
point, and the series holds exactly the converted samples, in order (`ofExact_points`,
`ofSamples_points`). What the drawing code does with them is stated by
`drawSeries_line_unmarked` and `drawSeries_scatter` (a polyline through the points that have a
position, a marker at each one) and, for the series built here, `ofExact_draw`,
`ofSamples_draw` and `scatterOfSamples_draw`: when every converted sample has a position on the
panel (`PanelLayout.pos`), the picture is one polyline through the pixels of exactly the samples
(or one marker at each), in order.

## What is proved and what is tested

* Proved: the samples are the grid with the values of `f`; the series' points are the samples
  converted one by one; the drawing, given positions, is the polyline (the markers) through the
  positions of exactly those points. The theorem `PILean.Plot.runs_map_some` and its companions
  are about the function that breaks a polyline (`polylinesWith`), which `PanelLayout.polylines`
  calls.
* Tested, not proved: the position function itself (`PanelLayout.toPx`, floating-point scales,
  clamping), the rasteriser, and how near `Exact.toFloat` is to the rational number (the correctly
  rounded quotient when numerator and denominator have at most 53 significant bits, as in the
  tests, if the platform's conversions and division round as IEEE 754 says).
* `Series.function`, the adaptive sampler for `Float → Float`, is unchanged: its guarantee is
  weaker (it is tested for refinement, poles and jumps, not proved).

Axioms of every theorem: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace PILean

open Canvas

namespace Exact

/-- An exact sample as a data point: where floating point begins. -/
def toPoint (p : Rat × Rat) : Point := ⟨toFloat p.1, toFloat p.2⟩

/-- An integer pair as an exact point. -/
def ofIntPair (p : Int × Int) : Rat × Rat := (p.1, p.2)

end Exact

namespace Plot

/-! ### Breaking polylines -/

/-- Runs of a list of `some` values, with nothing before them: all the values in one run (of
length at least two). -/
theorem runs_map_some {α : Type} (xs cur : List α) :
    runs (xs.map some) cur =
      if 1 < cur.length + xs.length then [cur.reverse ++ xs] else [] := by
  induction xs generalizing cur with
  | nil => simp [runs]
  | cons x xs ih =>
    rw [List.map_cons, runs, ih]
    have e1 : (x :: cur).reverse ++ xs = cur.reverse ++ x :: xs := by simp
    have e2 : (x :: cur).length + xs.length = cur.length + (x :: xs).length := by
      simp only [List.length_cons]; omega
    rw [e1, e2]

/-- Every run has at least two values. -/
theorem runs_length {α : Type} (xs : List (Option α)) (cur : List α) :
    ∀ r ∈ runs xs cur, 1 < r.length := by
  induction xs generalizing cur with
  | nil =>
    intro r hr
    simp only [runs] at hr
    split at hr <;> simp_all
  | cons x xs ih =>
    cases x with
    | none =>
      intro r hr
      simp only [runs, List.mem_append] at hr
      rcases hr with hr | hr
      · split at hr <;> simp_all
      · exact ih [] r hr
    | some a => exact ih (a :: cur)

/-- The values in the runs are some of the values of the list, in order; a value is lost only
if it is alone between two missing ones (or at an end). -/
theorem runs_sublist {α : Type} (xs : List (Option α)) (cur : List α) :
    (runs xs cur).flatten.Sublist (cur.reverse ++ xs.reduceOption) := by
  induction xs generalizing cur with
  | nil => unfold runs; split <;> simp
  | cons x xs ih =>
    cases x with
    | none =>
      simp only [runs, List.flatten_append]
      refine List.Sublist.append ?_ (by simpa [List.reduceOption] using ih [])
      split <;> simp
    | some a =>
      simpa [runs, List.reduceOption] using ih (a :: cur)

/-- When every point has a position, the points are one polyline (none when there is only one
point or none). -/
theorem polylinesWith_all (pos : Point → Option Point) (ps : Array Point)
    (h : ∀ p ∈ ps, (pos p).isSome) :
    polylinesWith pos ps =
      if 1 < ps.size then #[ps.map fun p => (pos p).getD ⟨0, 0⟩] else #[] := by
  have hm : ps.toList.map pos = (ps.toList.map fun p => (pos p).getD ⟨0, 0⟩).map some := by
    rw [List.map_map]
    refine List.map_congr_left fun p hp => ?_
    have := h p (Array.mem_toList_iff.1 hp)
    cases hpp : pos p with
    | none => simp [hpp] at this
    | some q => simp [hpp]
  unfold polylinesWith
  rw [hm, runs_map_some]
  by_cases hs : 1 < ps.size
  · have : 1 < ([] : List Point).length + (ps.toList.map fun p => (pos p).getD ⟨0, 0⟩).length := by
      simpa using hs
    have ha : (ps.toList.map fun p => (pos p).getD ⟨0, 0⟩).toArray =
        ps.map fun p => (pos p).getD ⟨0, 0⟩ := by
      apply Array.ext'; simp
    simp [hs, ha]
  · have : ¬ 1 < ([] : List Point).length +
        (ps.toList.map fun p => (pos p).getD ⟨0, 0⟩).length := by simpa using hs
    simp [hs]

/-- The hypotheses of `polylinesWith_all` can be met: every point has a position (here, itself),
and three points make one polyline. -/
example : polylinesWith some #[⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩] = #[#[⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩]] := by
  rw [polylinesWith_all _ _ (by decide)]
  simp

/-- The same on plain values: three present values and a gap make one run of three and drop the
lone value after the gap. -/
example : runs [some 1, some 2, some 3, none, some 4] [] = [[1, 2, 3]] := by decide

/-! ### What the drawing code does with a line and with scatter points -/

/-- A line series without markers is drawn as the polylines of `PanelLayout.polylines`, each as
a path with no fill and one line style. -/
theorem drawSeries_line_unmarked (st : Style) (l : PanelLayout) (label : String)
    (ps : Array Point) (c : Option Rgba) (dash : Array Float) (index : Nat) :
    ∃ ln : Line, drawSeries st l (.line label ps c false dash) index =
      (l.polylines ps).map fun pl => Shape.path (Path.polyline pl) none (some ln) := by
  exact ⟨dataLine st (c.getD (st.seriesColor index).1)
    (if !dash.isEmpty then dash else if (st.seriesColor index).2 then #[6, 4] else #[]),
    by simp [drawSeries]⟩

/-- A scatter series is drawn as one marker at the position of each point that has one. -/
theorem drawSeries_scatter (st : Style) (l : PanelLayout) (label : String)
    (ps : Array Point) (c : Option Rgba) (r : Option Float) (index : Nat) :
    ∃ (col : Rgba) (rad : Float), drawSeries st l (.scatter label ps c r) index =
      ps.filterMap fun p => (l.pos p).map fun q => marker st q col rad := by
  exact ⟨c.getD (st.seriesColor index).1, r.getD (st.markerRadius + 0.5), by simp [drawSeries]⟩

/-- When every point has a position, a scatter series is one marker at each, in order. -/
theorem drawSeries_scatter_all (st : Style) (l : PanelLayout) (label : String)
    (ps : Array Point) (c : Option Rgba) (r : Option Float) (index : Nat)
    (h : ∀ p ∈ ps, (l.pos p).isSome) :
    ∃ (col : Rgba) (rad : Float), drawSeries st l (.scatter label ps c r) index =
      ps.map fun p => marker st ((l.pos p).getD ⟨0, 0⟩) col rad := by
  obtain ⟨col, rad, e⟩ := drawSeries_scatter st l label ps c r index
  refine ⟨col, rad, e.trans ?_⟩
  apply Array.ext'
  rw [Array.toList_filterMap, Array.toList_map]
  have key : ∀ L : List Point, (∀ p ∈ L, (l.pos p).isSome) →
      L.filterMap (fun p => (l.pos p).map fun q => marker st q col rad) =
        L.map fun p => marker st ((l.pos p).getD ⟨0, 0⟩) col rad := by
    intro L
    induction L with
    | nil => intro _; rfl
    | cons p L ih =>
      intro hL
      have hp := hL p (List.mem_cons_self ..)
      have hrest := ih fun q hq => hL q (List.mem_cons_of_mem _ hq)
      cases hpp : l.pos p with
      | none => simp [hpp] at hp
      | some q => simp [hpp, hrest]
  exact key _ fun p hp => h p (Array.mem_toList_iff.1 hp)

/-! ### Series built from exact values -/

namespace Series

/-- A line through exact points, in order: the series holds the points converted one by one
(`Exact.toPoint`), without markers. -/
def ofSamples (label : String) (ps : List (Rat × Rat)) (color : Option Rgba := none)
    (dash : Array Float := #[]) : Series :=
  .line label (ps.map Exact.toPoint).toArray color false dash

/-- Exact points as markers, in order. -/
def scatterOfSamples (label : String) (ps : List (Rat × Rat)) (color : Option Rgba := none)
    (radius : Option Float := none) : Series :=
  .scatter label (ps.map Exact.toPoint).toArray color radius

/-- The graph of the exact function `f` on the grid of `n + 1` points `lo + k (hi - lo) / n`, as
a line through the exact samples `Exact.samples f lo hi n`. -/
def ofExact (label : String) (f : Rat → Rat) (lo hi : Rat) (n : Nat)
    (color : Option Rgba := none) (dash : Array Float := #[]) : Series :=
  ofSamples label (Exact.samples f lo hi n) color dash

/-- A line through integer data points, in order, without markers. -/
def ofIntPoints (label : String) (ps : List (Int × Int)) (color : Option Rgba := none)
    (dash : Array Float := #[]) : Series :=
  ofSamples label (ps.map Exact.ofIntPair) color dash

/-- Integer data points as markers, in order. -/
def scatterOfIntPoints (label : String) (ps : List (Int × Int)) (color : Option Rgba := none)
    (radius : Option Float := none) : Series :=
  scatterOfSamples label (ps.map Exact.ofIntPair) color radius

/-- The points of a line through exact points are the points converted one by one, in order. -/
theorem ofSamples_points (label : String) (ps : List (Rat × Rat)) (c : Option Rgba)
    (d : Array Float) : (ofSamples label ps c d).points = (ps.map Exact.toPoint).toArray := rfl

/-- The points of a scatter series of exact points are the points converted one by one, in
order. -/
theorem scatterOfSamples_points (label : String) (ps : List (Rat × Rat)) (c : Option Rgba)
    (r : Option Float) : (scatterOfSamples label ps c r).points = (ps.map Exact.toPoint).toArray :=
  rfl

/-- Every point of an exact function series is a converted exact sample `(x, f x)` with `x` on
the grid, and only those, in order. -/
theorem ofExact_points (label : String) (f : Rat → Rat) (lo hi : Rat) (n : Nat) (c : Option Rgba)
    (d : Array Float) :
    (ofExact label f lo hi n c d).points =
      ((Exact.samples f lo hi n).map Exact.toPoint).toArray := rfl

/-- The abscissae of an exact function series are the grid converted, in order: `n + 1` of them,
from `lo` to `hi` in equal steps (see `Exact.gridPoint_eq`). -/
theorem ofExact_xs (label : String) (f : Rat → Rat) (lo hi : Rat) (n : Nat) (c : Option Rgba)
    (d : Array Float) :
    (ofExact label f lo hi n c d).points.toList.map (·.x) =
      (Exact.grid lo hi n).map Exact.toFloat := by
  simp [ofExact, ofSamples, Series.points, Exact.samples, Function.comp_def, Exact.toPoint]

/-- The ordinates of an exact function series are the values of `f` on the grid, converted. -/
theorem ofExact_ys (label : String) (f : Rat → Rat) (lo hi : Rat) (n : Nat) (c : Option Rgba)
    (d : Array Float) :
    (ofExact label f lo hi n c d).points.toList.map (·.y) =
      (Exact.grid lo hi n).map fun x => Exact.toFloat (f x) := by
  simp [ofExact, ofSamples, Series.points, Exact.samples, Function.comp_def, Exact.toPoint]

/-- An exact function series has `n + 1` points. -/
theorem ofExact_size (label : String) (f : Rat → Rat) (lo hi : Rat) (n : Nat) (c : Option Rgba)
    (d : Array Float) : (ofExact label f lo hi n c d).points.size = n + 1 := by
  simp [ofExact, ofSamples, Series.points, Exact.samples, Exact.grid_length]

/-- The drawing of a line through exact points. If every converted point has a position on the
panel, the picture is one polyline through the positions of exactly those points, in order (none
for fewer than two points), drawn in one line style. -/
theorem ofSamples_draw (st : Style) (l : PanelLayout) (label : String) (ps : List (Rat × Rat))
    (c : Option Rgba) (d : Array Float) (index : Nat)
    (h : ∀ p ∈ ps, (l.pos (Exact.toPoint p)).isSome) :
    ∃ ln : Line, drawSeries st l (ofSamples label ps c d) index =
      if 1 < ps.length then
        #[Shape.path (Path.polyline
          (ps.map fun p => (l.pos (Exact.toPoint p)).getD ⟨0, 0⟩).toArray) none (some ln)]
      else #[] := by
  obtain ⟨ln, e⟩ := drawSeries_line_unmarked st l label (ps.map Exact.toPoint).toArray c d index
  refine ⟨ln, ?_⟩
  show drawSeries st l (.line label (ps.map Exact.toPoint).toArray c false d) index = _
  rw [e, PanelLayout.polylines, polylinesWith_all]
  · by_cases hs : 1 < ps.length
    · simp [hs, Function.comp_def]
    · simp [hs]
  · intro p hp
    simp only [List.mem_toArray, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact h q hq

/-- The drawing of an exact function series: when every converted sample has a position, one
polyline through the positions of exactly the exact samples, in order (a single point, `n = 0`,
draws nothing). -/
theorem ofExact_draw (st : Style) (l : PanelLayout) (label : String) (f : Rat → Rat)
    (lo hi : Rat) (n : Nat) (c : Option Rgba) (d : Array Float) (index : Nat)
    (h : ∀ p ∈ Exact.samples f lo hi n, (l.pos (Exact.toPoint p)).isSome) :
    ∃ ln : Line, drawSeries st l (ofExact label f lo hi n c d) index =
      if 0 < n then
        #[Shape.path (Path.polyline
          ((Exact.samples f lo hi n).map fun p => (l.pos (Exact.toPoint p)).getD ⟨0, 0⟩).toArray)
          none (some ln)]
      else #[] := by
  obtain ⟨ln, e⟩ := ofSamples_draw st l label (Exact.samples f lo hi n) c d index h
  refine ⟨ln, e.trans ?_⟩
  simp only [Exact.samples_length]
  by_cases hn : 0 < n
  · simp [hn, show 1 < n + 1 by omega]
  · simp [hn, show ¬ 1 < n + 1 by omega]

/-- The drawing of a scatter series of exact points: when every converted point has a position,
one marker at the position of each, in order. -/
theorem scatterOfSamples_draw (st : Style) (l : PanelLayout) (label : String)
    (ps : List (Rat × Rat)) (c : Option Rgba) (r : Option Float) (index : Nat)
    (h : ∀ p ∈ ps, (l.pos (Exact.toPoint p)).isSome) :
    ∃ (col : Rgba) (rad : Float), drawSeries st l (scatterOfSamples label ps c r) index =
      (ps.map fun p => marker st ((l.pos (Exact.toPoint p)).getD ⟨0, 0⟩) col rad).toArray := by
  obtain ⟨col, rad, e⟩ := drawSeries_scatter_all st l label (ps.map Exact.toPoint).toArray c r index
    (by
      intro p hp
      simp only [List.mem_toArray, List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact h q hq)
  refine ⟨col, rad, e.trans ?_⟩
  simp [List.map_toArray, Function.comp_def]

/-- The integer points are recovered from the exact points: nothing is added, dropped or
reordered by the exact layer. -/
theorem ofIntPairs_recover (ps : List (Int × Int)) :
    (ps.map Exact.ofIntPair).map (fun q => (q.1.num, q.2.num)) = ps := by
  simp [Exact.ofIntPair, Function.comp_def]

/-- The points of a line through integer data are the data converted one by one, in order: as
many as given, none added or dropped. -/
theorem ofIntPoints_points (label : String) (ps : List (Int × Int)) (c : Option Rgba)
    (d : Array Float) :
    (ofIntPoints label ps c d).points =
      (ps.map fun p => Exact.toPoint (Exact.ofIntPair p)).toArray := by
  simp [ofIntPoints, ofSamples, Series.points, Function.comp_def]

/-- The points of a scatter series of integer data are the data converted one by one, in
order. -/
theorem scatterOfIntPoints_points (label : String) (ps : List (Int × Int)) (c : Option Rgba)
    (r : Option Float) :
    (scatterOfIntPoints label ps c r).points =
      (ps.map fun p => Exact.toPoint (Exact.ofIntPair p)).toArray := by
  simp [scatterOfIntPoints, scatterOfSamples, Series.points, Function.comp_def]

/-- The hypotheses can be met: a function of three samples (`n = 2`), and the grid it uses. -/
example : Exact.samples (fun x => x * x) 0 2 2 = [(0, 0), (1, 1), (2, 4)] := by decide +kernel

end Series

end Plot

end PILean
