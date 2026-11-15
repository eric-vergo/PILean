/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Pseudo.Real

/-!
# Polylines in the real plane and their distance to a graph

A plot of a function is a polyline: finitely many points, each joined to the next by a straight
segment. This file says, over the real numbers, what the polyline is as a subset of the plane and
what it means for it to be near the graph of a function.

## Main definitions

* `PILean.polyline ps`: the union of the closed segments joining consecutive points of the list
  `ps`.
* `PILean.IsVerticallyWithin S f s δ`: the set `S` lies over `s`, has a point over every point of
  `s`, and each of its points `(x, y)` satisfies `|y - f x| ≤ δ`.

## Main results

* `PILean.IsVerticallyWithin.hausdorffDist_le`: a set vertically within `δ` of the graph of `f`
  over `s` is within Hausdorff distance `δ` of that graph (for the maximum metric of the plane).

## Implementation notes

The vertical distance is the notion a reader of a plot uses: above the abscissa `x`, how far is
the curve from `f x`? It is stronger than the Hausdorff distance between the two curves as
subsets of the plane. `IsVerticallyWithin.hausdorffDist_le` is one direction. The other fails:
where a graph is steep, the same graph moved sideways by a small amount stays close to it as a
set and is far from it above each abscissa.
-/

open Set

namespace PILean

/-- The polyline through the points of a list: the union of the closed segments joining each
point to the next. It is empty for a list of fewer than two points. -/
def polyline (ps : List (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {z | ∃ (k : ℕ) (h : k + 1 < ps.length), z ∈ segment ℝ ps[k] ps[k + 1]}

/-- A point is on the polyline when it is on the segment joining two consecutive points. -/
theorem mem_polyline_iff {ps : List (ℝ × ℝ)} {z : ℝ × ℝ} :
    z ∈ polyline ps ↔ ∃ (k : ℕ) (h : k + 1 < ps.length), z ∈ segment ℝ ps[k] ps[k + 1] :=
  Iff.rfl

/-- Each point of a list of at least two points lies on its polyline. -/
theorem getElem_mem_polyline {ps : List (ℝ × ℝ)} (hps : 2 ≤ ps.length) {k : ℕ}
    (hk : k < ps.length) : ps[k] ∈ polyline ps := by
  rcases Nat.lt_or_ge (k + 1) ps.length with h | h
  · exact ⟨k, h, left_mem_segment ℝ _ _⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact ⟨j, hk, right_mem_segment ℝ _ _⟩

/-- The set `S` of the plane is *vertically within `δ`* of the graph of `f` over `s`: every
point of `S` has its abscissa in `s`, above every abscissa of `s` there is a point of `S`, and
every point `(x, y)` of `S` has `|y - f x| ≤ δ`. -/
structure IsVerticallyWithin (S : Set (ℝ × ℝ)) (f : ℝ → ℝ) (s : Set ℝ) (δ : ℝ) : Prop where
  /-- Every point of `S` has its abscissa in `s`. -/
  fst_mem : ∀ z ∈ S, z.1 ∈ s
  /-- Above every abscissa of `s` there is a point of `S`. -/
  exists_mem : ∀ x ∈ s, ∃ y, (x, y) ∈ S
  /-- Every point of `S` is within `δ` of the graph of `f`, measured vertically. -/
  abs_sub_le : ∀ z ∈ S, |z.2 - f z.1| ≤ δ

namespace IsVerticallyWithin

variable {S : Set (ℝ × ℝ)} {f : ℝ → ℝ} {s : Set ℝ} {δ δ' : ℝ}

/-- Being vertically within `δ` is monotone in `δ`. -/
theorem mono (h : IsVerticallyWithin S f s δ) (hδ : δ ≤ δ') : IsVerticallyWithin S f s δ' :=
  ⟨h.fst_mem, h.exists_mem, fun z hz => (h.abs_sub_le z hz).trans hδ⟩

/-- Above every abscissa of `s`, every point of `S` there is within `δ` of the value of `f`,
and there is such a point. -/
theorem exists_abs_sub_le (h : IsVerticallyWithin S f s δ) {x : ℝ} (hx : x ∈ s) :
    ∃ y, (x, y) ∈ S ∧ |y - f x| ≤ δ :=
  let ⟨y, hy⟩ := h.exists_mem x hx
  ⟨y, hy, h.abs_sub_le _ hy⟩

/-- A set vertically within `δ` of the graph of `f` over `s` is within Hausdorff distance `δ` of
that graph, for the maximum metric of the plane. The converse does not hold. -/
theorem hausdorffDist_le (h : IsVerticallyWithin S f s δ) (hδ : 0 ≤ δ) :
    Metric.hausdorffDist S (s.graphOn f) ≤ δ := by
  refine Metric.hausdorffDist_le_of_mem_dist hδ (fun z hz => ?_) ?_
  · refine ⟨(z.1, f z.1), mem_image_of_mem _ (h.fst_mem z hz), ?_⟩
    simpa [Prod.dist_eq, Real.dist_eq, hδ] using h.abs_sub_le z hz
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := h.exists_abs_sub_le hx
    refine ⟨(x, y), hy, ?_⟩
    simpa [Prod.dist_eq, Real.dist_eq, hδ, abs_sub_comm] using hxy

end IsVerticallyWithin

/-- The definition can be met: the segment from `(0, 0)` to `(1, 1)` is vertically within `0` of
the graph of the identity over `[0, 1]`. -/
example : IsVerticallyWithin (polyline [(0, 0), (1, 1)]) id (Icc 0 1) 0 := by
  have key : ∀ z ∈ polyline [(0, 0), (1, 1)], z.1 ∈ Icc (0 : ℝ) 1 ∧ z.2 = z.1 := by
    rintro z ⟨k, hk, hz⟩
    obtain rfl : k = 0 := by simpa using hk
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Prod.smul_mk, Prod.mk_add_mk,
      smul_eq_mul, mul_zero, mul_one, zero_add, mem_Icc, and_true]
    exact ⟨hb, by linarith⟩
  refine ⟨fun z hz => (key z hz).1, fun x hx => ⟨x, 0, by simp, 1 - x, x, ?_⟩,
    fun z hz => by simp [(key z hz).2]⟩
  simpa using And.intro hx.2 hx.1

/-- The definition is not empty of content: the same segment is not vertically within `1 / 2` of
the graph of the constant function `1`, since its point `(0, 0)` is at vertical distance `1`. -/
example : ¬ IsVerticallyWithin (polyline [(0, 0), (1, 1)]) (fun _ => 1) (Icc 0 1) (1 / 2) := by
  intro h
  have := h.abs_sub_le (0, 0) (getElem_mem_polyline (ps := [(0, 0), (1, 1)]) le_rfl
    (k := 0) (by simp))
  norm_num at this

end PILean
