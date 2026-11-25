/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Anim.Timeline

/-!
# Theorems about timelines

A timeline built from `n` steps (`Timeline.build`) has `n + 1` key frames, and:

* `build_kinds_cut`, `build_kinds_crossfade`: its segments are, in order, the rest on key `0`, then
  for each step `i` the move of step `i` and the rest on key `i + 1`, with the fade in first and
  the fade out last under a crossfade; so there are `2 (n + 1) - 1` segments under a cut and
  `2 (n + 1) + 1` under a crossfade (`build_size_cut`, `build_size_crossfade`).
* `build_segment_spec`, `build_move_spec`, `build_rest_spec`, `build_seam_spec`: the move of step
  `j` lasts as long as step `j` and has its easing; the rest on key `0` lasts `firstHold`, the rest
  on the last key `lastHold`, any other rest `hold`; the fades, which exist only under a crossfade
  `d`, last `d / 2` each; rests and fades are not eased (a negative duration counting as zero).
* `build_start_zero`, `build_start_succ`, `build_stop_last`, `build_dur_nonneg`: the segments tile
  the cycle: the first starts at `0`, each starts where the one before it ends, the last ends at
  the end of the cycle, and none has a negative duration.
* `keyTimes_size`, `keyTimes_zero`, `keyTimes_last`, `keyTimes_mono`: the boundaries as
  fractions of the cycle are one more than the segments, start at `0`, end at `1` (when the cycle
  is longer than zero, `build_cycle_pos`) and never decrease.
* `wrap_mem`, `segmentAt_mem`, `progress_mem`: any time, brought into the cycle, lies in the
  segment `segmentAt` names, and the progress through that segment is in `[0, 1)`.

All of these are equalities and inequalities of rational numbers. For one key frame (no steps) the
timeline is the rest on key `0` (with the fade in and out under a crossfade): one segment under a
cut, three under a crossfade, and its cycle is longer than zero when `firstHold` is. Zero key
frames cannot be asked for: `build` always has key `0`. A cycle of length zero (every duration
zero) is allowed: then every key time is `0`, and the statements that need a cycle longer than
zero say so.

Not proved: anything about `Easing.eval` (floating point; tested against known values).
-/

namespace PILean.Anim

namespace Timeline

/-! ### Laying pieces end to end -/

private theorem max_nonneg (d : Rat) : 0 ≤ max d 0 := by grind

/-- The pieces laid end to end give one segment each. -/
theorem length_layout (s : Rat) (l : List Piece) : (layout s l).length = l.length := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => simp [layout, ih]

/-- The total duration of pieces is not negative. -/
theorem total_nonneg (l : List Piece) : 0 ≤ total l := by
  induction l with
  | nil => exact Rat.le_refl
  | cons a l ih =>
    obtain ⟨k, d, e⟩ := a
    simp only [total]
    have : 0 ≤ max d 0 := max_nonneg _
    grind

/-- The first segment of pieces laid end to end from `s` starts at `s`. -/
theorem layout_getElem_zero_start (s : Rat) (l : List Piece) (h : 0 < (layout s l).length) :
    (layout s l)[0].start = s := by
  match l, h with
  | (k, d, e) :: l, _ => rfl

/-- Each segment of pieces laid end to end starts where the one before it ends. -/
theorem layout_getElem_succ_start (s : Rat) (l : List Piece) (i : Nat)
    (h : i + 1 < (layout s l).length) :
    (layout s l)[i + 1].start = (layout s l)[i].stop := by
  induction l generalizing s i with
  | nil => simp [layout] at h
  | cons a l ih =>
    obtain ⟨k, d, e⟩ := a
    cases i with
    | zero =>
      simp only [layout, List.getElem_cons_succ, List.getElem_cons_zero, Segment.stop]
      exact layout_getElem_zero_start _ _ _
    | succ i =>
      simp only [layout, List.getElem_cons_succ]
      exact ih _ _ (by simpa [layout] using h)

/-- No segment of pieces laid end to end has a negative duration. -/
theorem layout_getElem_dur_nonneg (s : Rat) (l : List Piece) (i : Nat)
    (h : i < (layout s l).length) : 0 ≤ (layout s l)[i].dur := by
  induction l generalizing s i with
  | nil => simp [layout] at h
  | cons a l ih =>
    obtain ⟨k, d, e⟩ := a
    cases i with
    | zero => exact max_nonneg _
    | succ i =>
      simp only [layout, List.getElem_cons_succ]
      exact ih _ _ (by simpa [layout] using h)

/-- Segment `i` of pieces laid end to end from `s` ends at `s` plus the total duration of the
first `i + 1` pieces. -/
theorem layout_getElem_stop (s : Rat) (l : List Piece) (i : Nat)
    (h : i < (layout s l).length) : (layout s l)[i].stop = s + total (l.take (i + 1)) := by
  induction l generalizing s i with
  | nil => simp [layout] at h
  | cons a l ih =>
    obtain ⟨k, d, e⟩ := a
    cases i with
    | zero => simp [layout, total, Segment.stop]; grind
    | succ i =>
      simp only [layout, List.getElem_cons_succ, List.take_succ_cons, total]
      rw [ih _ _ (by simpa [layout] using h)]
      grind

/-- The last segment of pieces laid end to end from `s` ends at `s` plus their total duration. -/
theorem layout_last_stop (s : Rat) (l : List Piece) (h : 0 < (layout s l).length) :
    (layout s l)[(layout s l).length - 1].stop = s + total l := by
  rw [layout_getElem_stop]
  rw [List.take_of_length_le (by simp [length_layout]; omega)]

/-- A time `u` from `s` to the end of the pieces laid end to end from `s` lies in the segment
`findSeg` finds: from its start (inclusive) to its end (exclusive). -/
theorem findSeg_layout (s u : Rat) (l : List Piece) (h₁ : s ≤ u) (h₂ : u < s + total l) :
    ∃ h : findSeg u (layout s l) < (layout s l).length,
      (layout s l)[findSeg u (layout s l)].start ≤ u ∧
        u < (layout s l)[findSeg u (layout s l)].stop := by
  induction l generalizing s with
  | nil => simp [total] at h₂; grind
  | cons a l ih =>
    obtain ⟨k, d, e⟩ := a
    by_cases hu : u < s + max d 0
    · refine ⟨by simp [layout, findSeg, Segment.stop, hu], ?_⟩
      simp [layout, findSeg, Segment.stop, hu, h₁]
    · have h₁' : s + max d 0 ≤ u := by grind
      have h₂' : u < s + max d 0 + total l := by simp only [total] at h₂; grind
      obtain ⟨hlt, hs, hstop⟩ := ih (s + max d 0) h₁' h₂'
      have hf : findSeg u (layout s ((k, d, e) :: l)) = findSeg u (layout (s + max d 0) l) + 1 := by
        simp [layout, findSeg, Segment.stop, hu]
      refine ⟨by simp only [hf]; simp [layout]; exact hlt, ?_⟩
      simp only [hf]
      simp only [layout, List.getElem_cons_succ]
      exact ⟨hs, hstop⟩

/-! ### The kinds of the segments -/

/-- The steps give two segments each: the move and the rest after it. -/
theorem length_flatMap_steps (n : Nat) :
    ((List.range n).flatMap fun j => [SegKind.move j, .rest (j + 1)]).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, List.flatMap_append, ih]; omega

/-- Laying pieces end to end keeps their kinds. -/
theorem kinds_layout (s : Rat) (l : List Piece) :
    (layout s l).map (·.kind) = l.map (·.1) := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => obtain ⟨k, d, e⟩ := a; simp [layout, ih]

/-- Segment `i` of pieces laid end to end has the kind, the duration (at least zero) and the
easing of piece `i`. -/
theorem layout_getElem (s : Rat) (l : List Piece) (i : Nat) (h : i < (layout s l).length) :
    (layout s l)[i].kind = (l[i]'(by simpa [length_layout] using h)).1 ∧
      (layout s l)[i].dur = max (l[i]'(by simpa [length_layout] using h)).2.1 0 ∧
      (layout s l)[i].easing = (l[i]'(by simpa [length_layout] using h)).2.2 := by
  induction l generalizing s i with
  | nil => simp [layout] at h
  | cons a l ih =>
    obtain ⟨k, d, e⟩ := a
    cases i with
    | zero => simp [layout]
    | succ i =>
      simp only [layout, List.getElem_cons_succ]
      exact ih _ _ (by simpa [layout] using h)

/-- A piece with a duration adds at least that duration (counted as at least zero) to the total. -/
theorem le_total_of_mem {x : Piece} {l : List Piece} (h : x ∈ l) : max x.2.1 0 ≤ total l := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    obtain ⟨k, d, e⟩ := a
    have := total_nonneg l
    have := max_nonneg d
    simp only [total]
    rcases List.mem_cons.mp h with h | h
    · subst h; grind
    · have := ih h; grind

variable (steps : Array Step) (p : Pacing)

/-- A timeline of `n` steps has `n + 1` key frames. -/
theorem build_keys : (build steps p).keys = steps.size + 1 := rfl

/-- The cycle is the total duration of the pieces. -/
theorem build_cycle : (build steps p).cycle = total (pieces steps p) := rfl

/-- The segments are the pieces laid end to end from `0`. -/
theorem build_segments : (build steps p).segments.toList = layout 0 (pieces steps p) := by
  simp [build]

/-- The kinds of the segments are `kinds`. -/
theorem build_kinds : (build steps p).segments.toList.map (·.kind) = kinds steps p := by
  rw [build_segments, kinds_layout, pieces, List.map_map]
  exact List.map_id _

/-- Under a cut, the segments are the rest on key `0`, then for each step `i` the move of step `i`
and the rest on key `i + 1`. -/
theorem build_kinds_cut (h : p.seam = .cut) :
    (build steps p).segments.toList.map (·.kind) =
      .rest 0 :: (List.range steps.size).flatMap fun j => [.move j, .rest (j + 1)] := by
  rw [build_kinds, kinds, h]

/-- Under a crossfade, the segments are the fade in, the rest on key `0`, then for each step `i`
the move of step `i` and the rest on key `i + 1`, and the fade out. -/
theorem build_kinds_crossfade (d : Rat) (h : p.seam = .crossfade d) :
    (build steps p).segments.toList.map (·.kind) =
      .seamIn :: .rest 0 :: ((List.range steps.size).flatMap fun j => [.move j, .rest (j + 1)]) ++
        [.seamOut] := by
  rw [build_kinds, kinds, h]

/-- There is one segment for each piece. -/
theorem build_size_eq : (build steps p).segments.size = (kinds steps p).length := by
  simp [build, length_layout, pieces]

/-- Under a cut, a timeline of `n` key frames has `2 n - 1` segments. -/
theorem build_size_cut (h : p.seam = .cut) :
    (build steps p).segments.size = 2 * (build steps p).keys - 1 := by
  rw [build_size_eq, build_keys, kinds, h]
  simp only [List.length_cons, length_flatMap_steps]
  omega

/-- Under a crossfade, a timeline of `n` key frames has `2 n + 1` segments. -/
theorem build_size_crossfade (d : Rat) (h : p.seam = .crossfade d) :
    (build steps p).segments.size = 2 * (build steps p).keys + 1 := by
  rw [build_size_eq, build_keys, kinds, h]
  simp only [List.length_cons, List.length_append, length_flatMap_steps, List.length_nil]
  omega

/-- A timeline has at least one segment (the rest on key `0`). -/
theorem build_size_pos : 0 < (build steps p).segments.size := by
  rw [build_size_eq, kinds]
  split <;> simp

/-! ### Durations and easings -/

/-- Every segment has the duration (at least zero) and the easing `spec` gives its kind. -/
theorem build_segment_spec (i : Nat) (h : i < (build steps p).segments.size) :
    (build steps p).segments[i].dur = max (spec steps p (build steps p).segments[i].kind).1 0 ∧
      (build steps p).segments[i].easing = (spec steps p (build steps p).segments[i].kind).2 := by
  obtain ⟨hk, hd, he⟩ := layout_getElem 0 (pieces steps p) i (by simpa [build] using h)
  simp only [build, List.getElem_toArray]
  rw [hd, he, hk]
  simp [pieces]

/-- The kind of every segment is one of `kinds`. -/
theorem build_kind_mem (i : Nat) (h : i < (build steps p).segments.size) :
    (build steps p).segments[i].kind ∈ kinds steps p := by
  rw [← build_kinds]
  exact List.mem_map.mpr ⟨_, List.getElem_mem (by simpa using h), rfl⟩

/-- The move of step `j` lasts as long as step `j` (at least zero) and has its easing. -/
theorem build_move_spec (i j : Nat) (h : i < (build steps p).segments.size)
    (hk : (build steps p).segments[i].kind = .move j) :
    ∃ hj : j < steps.size, (build steps p).segments[i].dur = max steps[j].dur 0 ∧
      (build steps p).segments[i].easing = steps[j].easing := by
  have hm := build_kind_mem steps p i h
  rw [hk] at hm
  have hj : j < steps.size := by
    simp only [kinds] at hm
    split at hm <;> simp at hm <;> omega
  obtain ⟨hd, he⟩ := build_segment_spec steps p i h
  refine ⟨hj, ?_, ?_⟩ <;> simp [hd, he, hk, spec, hj]

/-- The rest on key `k` lasts `firstHold` for `k = 0`, `lastHold` for the last key and `hold`
otherwise (at least zero), and is not eased. -/
theorem build_rest_spec (i k : Nat) (h : i < (build steps p).segments.size)
    (hk : (build steps p).segments[i].kind = .rest k) :
    (build steps p).segments[i].dur =
        max (if k = 0 then p.firstHold else if k = steps.size then p.lastHold else p.hold) 0 ∧
      (build steps p).segments[i].easing = .linear := by
  obtain ⟨hd, he⟩ := build_segment_spec steps p i h
  simp [hd, he, hk, spec]

/-- The fades exist only under a crossfade `d`; each lasts `d / 2` (at least zero) and is not
eased. -/
theorem build_seam_spec (i : Nat) (h : i < (build steps p).segments.size)
    (hk : (build steps p).segments[i].kind = .seamIn ∨
      (build steps p).segments[i].kind = .seamOut) :
    ∃ d, p.seam = .crossfade d ∧ (build steps p).segments[i].dur = max (d / 2) 0 ∧
      (build steps p).segments[i].easing = .linear := by
  have hm := build_kind_mem steps p i h
  obtain ⟨hd, he⟩ := build_segment_spec steps p i h
  match hs : p.seam, hk with
  | .cut, hk =>
    simp only [kinds, hs] at hm
    rcases hk with hk | hk <;> rw [hk] at hm <;> simp at hm
  | .crossfade d, hk =>
    refine ⟨d, rfl, ?_, ?_⟩ <;>
      rcases hk with hk | hk <;> simp [hd, he, hk, spec, Pacing.seamHalf, hs]

/-! ### The segments tile the cycle -/

/-- The first segment starts at `0`. -/
theorem build_start_zero :
    ((build steps p).segments[0]'(build_size_pos steps p)).start = 0 := by
  have h := build_size_pos steps p
  simp only [build, List.getElem_toArray]
  exact layout_getElem_zero_start _ _ _

/-- Each segment starts where the one before it ends. -/
theorem build_start_succ (i : Nat) (h : i + 1 < (build steps p).segments.size) :
    (build steps p).segments[i + 1].start = (build steps p).segments[i].stop := by
  simp only [build, List.getElem_toArray]
  exact layout_getElem_succ_start _ _ _ _

/-- The last segment ends at the end of the cycle. -/
theorem build_stop_last :
    ((build steps p).segments[(build steps p).segments.size - 1]'
      (Nat.sub_lt (build_size_pos steps p) Nat.one_pos)).stop = (build steps p).cycle := by
  have h := build_size_pos steps p
  simp only [build, List.getElem_toArray, List.size_toArray]
  rw [layout_last_stop _ _ (by simpa [build] using h)]
  exact Rat.zero_add _

/-- No segment has a negative duration. -/
theorem build_dur_nonneg (i : Nat) (h : i < (build steps p).segments.size) :
    0 ≤ (build steps p).segments[i].dur := by
  simp only [build, List.getElem_toArray]
  exact layout_getElem_dur_nonneg _ _ _ _

/-- The cycle is not negative. -/
theorem build_cycle_nonneg : 0 ≤ (build steps p).cycle := total_nonneg _

/-- The cycle is longer than zero when the rest on the first key is. -/
theorem build_cycle_pos (h : 0 < p.firstHold) : 0 < (build steps p).cycle := by
  have hm : (SegKind.rest 0, spec steps p (.rest 0)) ∈ pieces steps p := by
    refine List.mem_map.mpr ⟨.rest 0, ?_, rfl⟩
    simp only [kinds]; split <;> simp
  have := le_total_of_mem hm
  simp only [spec, ite_true] at this
  rw [build_cycle]
  grind

/-! ### Key times -/

/-- There is one more key time than segments. -/
theorem keyTimes_size :
    (build steps p).keyTimes.size = (build steps p).segments.size + 1 := by
  simp [keyTimes, boundaries]

/-- Boundary `i`, for a segment `i`, is where that segment starts. -/
theorem boundaries_getElem_lt (tl : Timeline) (i : Nat) (h : i < tl.segments.size) :
    tl.boundaries[i]'(by simp [boundaries]; omega) = tl.segments[i].start := by
  simp [boundaries, Array.getElem_push, h]

/-- The last boundary is the end of the cycle. -/
theorem boundaries_getElem_size (tl : Timeline) :
    tl.boundaries[tl.segments.size]'(by simp [boundaries]) = tl.cycle := by
  simp [boundaries, Array.getElem_push]

/-- Consecutive boundaries do not decrease: the next boundary is where the segment ends. -/
theorem build_boundaries_succ (i : Nat) (h : i < (build steps p).segments.size) :
    (build steps p).boundaries[i + 1]'(by simp [boundaries]; omega) =
      (build steps p).segments[i].stop := by
  by_cases hi : i + 1 < (build steps p).segments.size
  · rw [boundaries_getElem_lt _ _ hi, build_start_succ]
  · have : i = (build steps p).segments.size - 1 := by omega
    subst this
    have hs : (build steps p).segments.size - 1 + 1 = (build steps p).segments.size := by omega
    simp only [hs, boundaries_getElem_size]
    exact (build_stop_last steps p).symm

/-- Consecutive boundaries do not decrease. -/
theorem build_boundaries_mono_succ (i : Nat) (h : i + 1 < (build steps p).boundaries.size) :
    (build steps p).boundaries[i] ≤ (build steps p).boundaries[i + 1] := by
  have hi : i < (build steps p).segments.size := by simpa [boundaries] using h
  rw [build_boundaries_succ _ _ _ hi, boundaries_getElem_lt _ _ hi]
  have := build_dur_nonneg steps p i hi
  simp only [Segment.stop]
  grind

private theorem div_le_div_of_nonneg {a b c : Rat} (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c := by
  rw [Rat.div_def, Rat.div_def]
  refine Rat.mul_le_mul_of_nonneg_right hab ?_
  rcases (Rat.le_iff_lt_or_eq.mp hc) with hc | hc
  · exact Rat.le_of_lt (Rat.inv_pos.mpr hc)
  · rw [← hc, Rat.inv_zero]; exact Rat.le_refl

/-- The key times start at `0`. -/
theorem keyTimes_zero :
    (build steps p).keyTimes[0]'(by rw [keyTimes_size]; omega) = 0 := by
  have h := build_size_pos steps p
  simp only [keyTimes, Array.getElem_map]
  rw [boundaries_getElem_lt _ _ h, build_start_zero]
  rw [Rat.div_def]
  exact Rat.zero_mul _

/-- The key times end at `1` when the cycle is longer than zero. -/
theorem keyTimes_last (h : 0 < (build steps p).cycle) :
    (build steps p).keyTimes[(build steps p).segments.size]'(by rw [keyTimes_size]; omega) = 1 := by
  simp only [keyTimes, Array.getElem_map, boundaries_getElem_size]
  rw [Rat.div_def]
  exact Rat.mul_inv_cancel _ (Rat.ne_of_gt h)

/-- The key times never decrease. -/
theorem keyTimes_mono (i j : Nat) (hij : i ≤ j) (hj : j < (build steps p).keyTimes.size) :
    (build steps p).keyTimes[i] ≤ (build steps p).keyTimes[j] := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this
    exact Rat.le_refl
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le hij with hij | hij
    · refine Rat.le_trans (ih (by omega) (by omega)) ?_
      simp only [keyTimes, Array.getElem_map]
      exact div_le_div_of_nonneg
        (build_boundaries_mono_succ _ _ _ (by simpa [keyTimes] using hj))
        (build_cycle_nonneg _ _)
    · subst hij; exact Rat.le_refl

/-! ### The segment at a time -/

/-- A time brought into a cycle longer than zero lies in `[0, cycle)`. -/
theorem wrap_mem (tl : Timeline) (h : 0 < tl.cycle) (t : Rat) :
    0 ≤ tl.wrap t ∧ tl.wrap t < tl.cycle := by
  have hn : ¬ tl.cycle ≤ 0 := Rat.not_le.mpr h
  simp only [wrap, hn, ite_false]
  have h₁ := Rat.floor_le (t / tl.cycle)
  have h₂ := Rat.lt_floor_add_one (t / tl.cycle)
  have hm₁ := Rat.mul_le_mul_of_nonneg_left h₁ (Rat.le_of_lt h)
  have hm₂ := (Rat.mul_lt_mul_left h).mpr h₂
  have hc : tl.cycle * (t / tl.cycle) = t := by
    rw [Rat.mul_comm]; exact Rat.div_mul_cancel (Rat.ne_of_gt h)
  rw [hc] at hm₁ hm₂
  push_cast at hm₂
  grind

/-- When the cycle is longer than zero, the time `t` brought into the cycle lies in the segment
`segmentAt t`: from its start (inclusive) to its end (exclusive). -/
theorem segmentAt_mem (h : 0 < (build steps p).cycle) (t : Rat) :
    ∃ hi : (build steps p).segmentAt t < (build steps p).segments.size,
      (build steps p).segments[(build steps p).segmentAt t].start ≤ (build steps p).wrap t ∧
        (build steps p).wrap t < (build steps p).segments[(build steps p).segmentAt t].stop := by
  obtain ⟨h₁, h₂⟩ := wrap_mem _ h t
  have := findSeg_layout 0 ((build steps p).wrap t) (pieces steps p) h₁
    (by rw [Rat.zero_add]; exact h₂)
  simpa [segmentAt, build] using this

/-- When the cycle is longer than zero, the progress through the segment at any time is in
`[0, 1)`. -/
theorem progress_mem (h : 0 < (build steps p).cycle) (t : Rat) :
    0 ≤ (build steps p).progress t ∧ (build steps p).progress t < 1 := by
  obtain ⟨hi, hs, hstop⟩ := segmentAt_mem steps p h t
  simp only [progress, Array.getElem?_eq_getElem hi]
  simp only [Segment.stop] at hstop
  have hd := build_dur_nonneg steps p _ hi
  split
  · rename_i h0; rw [h0] at hstop; grind
  · rename_i h0
    have hpos : 0 < (build steps p).segments[(build steps p).segmentAt t].dur := by grind
    refine ⟨?_, ?_⟩
    · rw [Rat.div_def]
      exact Rat.mul_nonneg (by grind) (Rat.le_of_lt (Rat.inv_pos.mpr hpos))
    · rw [Rat.div_lt_iff hpos]; grind

/-- The segment `locate` reports is the segment `segmentAt` names. -/
theorem locate_fst (h : 0 < (build steps p).cycle) (t : Rat) :
    ∃ hi : (build steps p).segmentAt t < (build steps p).segments.size,
      ((build steps p).locate t).1 =
        (build steps p).segments[(build steps p).segmentAt t].kind := by
  obtain ⟨hi, -⟩ := segmentAt_mem steps p h t
  exact ⟨hi, by simp [locate, Array.getElem?_eq_getElem hi]⟩

/-- The hypotheses can be met: with the default pacing, two turns give a cycle of
`0.2 + 1.2 + 1 + 0.6 + 1 + 1.8 + 0.2 = 6` seconds in seven segments. -/
example : (build #[({} : Pacing).turnStep, ({} : Pacing).turnStep] {}).cycle = 6 ∧
    (build #[({} : Pacing).turnStep, ({} : Pacing).turnStep] {}).segments.size = 7 := by
  decide +kernel

end Timeline

end PILean.Anim
