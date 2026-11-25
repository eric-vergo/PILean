/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Anim.Smil
import PILean.Anim.TimelineProofs

/-!
# Theorems about the SMIL tracks

What the builders of `PILean/Anim/Smil.lean` write, for a timeline built from any steps and any
pacing (`Timeline.build steps p`, written `B` below) and any options `o`:

* `times_size`, `times_mono`, `times_zero`, `times_last`, `times_mem`, `times_strict`: the key
  times written (`Smil.times`) are one more than the segments and never decrease; when the cycle
  is longer than zero they start at `0`, end at `1`, lie in `[0, 1]`, and with a gap above zero
  each is more than the one before it.
* `keyValues_size`, `seamLevels_size`, `track_counts`: every track the builders make on `B` has as
  many values as key times, and one easing fewer than key times (`keySplines`).
* `track_splines`, `track_splines_move`, `track_splines_still`: the easing of interval `i` is that
  of segment `i`: the step's own for a move, the identity for a rest and for a fade.
* `seamLevels_crossfade`: under a crossfade the motion layer's opacity is `0` at the first and at
  the last boundary.

All of these are about exact rational numbers and arrays, before the conversion to text. Not
proved: that `fmtNum` of the converted times keeps their order (tested), and anything a browser
does.
-/

namespace PILean.Anim

namespace Smil

open Timeline

/-! ### Pushing times apart -/

/-- Pushing up keeps the number of times. -/
theorem length_pushUp (g prev : Rat) (l : List Rat) : (pushUp g prev l).length = l.length := by
  induction l generalizing prev with
  | nil => rfl
  | cons x r ih =>
    cases r with
    | nil => rfl
    | cons y r => simp [pushUp, ih]

/-- Pushing up keeps the last time. -/
theorem getLast?_pushUp (g prev : Rat) (l : List Rat) :
    (pushUp g prev l).getLast? = l.getLast? := by
  induction l generalizing prev with
  | nil => rfl
  | cons x r ih =>
    cases r with
    | nil => rfl
    | cons y r =>
      have hne : pushUp g (max x (prev + g)) (y :: r) ≠ [] := by
        intro h; have := congrArg List.length h; simp [length_pushUp] at this
      obtain ⟨z, w, hz⟩ := List.exists_cons_of_ne_nil hne
      simp only [pushUp, hz, List.getLast?_cons_cons]
      rw [← hz, ih]

/-- Every time pushed up but the last is at least `prev` plus `g` for each time up to it. -/
theorem pushUp_ge (g prev : Rat) (l : List Rat) (k : Nat) (hk : k + 1 < (pushUp g prev l).length) :
    prev + ((k : Rat) + 1) * g ≤ (pushUp g prev l)[k]'(by omega) := by
  induction l generalizing prev k with
  | nil => simp [pushUp] at hk
  | cons x r ih =>
    cases r with
    | nil => simp [pushUp] at hk
    | cons y r =>
      have hu : prev + g ≤ max x (prev + g) := by grind
      cases k with
      | zero => simp only [pushUp, List.getElem_cons_zero]; grind
      | succ k =>
        simp only [pushUp, List.getElem_cons_succ]
        have := ih (max x (prev + g)) k (by simpa [pushUp, length_pushUp] using hk)
        push_cast
        grind

/-- Pulling down keeps the number of times. -/
theorem length_pullDown (g : Rat) (l : List Rat) : (pullDown g l).length = l.length := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    cases h : pullDown g rest with
    | nil => rw [h] at ih; simp at ih; simp [pullDown, h, ih]
    | cons y r => rw [h] at ih; simp [pullDown, h, ← ih]

/-- Pulling down keeps the last time. -/
theorem getLast?_pullDown (g : Rat) (l : List Rat) : (pullDown g l).getLast? = l.getLast? := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    cases h : pullDown g rest with
    | nil =>
      have : rest = [] := by
        have := length_pullDown g rest
        rw [h] at this
        exact List.eq_nil_of_length_eq_zero this.symm
      subst this; rfl
    | cons y r =>
      have hne : rest ≠ [] := by
        intro h'; subst h'; simp [pullDown] at h
      have e : pullDown g (x :: rest) = min x (y - g) :: y :: r := by simp only [pullDown, h]
      rw [e, List.getLast?_cons_cons, ← h, ih]
      obtain ⟨z, rest', rfl⟩ := List.exists_cons_of_ne_nil hne
      rw [List.getLast?_cons_cons]

/-- After pulling down, each time is at least `g` before the next. -/
theorem pullDown_chain (g : Rat) (l : List Rat) (k : Nat) (hk : k + 1 < (pullDown g l).length) :
    (pullDown g l)[k] + g ≤ (pullDown g l)[k + 1] := by
  induction l generalizing k with
  | nil => simp [pullDown] at hk
  | cons x rest ih =>
    cases h : pullDown g rest with
    | nil => simp [pullDown, h] at hk
    | cons y r =>
      have ih' := ih
      simp only [h] at ih'
      simp only [pullDown, h]
      cases k with
      | zero => simp; grind
      | succ k =>
        simp only [List.getElem_cons_succ]
        exact ih' k (by simp [pullDown, h] at hk; simp; omega)

/-- Pulling down keeps a lower bound `a + k g` on the time at `k`. -/
theorem pullDown_ge (g a : Rat) (l : List Rat)
    (hl : ∀ k (hk : k < l.length), a + (k : Rat) * g ≤ l[k]) (k : Nat)
    (hk : k < (pullDown g l).length) : a + (k : Rat) * g ≤ (pullDown g l)[k] := by
  induction l generalizing a k with
  | nil => simp [pullDown] at hk
  | cons x rest ih =>
    have h0 : a ≤ x := by have := hl 0 (by simp); simp at this; grind
    have hr : ∀ k (hk : k < rest.length), (a + g) + (k : Rat) * g ≤ rest[k] := fun k hk => by
      have := hl (k + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      push_cast at this
      grind
    cases h : pullDown g rest with
    | nil =>
      simp only [pullDown, h]
      cases k with
      | zero => simp; grind
      | succ k => simp [pullDown, h] at hk
    | cons y r =>
      have ih' := ih (a + g) hr
      simp only [h] at ih'
      simp only [pullDown, h]
      cases k with
      | zero =>
        have := ih' 0 (by simp)
        simp at this ⊢
        grind
      | succ k =>
        simp only [List.getElem_cons_succ]
        have := ih' k (by simp [pullDown, h] at hk; simp; omega)
        push_cast
        grind

/-- Pulling down does not move the first time later. -/
theorem pullDown_head_le (g x : Rat) (rest : List Rat) :
    (pullDown g (x :: rest))[0]'(by simp [length_pullDown]) ≤ x := by
  cases h : pullDown g rest with
  | nil => simp [pullDown, h]
  | cons y r => simp [pullDown, h]; grind

/-! ### Spreading the key times -/

/-- Spreading keeps the number of times. -/
theorem length_spreadList (g : Rat) (l : List Rat) : (spreadList g l).length = l.length := by
  cases l with
  | nil => rfl
  | cons t ts => simp [spreadList, length_pullDown, length_pushUp]

/-- Spreading keeps the last time. -/
theorem getLast?_spreadList (g : Rat) (l : List Rat) : (spreadList g l).getLast? = l.getLast? := by
  cases l with
  | nil => rfl
  | cons t ts =>
    simp only [spreadList, getLast?_pullDown]
    cases ts with
    | nil => rfl
    | cons y r =>
      simp only [List.getLast?_cons_cons]
      rw [show pushUp g t (y :: r) = (pushUp g t (y :: r)) from rfl]
      obtain ⟨z, w, hz⟩ : ∃ z w, pushUp g t (y :: r) = z :: w := by
        cases r <;> simp [pushUp]
      rw [hz, List.getLast?_cons_cons, ← hz, getLast?_pushUp]

/-- After spreading, each time is at least `g` before the next. -/
theorem spreadList_chain (g : Rat) (l : List Rat) (k : Nat) (hk : k + 1 < (spreadList g l).length) :
    (spreadList g l)[k] + g ≤ (spreadList g l)[k + 1] := by
  cases l with
  | nil => simp [spreadList] at hk
  | cons t ts => exact pullDown_chain g _ k hk

/-- Spreading times that start at `0` and end at `1`, `m + 1` of them with `m g ≤ 1`, keeps the
first at `0` and every time at least `k g`. -/
theorem spreadList_ge (g : Rat) (ts : List Rat) (hg : 0 ≤ g)
    (hlast : (0 :: ts).getLast? = some 1) (hm : (ts.length : Rat) * g ≤ 1) (k : Nat)
    (hk : k < (spreadList g (0 :: ts)).length) :
    (k : Rat) * g ≤ (spreadList g (0 :: ts))[k] := by
  have hF : ∀ k (hk : k < (0 :: pushUp g 0 ts).length),
      0 + (k : Rat) * g ≤ (0 :: pushUp g 0 ts)[k] := by
    intro k hk
    cases k with
    | zero => simp; grind
    | succ k =>
      simp only [List.getElem_cons_succ]
      simp only [List.length_cons, length_pushUp] at hk
      by_cases hl : k + 1 < (pushUp g 0 ts).length
      · have := pushUp_ge g 0 ts k hl
        push_cast; grind
      · -- the last time, which is `1`
        have hkl : k = ts.length - 1 := by rw [length_pushUp] at hl; omega
        have hne : ts ≠ [] := by intro h; subst h; simp at hk
        have hl1 : ts.getLast? = some 1 := by
          obtain ⟨y, r, rfl⟩ := List.exists_cons_of_ne_nil hne
          simpa [List.getLast?_cons_cons] using hlast
        have : (pushUp g 0 ts).getLast? = some 1 := by rw [getLast?_pushUp]; exact hl1
        rw [List.getLast?_eq_getElem?, length_pushUp] at this
        have hk' : k < (pushUp g 0 ts).length := by rw [length_pushUp]; omega
        have hv : (pushUp g 0 ts)[k] = 1 := by
          subst hkl
          rw [List.getElem?_eq_getElem hk'] at this
          exact Option.some.inj this
        rw [hv]
        have : ((k : Rat) + 1) ≤ ts.length := by
          have : k + 1 ≤ ts.length := by omega
          exact_mod_cast this
        have : ((k : Rat) + 1) * g ≤ (ts.length : Rat) * g :=
          Rat.mul_le_mul_of_nonneg_right this hg
        push_cast; grind
  have := pullDown_ge g 0 _ hF k hk
  simp only [spreadList] at this ⊢
  grind

/-- Spreading times that start at `0` keeps the first at `0`. -/
theorem spreadList_zero (g : Rat) (ts : List Rat) (hg : 0 ≤ g)
    (hlast : (0 :: ts).getLast? = some 1) (hm : (ts.length : Rat) * g ≤ 1) :
    (spreadList g (0 :: ts))[0]'(by simp [length_spreadList]) = 0 := by
  have h₁ := spreadList_ge g ts hg hlast hm 0 (by simp [length_spreadList])
  have h₂ := pullDown_head_le g 0 (pushUp g 0 ts)
  simp only [spreadList] at h₁ ⊢
  simp at h₁
  grind

/-! ### The effective gap -/

/-- The effective gap is not negative. -/
theorem effectiveGap_nonneg (gap : Rat) (m : Nat) : 0 ≤ effectiveGap gap m := by
  unfold effectiveGap
  split
  · exact Rat.le_refl
  · have : (0 : Rat) ≤ 1 / (2 * m) := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg (by decide) (by
        rcases Nat.eq_zero_or_pos m with h | h
        · subst h; simp
        · exact Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (by omega : 0 < 2 * m))))
    have : (0 : Rat) < minGap := by unfold minGap; decide +kernel
    grind

/-- A gap above zero gives an effective gap above zero. -/
theorem effectiveGap_pos (gap : Rat) (m : Nat) (hg : 0 < gap) (hm : 0 < m) :
    0 < effectiveGap gap m := by
  unfold effectiveGap
  have : ¬ gap ≤ 0 := Rat.not_le.mpr hg
  simp only [this, ite_false]
  have : (0 : Rat) < 1 / (2 * m) := by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.inv_pos.mpr (by exact_mod_cast (by omega : 0 < 2 * m))
  grind

/-- `m` effective gaps take at most the whole cycle. -/
theorem effectiveGap_mul_le (gap : Rat) (m : Nat) : (m : Rat) * effectiveGap gap m ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp; decide
  have hm : (0 : Rat) < m := by exact_mod_cast h
  have hle : effectiveGap gap m ≤ 1 / (2 * m) := by
    unfold effectiveGap; split
    · rw [Rat.div_def, Rat.one_mul]
      exact Rat.le_of_lt (Rat.inv_pos.mpr (by exact_mod_cast (by omega : 0 < 2 * m)))
    · grind
  have hne : (2 * (m : Rat)) ≠ 0 := Rat.ne_of_gt (by grind)
  have h2 : 2 * ((m : Rat) * (1 / (2 * m))) = 1 := by
    rw [Rat.div_def, Rat.one_mul, ← Rat.mul_assoc]
    exact Rat.mul_inv_cancel _ hne
  have := Rat.mul_le_mul_of_nonneg_left hle (Rat.le_of_lt hm)
  grind

/-! ### The key times written -/

variable (steps : Array Step) (p : Pacing) (o : Options)

/-- The written key times of `build steps p` are the spread key times. -/
theorem times_toList :
    (times (build steps p) o).toList =
      spreadList (effectiveGap o.gap (build steps p).segments.size)
        (build steps p).keyTimes.toList := by
  simp [times, keyTimes_size]

/-- There is one key time more than segments. -/
theorem times_size : (times (build steps p) o).size = (build steps p).segments.size + 1 := by
  simp [times, length_spreadList, keyTimes_size]

/-- Consecutive key times are at least the effective gap apart. -/
theorem times_chain (i : Nat) (h : i + 1 < (times (build steps p) o).size) :
    (times (build steps p) o)[i] + effectiveGap o.gap (build steps p).segments.size ≤
      (times (build steps p) o)[i + 1] := by
  have := spreadList_chain (effectiveGap o.gap (build steps p).segments.size)
    (build steps p).keyTimes.toList i (by simpa [times, keyTimes_size] using h)
  simpa [times, keyTimes_size] using this

/-- The key times never decrease (whatever the cycle). -/
theorem times_mono (i : Nat) (h : i + 1 < (times (build steps p) o).size) :
    (times (build steps p) o)[i] ≤ (times (build steps p) o)[i + 1] := by
  have := times_chain steps p o i h
  have := effectiveGap_nonneg o.gap (build steps p).segments.size
  grind

/-- With a gap above zero, each key time is more than the one before it. -/
theorem times_strict (hg : 0 < o.gap) (i : Nat) (h : i + 1 < (times (build steps p) o).size) :
    (times (build steps p) o)[i] < (times (build steps p) o)[i + 1] := by
  have := times_chain steps p o i h
  have := effectiveGap_pos o.gap _ hg (build_size_pos steps p)
  grind

/-- The key times as `0 ::` the rest, the last being `1`, when the cycle is longer than zero. -/
theorem keyTimes_toList_shape (hc : 0 < (build steps p).cycle) :
    ∃ ts, (build steps p).keyTimes.toList = 0 :: ts ∧ (0 :: ts).getLast? = some 1 ∧
      ts.length = (build steps p).segments.size := by
  have h0 := keyTimes_zero steps p
  have h1 := keyTimes_last steps p hc
  have hs := keyTimes_size steps p
  cases hl : (build steps p).keyTimes.toList with
  | nil => have := congrArg List.length hl; simp [hs] at this
  | cons t ts =>
    have ht : t = 0 := by
      have : (build steps p).keyTimes.toList[0]'(by simp [hs]) = 0 := by simpa using h0
      simpa [hl] using this
    subst ht
    have hlen : ts.length = (build steps p).segments.size := by
      have := congrArg List.length hl; simp [hs] at this; omega
    refine ⟨ts, rfl, ?_, hlen⟩
    rw [← hl, List.getLast?_eq_getElem?]
    simp [hs, h1]

/-- When the cycle is longer than zero, the first key time is `0`. -/
theorem times_zero (hc : 0 < (build steps p).cycle) :
    (times (build steps p) o)[0]'(by rw [times_size]; omega) = 0 := by
  obtain ⟨ts, hl, hlast, hlen⟩ := keyTimes_toList_shape steps p hc
  have hm := effectiveGap_mul_le o.gap (build steps p).segments.size
  have := spreadList_zero (effectiveGap o.gap (build steps p).segments.size) ts
    (effectiveGap_nonneg ..) hlast (by rw [hlen]; exact hm)
  have ht := times_toList steps p o
  rw [hl] at ht
  simp only [← Array.getElem_toList, ht]
  exact this

/-- When the cycle is longer than zero, the last key time is `1`. -/
theorem times_last (hc : 0 < (build steps p).cycle) :
    (times (build steps p) o)[(build steps p).segments.size]'(by rw [times_size]; omega) = 1 := by
  obtain ⟨ts, hl, hlast, hlen⟩ := keyTimes_toList_shape steps p hc
  have ht := times_toList steps p o
  rw [hl] at ht
  have h := getLast?_spreadList (effectiveGap o.gap (build steps p).segments.size) (0 :: ts)
  rw [hlast, ← ht, List.getLast?_eq_getElem?] at h
  simp only [Array.length_toList, times_size, Nat.add_sub_cancel] at h
  rw [List.getElem?_eq_getElem (by simp [times_size])] at h
  simpa using h

/-- Times whose consecutive ones never decrease never decrease. -/
theorem le_of_mono (a : Array Rat) (ha : ∀ i (h : i + 1 < a.size), a[i] ≤ a[i + 1])
    (i j : Nat) (hij : i ≤ j) (hj : j < a.size) : a[i] ≤ a[j] := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; exact Rat.le_refl
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le hij with hij | hij
    · exact Rat.le_trans (ih (by omega) (by omega)) (ha j hj)
    · subst hij; exact Rat.le_refl

/-- When the cycle is longer than zero, every key time lies in `[0, 1]`. -/
theorem times_mem (hc : 0 < (build steps p).cycle) (i : Nat)
    (h : i < (times (build steps p) o).size) :
    0 ≤ (times (build steps p) o)[i] ∧ (times (build steps p) o)[i] ≤ 1 := by
  have hs := times_size steps p o
  have h₁ := le_of_mono _ (times_mono steps p o) 0 i (Nat.zero_le _) h
  have h₂ := le_of_mono _ (times_mono steps p o) i (build steps p).segments.size (by omega)
    (by omega)
  rw [times_zero steps p o hc] at h₁
  rw [times_last steps p o hc] at h₂
  exact ⟨h₁, h₂⟩

/-! ### Counts, splines and the seam -/

/-- There is one key at each boundary: one more than the segments. -/
theorem boundaryKeys_size (tl : Timeline) (h : 0 < tl.segments.size) :
    (boundaryKeys tl).size = tl.segments.size + 1 := by
  unfold boundaryKeys
  rw [Array.getElem?_eq_getElem h]
  simp; omega

/-- The values at the keys of the boundaries are one more than the segments. -/
theorem keyValues_size (f : Nat → String) :
    (keyValues (build steps p) f).size = (build steps p).segments.size + 1 := by
  simp [keyValues, boundaryKeys_size _ (build_size_pos steps p)]

/-- The opacities of the motion layer are one more than the segments. -/
theorem seamLevels_size :
    (seamLevels (build steps p)).size = (build steps p).segments.size + 1 := by
  unfold seamLevels
  rw [Array.getElem?_eq_getElem (build_size_pos steps p)]
  simp; omega

/-- A track on `build steps p` with a value at each boundary (as `keyValues` and `seamLevels`
give) has as many values as key times, and one easing fewer than key times. -/
theorem track_counts (tag : String) (head : Array (String × String)) (values : Array String)
    (hv : values.size = (build steps p).segments.size + 1) :
    (track tag head (build steps p) values o).values.size =
        (track tag head (build steps p) values o).times.size ∧
      (track tag head (build steps p) values o).times.size =
        (track tag head (build steps p) values o).splines.size + 1 := by
  simp [track, times_size, hv]

/-- The easing of interval `i` is that of segment `i`. -/
theorem track_splines (tag : String) (head : Array (String × String)) (tl : Timeline)
    (values : Array String) (i : Nat) (h : i < tl.segments.size) :
    (track tag head tl values o).splines[i]'(by simpa [track] using h) =
      tl.segments[i].easing := by
  simp [track]

/-- The interval of the move of step `j` has the step's easing. -/
theorem track_splines_move (tag : String) (head : Array (String × String)) (values : Array String)
    (i j : Nat) (h : i < (build steps p).segments.size)
    (hk : (build steps p).segments[i].kind = .move j) :
    ∃ hj : j < steps.size,
      (track tag head (build steps p) values o).splines[i]'(by simpa [track] using h) =
        steps[j].easing := by
  obtain ⟨hj, -, he⟩ := build_move_spec steps p i j h hk
  exact ⟨hj, by rw [track_splines]; exact he⟩

/-- The interval of a rest or of a fade has the identity easing. -/
theorem track_splines_still (tag : String) (head : Array (String × String))
    (values : Array String) (i : Nat) (h : i < (build steps p).segments.size)
    (hk : (∃ k, (build steps p).segments[i].kind = .rest k) ∨
      (build steps p).segments[i].kind = .seamIn ∨ (build steps p).segments[i].kind = .seamOut) :
    (track tag head (build steps p) values o).splines[i]'(by simpa [track] using h) =
      .linear := by
  rw [track_splines]
  rcases hk with ⟨k, hk⟩ | hk
  · exact (build_rest_spec steps p i k h hk).2
  · obtain ⟨_, _, _, he⟩ := build_seam_spec steps p i h hk
    exact he

/-- Under a crossfade the motion layer's opacity is `0` at the first and at the last boundary. -/
theorem seamLevels_crossfade (d : Rat) (hs : p.seam = .crossfade d) :
    (seamLevels (build steps p))[0]? = some 0 ∧
      (seamLevels (build steps p))[(build steps p).segments.size]? = some 0 := by
  have hk := build_kinds_crossfade steps p d hs
  have h0 := build_size_pos steps p
  have hfirst : (build steps p).segments[0].kind = .seamIn := by
    have := congrArg (·[0]?) hk
    simp only [List.getElem?_map, Array.getElem?_toList] at this
    rw [Array.getElem?_eq_getElem h0] at this
    simpa using this
  have hlast : (build steps p).segments[(build steps p).segments.size - 1].kind = .seamOut := by
    have := congrArg List.getLast? hk
    rw [List.getLast?_append] at this
    simp only [List.getLast?_map, List.getLast?_singleton, Option.some_or] at this
    rw [Array.getLast?_toList, Array.back?, Array.getElem?_eq_getElem (by omega)] at this
    simpa using this
  unfold seamLevels
  rw [Array.getElem?_eq_getElem h0]
  refine ⟨?_, ?_⟩
  · rw [Array.getElem?_append_left (by simp)]
    simp [hfirst]
  · rw [Array.getElem?_append_right (by simp; omega)]
    simp only [List.size_toArray, List.length_singleton]
    rw [Array.getElem?_map, Array.getElem?_eq_getElem (by omega)]
    simp [hlast]

/-- The hypotheses can be met: the default pacing has a cycle longer than zero and a gap above
zero. -/
example : 0 < (build #[({} : Pacing).turnStep] {}).cycle ∧ 0 < ({} : Options).gap := by
  decide +kernel

end Smil

end PILean.Anim
