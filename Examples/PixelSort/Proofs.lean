import Examples.PixelSort.Sort

/-!
# Verified pixel sort — the theorems

Core-Lean-only (no Mathlib) proofs about `Examples.PixelSort.pass`, the
function that generates every frame of `pixelsort.gif`:

* `passes_perm` — **every frame invariant**: after any number of passes the
  list is a permutation of the original. No pixel is ever created or
  destroyed, in any frame.
* `sorted_passes` — **convergence**: `l.length` passes fully sort the
  list, so the animation is provably done by its final frame.
* `pixelSort_correct` — the two combined: the final frame is a sorted
  permutation of the first.
-/

namespace Examples.PixelSort

/-! ## Permutation: every frame is the same multiset of pixels -/

/-- `go cur l` is a permutation of `cur :: l`. -/
theorem go_perm (cur : Nat × α) (l : List (Nat × α)) :
    (go cur l).Perm (cur :: l) := by
  induction l generalizing cur with
  | nil => exact .refl _
  | cons b rest ih =>
    unfold go
    by_cases h : cur.1 ≤ b.1
    · simpa [h] using (ih b).cons cur
    · simp only [h, ite_false]
      exact ((ih cur).cons b).trans (List.Perm.swap cur b rest)

/-- One pass is a permutation. -/
theorem pass_perm (l : List (Nat × α)) : (pass l).Perm l := by
  cases l with
  | nil => exact .refl _
  | cons a rest => exact go_perm a rest

/-- Any number of passes is a permutation — **every frame of the GIF
contains exactly the original pixels**. -/
theorem passes_perm (k : Nat) (l : List (Nat × α)) : (passes k l).Perm l := by
  induction k generalizing l with
  | zero => exact .refl _
  | succ k ih => exact (ih (pass l)).trans (pass_perm l)

/-! ## One pass bubbles a maximum to the end -/

/-- `go` ends with an element that dominates everything it saw. -/
theorem go_max_split (cur : Nat × α) (l : List (Nat × α)) :
    ∃ ys m, go cur l = ys ++ [m] ∧ ∀ x ∈ go cur l, x.1 ≤ m.1 := by
  induction l generalizing cur with
  | nil =>
    exact ⟨[], cur, rfl, by intro x hx; simp only [go] at hx; simp_all⟩
  | cons b rest ih =>
    unfold go
    by_cases h : cur.1 ≤ b.1
    · obtain ⟨ys, m, heq, hbound⟩ := ih b
      refine ⟨cur :: ys, m, by simp [h, heq], ?_⟩
      intro x hx
      simp only [h, ite_true, List.mem_cons] at hx
      rcases hx with rfl | hx
      · -- cur ≤ b ≤ m since b ∈ go b rest
        have hb : b ∈ go b rest := ((go_perm b rest).mem_iff).mpr (List.mem_cons_self ..)
        exact Nat.le_trans h (hbound b hb)
      · exact hbound x hx
    · obtain ⟨ys, m, heq, hbound⟩ := ih cur
      refine ⟨b :: ys, m, by simp [h, heq], ?_⟩
      intro x hx
      simp only [h, ite_false, List.mem_cons] at hx
      rcases hx with rfl | hx
      · -- x = b < cur ≤ m since cur ∈ go cur rest
        have hc : cur ∈ go cur rest := ((go_perm cur rest).mem_iff).mpr (List.mem_cons_self ..)
        exact Nat.le_trans (Nat.le_of_lt (Nat.lt_of_not_le h)) (hbound cur hc)
      · exact hbound x hx

/-- One `pass` of a nonempty list ends with a dominating element. -/
theorem pass_max_split (a : Nat × α) (rest : List (Nat × α)) :
    ∃ ys m, pass (a :: rest) = ys ++ [m] ∧ ∀ x ∈ pass (a :: rest), x.1 ≤ m.1 :=
  go_max_split a rest

/-! ## A dominating last element is inert -/

/-- If `m` dominates `cur` and `l`, a `go` sweep leaves it at the end. -/
theorem go_append_max (cur m : Nat × α) (l : List (Nat × α))
    (hc : cur.1 ≤ m.1) (hl : ∀ x ∈ l, x.1 ≤ m.1) :
    go cur (l ++ [m]) = go cur l ++ [m] := by
  induction l generalizing cur with
  | nil => simp [go, hc]
  | cons b rest ih =>
    have hb : b.1 ≤ m.1 := hl b (List.mem_cons_self ..)
    have hrest : ∀ x ∈ rest, x.1 ≤ m.1 := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    by_cases h : cur.1 ≤ b.1
    · simp [go, h, ih b hb hrest]
    · simp [go, h, ih cur hc hrest]

/-- If `m` dominates `l`, one `pass` leaves it at the end. -/
theorem pass_append_max (m : Nat × α) (l : List (Nat × α))
    (hl : ∀ x ∈ l, x.1 ≤ m.1) :
    pass (l ++ [m]) = pass l ++ [m] := by
  cases l with
  | nil => simp [pass, go]
  | cons a rest =>
    exact go_append_max a m rest (hl a (List.mem_cons_self ..))
      (fun x hx => hl x (List.mem_cons_of_mem _ hx))

/-- If `m` dominates `l`, any number of passes leaves it at the end. -/
theorem passes_append_max (k : Nat) (m : Nat × α) (l : List (Nat × α))
    (hl : ∀ x ∈ l, x.1 ≤ m.1) :
    passes k (l ++ [m]) = passes k l ++ [m] := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    have hpass : ∀ x ∈ pass l, x.1 ≤ m.1 := fun x hx =>
      hl x ((pass_perm l).mem_iff.mp hx)
    calc passes (k + 1) (l ++ [m])
        = passes k (pass (l ++ [m])) := rfl
      _ = passes k (pass l ++ [m]) := by rw [pass_append_max m l hl]
      _ = passes k (pass l) ++ [m] := ih (pass l) hpass

/-! ## Sortedness glue -/

/-- Appending a dominating element to a sorted list keeps it sorted. -/
theorem sorted_append_max (m : Nat × α) (l : List (Nat × α))
    (hs : SortedKeys l) (hl : ∀ x ∈ l, x.1 ≤ m.1) :
    SortedKeys (l ++ [m]) := by
  induction l with
  | nil => exact List.Pairwise.cons (by simp) List.Pairwise.nil
  | cons a rest ih =>
    cases hs with
    | cons ha hrest =>
      refine List.Pairwise.cons ?_ (ih hrest fun x hx => hl x (List.mem_cons_of_mem _ hx))
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact ha x hx
      · simp only [List.mem_singleton] at hx
        subst hx
        exact hl a (List.mem_cons_self ..)

/-! ## Convergence: `length` passes fully sort -/

/-- After `n` passes, a length-`n` list is sorted. -/
theorem sorted_passes_aux : ∀ (n : Nat) (l : List (Nat × α)),
    l.length = n → SortedKeys (passes n l) := by
  intro n
  induction n with
  | zero =>
    intro l h
    rw [List.length_eq_zero_iff.mp h]
    exact List.Pairwise.nil
  | succ n ih =>
    intro l h
    cases l with
    | nil => simp at h
    | cons a rest =>
      obtain ⟨ys, m, heq, hbound⟩ := pass_max_split a rest
      -- ys has length n
      have hlen : ys.length = n := by
        have h1 : (pass (a :: rest)).length = n + 1 :=
          (pass_perm (a :: rest)).length_eq.trans h
        rw [heq, List.length_append, List.length_singleton] at h1
        omega
      have hysBound : ∀ x ∈ ys, x.1 ≤ m.1 := fun x hx =>
        hbound x (heq ▸ List.mem_append_left [m] hx)
      show SortedKeys (passes n (pass (a :: rest)))
      rw [heq, passes_append_max n m ys hysBound]
      exact sorted_append_max m (passes n ys) (ih ys hlen)
        (fun x hx => hysBound x ((passes_perm n ys).mem_iff.mp hx))

/-- **Convergence**: `l.length` passes sort any list — the animation is
provably complete by its final frame. -/
theorem sorted_passes (l : List (Nat × α)) : SortedKeys (passes l.length l) :=
  sorted_passes_aux l.length l rfl

/-- The headline: the final frame is a **sorted permutation** of the first
frame — every original pixel present, in luma order. -/
theorem pixelSort_correct (l : List (Nat × α)) :
    (passes l.length l).Perm l ∧ SortedKeys (passes l.length l) :=
  ⟨passes_perm l.length l, sorted_passes l⟩

end Examples.PixelSort
