/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Image.Ops

/-!
# Properties of the image operations

Sizes and well-formedness of the results of `Image.crop`, `Image.paste`, `Image.convert`, the
flips and turns, and `Image.new`, and that flipping twice is the identity on a well-formed image.

## Main statements

* `Image.generate_wellFormed`, `Image.new_wellFormed`.
* `Image.crop_width`, `Image.crop_height`, `Image.crop_wellFormed`.
* `Image.paste_wellFormed`, `Image.convert_wellFormed`.
* `Image.flipLeftRight_wellFormed`, `Image.flipLeftRight_flipLeftRight`,
  `Image.flipTopBottom_flipTopBottom`.

## Implementation notes

`Image.resize` is built from loops and its well-formedness is tested (`PILeanTest.Image`), not
proved here.

## References

None.
-/

namespace PILean

namespace Image

/-! ### Sizes of generated images -/

/-- An image made by `generate` is well formed. -/
theorem generate_wellFormed (mode : Mode) (w h : Nat) (f : Nat → Nat → Nat → UInt8) :
    (generate mode w h f).WellFormed := by
  simp [WellFormed, generate, ByteArray.size]

/-- Pushing the elements of a list onto a byte array adds their number. -/
private theorem foldl_push_size (l : List UInt8) (s : ByteArray) :
    (List.foldl (fun b a => b.push a) s l).size = s.size + l.length := by
  induction l generalizing s with
  | nil => simp
  | cons b l ih => simp [ih]; omega

/-- Pushing a pixel's samples once per list element adds their number. -/
private theorem rows_size (px : Array UInt8) (l : List Nat) (s : ByteArray) :
    (List.foldl (fun b _ => Array.foldl (fun b a => b.push a) b px) s l).size
      = s.size + l.length * px.size := by
  induction l generalizing s with
  | nil => simp
  | cons b l ih =>
    rw [List.foldl_cons, ih, ← Array.foldl_toList, foldl_push_size]
    simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- `Image.new` is well formed. -/
theorem new_wellFormed (mode : Mode) (w h : Nat) (c : Rgba) : (new mode w h c).WellFormed := by
  have hpx : (samplesOf mode c).size = mode.channels := by cases mode <;> rfl
  simp only [new, WellFormed]
  generalize samplesOf mode c = px at hpx ⊢
  simp [Std.Legacy.Range.forIn_eq_forIn_range']
  rw [rows_size]
  simp [hpx]
  rfl

/-- A crop is `(x1 - x0).toNat` wide. -/
theorem crop_width (im : Image) (x0 y0 x1 y1 : Int) :
    (im.crop x0 y0 x1 y1).width = (x1 - x0).toNat := rfl

/-- A crop is `(y1 - y0).toNat` high. -/
theorem crop_height (im : Image) (x0 y0 x1 y1 : Int) :
    (im.crop x0 y0 x1 y1).height = (y1 - y0).toNat := rfl

/-- A crop is well formed, whatever the image and the box. -/
theorem crop_wellFormed (im : Image) (x0 y0 x1 y1 : Int) : (im.crop x0 y0 x1 y1).WellFormed :=
  generate_wellFormed _ _ _ _

/-- A paste has `dst`'s size and is well formed. -/
theorem paste_wellFormed (dst src : Image) (x y : Int) (mask : Option Image) :
    (dst.paste src x y mask).WellFormed ∧ (dst.paste src x y mask).width = dst.width ∧
      (dst.paste src x y mask).height = dst.height :=
  ⟨generate_wellFormed _ _ _ _, rfl, rfl⟩

/-- A conversion of a well-formed image is well formed. -/
theorem convert_wellFormed (im : Image) (mode : Mode) (h : im.WellFormed) :
    (im.convert mode).WellFormed := by
  unfold convert
  split
  · exact h
  · exact generate_wellFormed _ _ _ _

/-- A left-right flip keeps the width and the height. -/
theorem flipLeftRight_size (im : Image) :
    im.flipLeftRight.width = im.width ∧ im.flipLeftRight.height = im.height := ⟨rfl, rfl⟩

/-- A left-right flip is well formed. -/
theorem flipLeftRight_wellFormed (im : Image) : im.flipLeftRight.WellFormed :=
  generate_wellFormed _ _ _ _

/-- A quarter turn swaps the width and the height. -/
theorem rotate90_size (im : Image) :
    im.rotate90.width = im.height ∧ im.rotate90.height = im.width := ⟨rfl, rfl⟩

/-! ### Reading a generated image back -/

/-- The index of a sample is inside the data. -/
private theorem index_lt {x y k w h c : Nat} (hx : x < w) (hy : y < h) (hk : k < c) :
    (y * w + x) * c + k < w * h * c := by
  have h1 : y * w + x + 1 ≤ h * w := by
    have := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hy)
    rw [Nat.succ_mul] at this
    omega
  have h2 : (y * w + x + 1) * c ≤ h * w * c := Nat.mul_le_mul_right c h1
  rw [Nat.succ_mul] at h2
  rw [Nat.mul_comm h w] at h2
  omega

/-- A sample of a generated image is the generating function's value. -/
theorem sample_generate {mode : Mode} {w h : Nat} {f : Nat → Nat → Nat → UInt8} {x y k : Nat}
    (hx : x < w) (hy : y < h) (hk : k < mode.channels) :
    (generate mode w h f).sample x y k = f x y k := by
  have hc : 0 < mode.channels := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  have hlt := index_lt hx hy hk
  have hd : ((y * w + x) * mode.channels + k) / mode.channels = y * w + x := by
    rw [Nat.mul_comm (y * w + x), Nat.mul_add_div hc]
    simp [Nat.div_eq_of_lt hk]
  have hm : ((y * w + x) * mode.channels + k) % mode.channels = k := by
    rw [Nat.mul_comm (y * w + x), Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hk
  have hw : 0 < w := Nat.lt_of_le_of_lt (Nat.zero_le x) hx
  have h3 : (y * w + x) % w = x := by
    rw [Nat.mul_comm y w, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hx
  have h4 : (y * w + x) / w = y := by
    rw [Nat.mul_comm y w, Nat.mul_add_div hw]; simp [Nat.div_eq_of_lt hx]
  unfold sample generate
  simp only [hx, hy, hk, and_self, ite_true]
  split
  · rw [ByteArray.getElem_eq_getElem_data]
    simp only [Array.getElem_ofFn, hd, hm, h3, h4]
  · next hs => exact absurd (by simpa [ByteArray.size] using hlt) hs

/-- A function that agrees on the pixels of the image generates the same image. -/
theorem generate_congr {mode : Mode} {w h : Nat} {f g : Nat → Nat → Nat → UInt8}
    (hfg : ∀ x y k, x < w → y < h → k < mode.channels → f x y k = g x y k) :
    generate mode w h f = generate mode w h g := by
  have key : (Array.ofFn (n := w * h * mode.channels) fun i =>
      f (i / mode.channels % w) (i / mode.channels / w) (i % mode.channels)) =
      Array.ofFn (n := w * h * mode.channels) fun i =>
        g (i / mode.channels % w) (i / mode.channels / w) (i % mode.channels) := by
    apply Array.ext
    · simp
    · intro i h1 h2
      simp only [Array.getElem_ofFn]
      have hi : i < w * h * mode.channels := by simpa using h1
      have hc : 0 < mode.channels := by
        rcases Nat.eq_zero_or_pos mode.channels with h0 | h0
        · rw [h0] at hi; simp at hi
        · exact h0
      have hwh : i / mode.channels < w * h := (Nat.div_lt_iff_lt_mul hc).2 hi
      have hw : 0 < w := by
        rcases Nat.eq_zero_or_pos w with h0 | h0
        · rw [h0] at hwh; simp at hwh
        · exact h0
      apply hfg
      · exact Nat.mod_lt _ hw
      · exact (Nat.div_lt_iff_lt_mul hw).2 (by rwa [Nat.mul_comm h w])
      · exact Nat.mod_lt _ hc
  simp only [generate, key]

/-- A well-formed image is generated by its own samples. -/
theorem generate_sample (im : Image) (hwf : im.WellFormed) :
    generate im.mode im.width im.height im.sample = im := by
  obtain ⟨mode, w, h, d⟩ := im
  simp only [WellFormed] at hwf
  simp only [generate]
  refine congrArg (fun dd => ({ mode := mode, width := w, height := h, data := dd } : Image))
    (ByteArray.ext (Array.ext ?_ ?_))
  · dsimp only
    rw [Array.size_ofFn]
    exact hwf.symm
  · intro i h1 h2
    dsimp only
    rw [Array.getElem_ofFn]
    have hi : i < d.size := h2
    have e1 : i / mode.channels / w * w + i / mode.channels % w = i / mode.channels :=
      Nat.div_add_mod' _ _
    have e2 : i / mode.channels * mode.channels + i % mode.channels = i := Nat.div_add_mod' _ _
    have hc : 0 < mode.channels := by
      rcases Nat.eq_zero_or_pos mode.channels with h0 | h0
      · exfalso
        rw [h0, Nat.mul_zero] at hwf
        omega
      · exact h0
    have hk : i % mode.channels < mode.channels := Nat.mod_lt _ hc
    have hwh : i / mode.channels < w * h := (Nat.div_lt_iff_lt_mul hc).2 (by rw [← hwf]; exact hi)
    have hw : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · rw [h0] at hwh; simp at hwh
      · exact h0
    have hx : i / mode.channels % w < w := Nat.mod_lt _ hw
    have hy : i / mode.channels / w < h := (Nat.div_lt_iff_lt_mul hw).2 (by rwa [Nat.mul_comm h w])
    unfold sample
    simp only [hx, hy, hk, and_self, ite_true]
    rw [e1, e2]
    split
    · rfl
    · next hs => exact absurd hi hs

/-- The samples of a left-right flip. -/
theorem sample_flipLeftRight (im : Image) {x y k : Nat} (hx : x < im.width) (hy : y < im.height)
    (hk : k < im.mode.channels) :
    im.flipLeftRight.sample x y k = im.sample (im.width - 1 - x) y k :=
  sample_generate hx hy hk

/-- The samples of a top-bottom flip. -/
theorem sample_flipTopBottom (im : Image) {x y k : Nat} (hx : x < im.width)
    (hy : y < im.height) (hk : k < im.mode.channels) :
    im.flipTopBottom.sample x y k = im.sample x (im.height - 1 - y) k :=
  sample_generate hx hy hk

/-- Flipping left to right twice gives back a well-formed image. -/
theorem flipLeftRight_flipLeftRight (im : Image) (h : im.WellFormed) :
    im.flipLeftRight.flipLeftRight = im := by
  refine Eq.trans ?_ (generate_sample im h)
  show generate im.mode im.width im.height
    (fun x y k => im.flipLeftRight.sample (im.width - 1 - x) y k) = _
  apply generate_congr
  intro x y k hx hy hk
  rw [sample_flipLeftRight im (by omega) hy hk]
  congr 1
  omega

/-- Flipping top to bottom twice gives back a well-formed image. -/
theorem flipTopBottom_flipTopBottom (im : Image) (h : im.WellFormed) :
    im.flipTopBottom.flipTopBottom = im := by
  refine Eq.trans ?_ (generate_sample im h)
  show generate im.mode im.width im.height
    (fun x y k => im.flipTopBottom.sample x (im.height - 1 - y) k) = _
  apply generate_congr
  intro x y k hx hy hk
  rw [sample_flipTopBottom im hx (by omega) hk]
  congr 1
  omega

/-! ### The hypotheses can be met -/

example : (new .rgb 2 3).WellFormed := new_wellFormed _ _ _ _

example : ((new .rgb 3 3).crop 1 1 3 3).width = 2 := rfl

example : ((new .rgb 3 3).crop (-2) 5 1 3).height = 0 := rfl

example : (new .rgba 2 2).flipLeftRight.flipLeftRight = new .rgba 2 2 :=
  flipLeftRight_flipLeftRight _ (new_wellFormed _ _ _ _)

example : (new .l 4 1).flipTopBottom.flipTopBottom = new .l 4 1 :=
  flipTopBottom_flipTopBottom _ (new_wellFormed _ _ _ _)

example : ((new .rgb 2 2).convert .rgba).WellFormed :=
  convert_wellFormed _ _ (new_wellFormed _ _ _ _)

end Image

end PILean
