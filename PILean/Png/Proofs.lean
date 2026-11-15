/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Png.Checksum

/-!
# Proofs about the PNG codec

## Main statements

* `crc32_eq_crc32Bits`: the table-driven CRC-32 equals the bitwise definition.
* `adler32_eq_adlerSpec`: the byte-by-byte Adler-32 equals the sums of RFC 1950.

## Implementation notes

Only the axioms `propext`, `Classical.choice` and `Quot.sound` are used (checked in the tests
with `#print axioms`).

## References

* PNG Specification, Third Edition (W3C); RFC 1950; RFC 1951.
-/

namespace PILean.Png

/-! ### Folds over byte arrays -/

theorem foldlM_loop_eq {β : Type} (f : β → UInt8 → β) (as : ByteArray) (stop : Nat)
    (h : stop ≤ as.size) (i j : Nat) (b : β) (hij : j + i = stop) :
    (ByteArray.foldlM.loop (m := Id) (fun x y => pure (f x y)) as stop h i j b) =
      ((as.data.toList.drop j).take i).foldl f b := by
  induction i generalizing j b with
  | zero => simp [ByteArray.foldlM.loop]; rfl
  | succ n ih =>
    rw [ByteArray.foldlM.loop]
    have hj : j < stop := by omega
    have hj' : j < as.size := by omega
    simp only [hj, ↓reduceDIte]
    show ByteArray.foldlM.loop (m := Id) (fun x y => pure (f x y)) as stop h n (j + 1)
      (f b as[j]) = _
    rw [ih (j + 1) _ (by omega)]
    have hl : j < as.data.toList.length := by simpa using hj'
    rw [List.drop_eq_getElem_cons hl, List.take_succ_cons, List.foldl_cons]
    rfl

/-- A `ByteArray` fold is the fold over its list of bytes. -/
theorem bytearray_foldl_eq {β : Type} (f : β → UInt8 → β) (b : β) (as : ByteArray) :
    as.foldl f b = as.data.toList.foldl f b := by
  unfold ByteArray.foldl ByteArray.foldlM
  simp
  have := foldlM_loop_eq f as as.size (Nat.le_refl _) as.size 0 b (by omega)
  show ByteArray.foldlM.loop (m := Id) (fun x y => pure (f x y)) as as.size _ as.size 0 b = _
  rw [this]
  simp only [List.drop_zero]
  rw [List.take_of_length_le (by rw [Array.length_toList]; exact Nat.le_refl _)]
  exact Array.foldl_toList f

/-! ### CRC-32 -/

theorem uint32_and_xor (a b c : UInt32) : (a ^^^ b) &&& c = (a &&& c) ^^^ (b &&& c) := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp [BitVec.getElem_and, BitVec.getElem_xor]
  cases a.toBitVec[i] <;> cases b.toBitVec[i] <;> cases c.toBitVec[i] <;> simp

theorem uint32_and_one_cases (x : UInt32) : x &&& 1 = 0 ∨ x &&& 1 = 1 := by
  have h : (x &&& 1).toNat = x.toNat % 2 := by
    rw [UInt32.toNat_and]; exact Nat.and_one_is_mod _
  have : x.toNat % 2 = 0 ∨ x.toNat % 2 = 1 := by omega
  rcases this with h0 | h0
  · left; apply UInt32.toNat_inj.mp; simp [h, h0]
  · right; apply UInt32.toNat_inj.mp; simp [h, h0]

theorem crcBitStep_xor (a b : UInt32) :
    crcBitStep (a ^^^ b) = crcBitStep a ^^^ crcBitStep b := by
  unfold crcBitStep
  rw [uint32_and_xor]
  rcases uint32_and_one_cases a with ha | ha <;> rcases uint32_and_one_cases b with hb | hb <;>
    simp [ha, hb, UInt32.shiftRight_xor, UInt32.xor_assoc]
  · exact UInt32.xor_comm _ _
  · rw [UInt32.xor_comm (b >>> 1), ← UInt32.xor_assoc, UInt32.xor_self, UInt32.zero_xor]

theorem crcByteBits_xor (a b : UInt32) :
    crcByteBits (a ^^^ b) = crcByteBits a ^^^ crcByteBits b := by
  simp only [crcByteBits, crcBitStep_xor]

theorem crcBitStep_of_even (y : UInt32) (h : y.toNat % 2 = 0) : crcBitStep y = y >>> 1 := by
  have h1 : y &&& 1 = 0 := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_and]
    have := Nat.and_one_is_mod y.toNat
    simp [this, h]
  simp [crcBitStep, h1]

theorem uint32_shr_one_toNat (y : UInt32) : (y >>> 1).toNat = y.toNat / 2 := by
  simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

theorem uint32_shr_eight_toNat (y : UInt32) : (y >>> 8).toNat = y.toNat / 256 := by
  simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

theorem uint32_split (c : UInt32) : c = (c <<< 24 >>> 24) ^^^ ((c >>> 8) <<< 8) := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp [BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft, UInt32.toBitVec_shiftLeft,
    UInt32.toBitVec_shiftRight]
  rw [← BitVec.getLsbD_eq_getElem hi]
  by_cases h : i < 8
  · have h1 : 24 + i < 32 := by omega
    have h2 : ¬ 24 + i < 24 := by omega
    simp [h, h1, h2]
  · have h2 : 8 + (i - 8) = i := by omega
    have h3 : ¬ 24 + i < 32 := by omega
    simp [h, h2, h3]

theorem uint32_hi_shift (c : UInt32) : ((c >>> 8) <<< 8) >>> 8 = c >>> 8 := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp [BitVec.getElem_ushiftRight, UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight]
  intro h
  apply Classical.byContradiction
  intro h'
  have := BitVec.getLsbD_of_ge c.toBitVec (8 + i) (by omega)
  simp_all

theorem uint32_hi_toNat (c : UInt32) :
    ((c >>> 8) <<< 8).toNat = c.toNat / 256 * 256 := by
  simp [UInt32.toNat_shiftLeft, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  have := c.toNat_lt
  omega

/-- Eight steps on a register whose low eight bits are zero just shift it right by eight. -/
theorem crcByteBits_hi (c : UInt32) : crcByteBits ((c >>> 8) <<< 8) = c >>> 8 := by
  have h0 : ((c >>> 8) <<< 8).toNat % 256 = 0 := by rw [uint32_hi_toNat]; omega
  generalize hy : (c >>> 8) <<< 8 = y at h0 ⊢
  unfold crcByteBits
  rw [crcBitStep_of_even y (by omega)]
  rw [crcBitStep_of_even (y >>> 1) (by rw [uint32_shr_one_toNat]; omega)]
  rw [crcBitStep_of_even (y >>> 1 >>> 1) (by simp only [uint32_shr_one_toNat]; omega)]
  rw [crcBitStep_of_even (y >>> 1 >>> 1 >>> 1) (by simp only [uint32_shr_one_toNat]; omega)]
  rw [crcBitStep_of_even (y >>> 1 >>> 1 >>> 1 >>> 1) (by simp only [uint32_shr_one_toNat]; omega)]
  rw [crcBitStep_of_even (y >>> 1 >>> 1 >>> 1 >>> 1 >>> 1)
    (by simp only [uint32_shr_one_toNat]; omega)]
  rw [crcBitStep_of_even (y >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1)
    (by simp only [uint32_shr_one_toNat]; omega)]
  rw [crcBitStep_of_even (y >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1 >>> 1)
    (by simp only [uint32_shr_one_toNat]; omega)]
  rw [← uint32_hi_shift c, ← hy]
  apply UInt32.toNat_inj.mp
  simp only [uint32_shr_one_toNat, uint32_shr_eight_toNat]
  omega

/-- One table lookup does the work of eight bit steps. -/
theorem crcByteBits_table (x : UInt32) :
    crcByteBits x = crcTable[x.toUInt8.toNat]'(by have := x.toUInt8.toNat_lt; omega) ^^^
      (x >>> 8) := by
  conv => lhs; rw [uint32_split x]
  rw [crcByteBits_xor, crcByteBits_hi]
  have h : x.toUInt8.toNat.toUInt32 = x <<< 24 >>> 24 := by
    apply UInt32.toNat_inj.mp
    have := x.toUInt8.toNat_lt
    simp [UInt32.toNat_ofNat, UInt32.toNat_toUInt8, UInt32.toNat_shiftLeft,
      UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    omega
  simp only [crcTable, Vector.getElem_ofFn, h]

theorem crcStep_eq (c : UInt32) (b : UInt8) : crcStep c b = crcByteBits (c ^^^ b.toUInt32) := by
  unfold crcStep
  simp only
  rw [crcByteBits_table, UInt32.shiftRight_xor]
  have : b.toUInt32 >>> 8 = 0 := by
    apply UInt32.toNat_inj.mp
    have := b.toNat_lt
    simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    omega
  rw [this]
  simp

/-- The table-driven CRC-32 equals the bitwise definition, for every byte array. -/
theorem crc32_eq_crc32Bits (data : ByteArray) : crc32 data = crc32Bits data := by
  unfold crc32 crc32Bits crcUpdate
  have : crcStep = fun (c : UInt32) (b : UInt8) => crcByteBits (c ^^^ b.toUInt32) :=
    funext fun c => funext fun b => crcStep_eq c b
  rw [this]

/-! ### Adler-32 -/

/-- The unreduced `B` sum of Adler-32: the sum over all prefixes of `1 +` the prefix sum. -/
def adlerBSum (l : List UInt8) : Nat :=
  ((List.range l.length).map fun k => 1 + byteSum (l.take (k + 1))).sum

theorem byteSum_append_singleton (l : List UInt8) (x : UInt8) :
    byteSum (l ++ [x]) = byteSum l + x.toNat := by
  simp [byteSum]

theorem adlerBSum_append_singleton (l : List UInt8) (x : UInt8) :
    adlerBSum (l ++ [x]) = adlerBSum l + (1 + byteSum l + x.toNat) := by
  unfold adlerBSum
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append, List.sum_append]
  have h1 : ((List.range l.length).map fun k => 1 + byteSum ((l ++ [x]).take (k + 1))) =
      ((List.range l.length).map fun k => 1 + byteSum (l.take (k + 1))) := by
    apply List.map_congr_left
    intro k hk
    have : k + 1 ≤ l.length := by have := List.mem_range.mp hk; omega
    rw [List.take_append_of_le_length this]
  rw [h1]
  have h2 : (l ++ [x]).take (l.length + 1) = l ++ [x] := by
    simp [List.take_of_length_le]
  simp [h2, byteSum_append_singleton]
  omega

/-- Induction on a list from its end. -/
theorem list_rev_ind {α : Type} {P : List α → Prop} (nil : P [])
    (snoc : ∀ l x, P l → P (l ++ [x])) : ∀ l, P l := by
  intro l
  suffices h : ∀ r : List α, P r.reverse by simpa using h l.reverse
  intro r
  induction r with
  | nil => simpa using nil
  | cons x r ih => simpa using snoc _ x ih

/-- The fold state for a list of bytes. -/
def adlerFold (l : List UInt8) : UInt32 × UInt32 :=
  l.foldl (fun (s : UInt32 × UInt32) b =>
    let a := (s.1 + b.toUInt32) % 65521
    (a, (s.2 + a) % 65521)) (1, 0)

theorem adlerFold_spec (l : List UInt8) :
    (adlerFold l).1.toNat = (1 + byteSum l) % adlerMod ∧
      (adlerFold l).2.toNat = adlerBSum l % adlerMod := by
  induction l using list_rev_ind with
  | nil => simp [adlerFold, byteSum, adlerBSum, adlerMod]
  | snoc l x ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have e : adlerFold (l ++ [x]) =
        (((adlerFold l).1 + x.toUInt32) % 65521,
          ((adlerFold l).2 + ((adlerFold l).1 + x.toUInt32) % 65521) % 65521) := by
      simp [adlerFold, List.foldl_append]
    rw [e]
    have hb := x.toNat_lt
    have hA : (adlerFold l).1.toNat < 65521 := by rw [ih1]; unfold adlerMod; omega
    have hB : (adlerFold l).2.toNat < 65521 := by rw [ih2]; unfold adlerMod; omega
    have hx : x.toUInt32.toNat = x.toNat := by simp
    have h1 : ((adlerFold l).1 + x.toUInt32).toNat = (adlerFold l).1.toNat + x.toNat := by
      rw [UInt32.toNat_add, hx]; omega
    have h2 : (((adlerFold l).1 + x.toUInt32) % 65521).toNat =
        ((adlerFold l).1.toNat + x.toNat) % 65521 := by
      rw [UInt32.toNat_mod, h1]; rfl
    refine ⟨?_, ?_⟩
    · simp only [h2, ih1, byteSum_append_singleton, adlerMod]
      omega
    · simp only [UInt32.toNat_mod, UInt32.toNat_add, h2, ih1, ih2, adlerBSum_append_singleton,
        adlerMod]
      show (_ + _) % 4294967296 % 65521 = _
      omega

/-- The byte-by-byte Adler-32 equals the sums `A` and `B` of RFC 1950: the checksum is
`B * 65536 + A`. -/
theorem adler32_eq_adlerSpec (data : ByteArray) :
    (adler32 data).toNat =
      (adlerSpec data.data.toList).2 * 65536 + (adlerSpec data.data.toList).1 := by
  have e : adler32 data =
      ((adlerFold data.data.toList).2 <<< 16) + (adlerFold data.data.toList).1 := by
    unfold adler32 adlerFold
    rw [bytearray_foldl_eq]
  obtain ⟨h1, h2⟩ := adlerFold_spec data.data.toList
  rw [e]
  have hA : (adlerFold data.data.toList).1.toNat < 65521 := by rw [h1]; unfold adlerMod; omega
  have hB : (adlerFold data.data.toList).2.toNat < 65521 := by rw [h2]; unfold adlerMod; omega
  simp only [UInt32.toNat_add, UInt32.toNat_shiftLeft, h1, h2, adlerSpec, adlerBSum]
  simp [Nat.shiftLeft_eq]
  unfold adlerMod
  omega

end PILean.Png
