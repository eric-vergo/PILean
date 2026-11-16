/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Trust.Sha256

/-!
# Facts about SHA-256 padding and the digest size

## Main statements

* `Sha256.pad_size_mod`: the padded message has a multiple of 64 bytes.
* `Sha256.size_lt_pad_size`, `Sha256.pad_size_le`: it is longer than the message, by at most 72
  bytes.
* `Sha256.pad_getElem!_prefix`: it starts with the message.
* `Sha256.pad_getElem!_marker`: the byte after the message is `0x80`.
* `Sha256.hash_size`: the digest has 32 bytes.
-/

namespace PILean.Sha256

/-- The length field of the padding has 8 bytes. -/
theorem lengthBytes_size (n : Nat) : (lengthBytes n).size = 8 := rfl

/-- A word is written as 4 bytes. -/
theorem wordBytes_size (x : UInt32) : (wordBytes x).size = 4 := rfl

/-- The marker of the padding is one byte. -/
theorem marker_size : (⟨#[0x80]⟩ : ByteArray).size = 1 := rfl

/-- An array of `k` zero bytes has `k` bytes. -/
theorem zeros_size (k : Nat) : (⟨Array.replicate k 0⟩ : ByteArray).size = k := by
  show (Array.replicate k 0).size = k
  simp

/-- The size of the padded message: the message, the marker, the zeros and the length field. -/
theorem pad_size (m : ByteArray) : (pad m).size = m.size + 1 + zeroCount m.size + 8 := by
  unfold pad
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_append, lengthBytes_size,
    zeros_size]
  show m.size + 1 + _ + 8 = _
  rfl

/-- Fewer than 64 zero bytes are added. -/
theorem zeroCount_lt (n : Nat) : zeroCount n < 64 := Nat.mod_lt _ (by decide)

/-- An index inside the first of two appended byte arrays reads from the first. -/
theorem getElem!_append_left (a b : ByteArray) (i : Nat) (h : i < a.size) :
    (a ++ b)[i]! = a[i]! := by
  have h1 : i < (a ++ b).size := by rw [ByteArray.size_append]; omega
  rw [getElem!_pos (a ++ b) i h1, getElem!_pos a i h, ByteArray.getElem_append_left h]

/-- The padded message has a multiple of 64 bytes. -/
theorem pad_size_mod (m : ByteArray) : (pad m).size % 64 = 0 := by
  rw [pad_size, zeroCount]
  omega

/-- The padded message is longer than the message. -/
theorem size_lt_pad_size (m : ByteArray) : m.size < (pad m).size := by
  rw [pad_size]
  omega

/-- The padded message is at most 72 bytes longer than the message. -/
theorem pad_size_le (m : ByteArray) : (pad m).size ≤ m.size + 72 := by
  have := zeroCount_lt m.size
  rw [pad_size]
  omega

/-- The padded message starts with the message. -/
theorem pad_getElem!_prefix (m : ByteArray) (i : Nat) (h : i < m.size) :
    (pad m)[i]! = m[i]! := by
  have e1 : i < (m ++ (⟨#[0x80]⟩ : ByteArray)).size := by
    rw [ByteArray.size_append, marker_size]; omega
  have e2 : i < (m ++ (⟨#[0x80]⟩ : ByteArray) ++
      (⟨Array.replicate (zeroCount m.size) 0⟩ : ByteArray)).size := by
    rw [ByteArray.size_append, ByteArray.size_append, marker_size]; omega
  unfold pad
  rw [getElem!_append_left _ _ i e2, getElem!_append_left _ _ i e1,
    getElem!_append_left _ _ i h]

/-- The byte after the message in the padded message is `0x80`. -/
theorem pad_getElem!_marker (m : ByteArray) : (pad m)[m.size]! = 0x80 := by
  have e1 : m.size < (m ++ (⟨#[0x80]⟩ : ByteArray)).size := by
    rw [ByteArray.size_append, marker_size]; omega
  have e2 : m.size < (m ++ (⟨#[0x80]⟩ : ByteArray) ++
      (⟨Array.replicate (zeroCount m.size) 0⟩ : ByteArray)).size := by
    rw [ByteArray.size_append, ByteArray.size_append, marker_size]; omega
  unfold pad
  rw [getElem!_append_left _ _ m.size e2, getElem!_append_left _ _ m.size e1,
    getElem!_pos _ _ (by rw [ByteArray.size_append, marker_size]; omega),
    ByteArray.getElem_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self]
  rfl

/-- The digest has 32 bytes. -/
theorem hash_size (m : ByteArray) : (hash m).size = 32 := by
  simp only [hash, digest, ByteArray.size_append, wordBytes_size]

end PILean.Sha256
