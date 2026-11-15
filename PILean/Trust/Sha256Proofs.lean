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

/-- The padded message has a multiple of 64 bytes. -/
theorem pad_size_mod (m : ByteArray) : (pad m).size % 64 = 0 := by
  sorry

/-- The padded message is longer than the message. -/
theorem size_lt_pad_size (m : ByteArray) : m.size < (pad m).size := by
  sorry

/-- The padded message is at most 72 bytes longer than the message. -/
theorem pad_size_le (m : ByteArray) : (pad m).size ≤ m.size + 72 := by
  sorry

/-- The padded message starts with the message. -/
theorem pad_getElem!_prefix (m : ByteArray) (i : Nat) (h : i < m.size) :
    (pad m)[i]! = m[i]! := by
  sorry

/-- The byte after the message in the padded message is `0x80`. -/
theorem pad_getElem!_marker (m : ByteArray) : (pad m)[m.size]! = 0x80 := by
  sorry

/-- The digest has 32 bytes. -/
theorem hash_size (m : ByteArray) : (hash m).size = 32 := by
  sorry

end PILean.Sha256
