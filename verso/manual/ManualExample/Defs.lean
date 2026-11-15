/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# What the example's figures show

The triangular numbers, defined in a module of their own, as a manual's subject would be: the
figure that plots them (`ManualExample.trianglePlot`) is in another module, and the theorem it is
linked to speaks of `triangle`, not of the figure.
-/

namespace ManualExample

/-- The `n`th triangular number, `0 + 1 + ⋯ + n`. -/
def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => triangle n + (n + 1)

/-- The closed form: twice the `n`th triangular number is `n (n + 1)`. -/
theorem two_mul_triangle (n : Nat) : 2 * triangle n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [triangle, Nat.mul_add, ih, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

end ManualExample
