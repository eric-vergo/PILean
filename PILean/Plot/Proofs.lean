/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plot.Ticks

/-!
# Theorems about ticks

The ticks of every axis are integer multiples of a step, `k · step` for the multipliers `k` of
`tickMultipliers a b` (`niceTicks`, `minorValues`, `logTicks` all take them from there). Proved
about that function:

* `tickMultipliers_strictlyIncreasing`: the multipliers ascend strictly, so no tick repeats and
  they come in order;
* `mem_tickMultipliers`: they are exactly the integers of `[a, b]`, so every tick lies between
  the first and the last multiple of the step inside the axis's range;
* `tickMultipliers_length`: there are `b - a + 1` of them (none when `b < a`).

The conversion to `Float` (`k · step`) is tested, not proved: floating-point multiplication by a
positive step preserves the order of the multipliers, and the tests check the values' order and
bounds on every gallery axis. Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace PILean.Plot

/-- The tick multipliers ascend strictly. -/
theorem tickMultipliers_strictlyIncreasing (a b : Int) :
    (tickMultipliers a b).Pairwise (· < ·) := by
  unfold tickMultipliers
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp (fun h => by omega)

/-- The tick multipliers are exactly the integers from `a` to `b`. -/
theorem mem_tickMultipliers (a b k : Int) : k ∈ tickMultipliers a b ↔ a ≤ k ∧ k ≤ b := by
  simp only [tickMultipliers, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨(k - a).toNat, by omega, by omega⟩

/-- There are `b - a + 1` tick multipliers. -/
theorem tickMultipliers_length (a b : Int) :
    (tickMultipliers a b).length = (b - a + 1).toNat := by
  simp [tickMultipliers]

/-- The hypotheses can be met: the multipliers of `[-1, 1]`. -/
example : tickMultipliers (-1) 1 = [-1, 0, 1] := by decide

end PILean.Plot
