import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Möbius flow — the exact (ℚ) layer

The rational Möbius rotation family `M t = [[1, −t], [t, 1]]` and the
exact projective normalization the renderer feeds to its Float pipeline.
Everything here is computable ℚ arithmetic; the theorems (added by the
proofs work package) certify the tangent addition law and its
normalization corollary — the fact that makes the finale's two renders
byte-identical.

**Frozen defs**: `M`, `normalize`, `entries` are the interface the render
layer builds against — theorems are added below them, the defs themselves
do not change.
-/

namespace Gallery.Mobius

open Matrix

/-- The rational Möbius rotation family: `M t` acts on the plane as
`z ↦ (z − t)/(t·z + 1)` — an elliptic rotation with tangent-half-angle
parameter `t`. -/
def M (t : ℚ) : Matrix (Fin 2) (Fin 2) ℚ := !![1, -t; t, 1]

/-- Canonical representative of a matrix's projective class: divide every
entry by the first nonzero entry (row-major scan), exactly, in ℚ. Möbius
maps are unchanged by nonzero scaling, so feeding *normalized* entries to
the Float renderer makes provably-equal maps render byte-identically. -/
def normalize (A : Matrix (Fin 2) (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  let pivot :=
    if A 0 0 ≠ 0 then A 0 0
    else if A 0 1 ≠ 0 then A 0 1
    else if A 1 0 ≠ 0 then A 1 0
    else A 1 1
  if pivot = 0 then A else Matrix.of fun i j => A i j / pivot

/-- The four entries `(a, b, c, d)` of a 2×2 matrix, row-major — the
computable hand-off from the exact layer to the Float renderer. -/
def entries (A : Matrix (Fin 2) (Fin 2) ℚ) : ℚ × ℚ × ℚ × ℚ :=
  (A 0 0, A 0 1, A 1 0, A 1 1)

/-! ## Theorems

The showcase's signature beat is a *rendered* identity: two different
parameter pairs `(1/3, 1/2)` and `(1,)` produce byte-identical GIF frames.
That is only true because it is first a *mathematical* identity — the
tangent addition law for the Möbius rotation family, `mobius_add` below —
and because projective normalization erases the scalar factor the group
law leaves behind, `normalize_smul`. `normalized_composition` chains the
two into the statement the render layer actually relies on, and the
example at the end is the concrete instance it animates. -/

/-- **Tangent addition law.** Composing two Möbius rotations multiplies
their matrices to `(1 - s*t)` times the matrix for the "added" parameter
`(s + t) / (1 - s*t)` — the familiar `tan(α + β)` addition formula, here
exact over `ℚ` and matrix-valued instead of scalar. This is the algebraic
heart of the showcase: it is *why* `M (1/3) * M (1/2)` and `M 1` describe
the same projective map (`1/3 + 1/2 = 5/6` and `1 - (1/3)*(1/2) = 5/6`, so
the "added" parameter is exactly `1`). -/
theorem mobius_add (s t : ℚ) (h : s * t ≠ 1) :
    M s * M t = (1 - s * t) • M ((s + t) / (1 - s * t)) := by
  have hd : (1 : ℚ) - s * t ≠ 0 := sub_ne_zero.mpr h.symm
  -- `field_simp` needs the denominator's nonzero-ness in whichever multiplication
  -- order it settles on internally, so both commutations are on hand.
  have hd' : (1 : ℚ) - t * s ≠ 0 := by rw [mul_comm]; exact hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, Matrix.smul_apply] <;>
    field_simp <;> ring

/-- **Normalization erases scalar factors.** `normalize` picks out the
first nonzero entry (row-major) and divides the whole matrix by it, so
scaling a matrix by any nonzero constant before normalizing has no effect
on the result: the pivot scales along with everything else and cancels.
This is what lets the renderer treat `mobius_add`'s leftover scalar
`(1 - s*t)` as noise — `M s * M t` and `M ((s+t)/(1-s*t))` normalize to
the same matrix even though they are not equal on the nose. -/
theorem normalize_smul (c : ℚ) (hc : c ≠ 0) (A : Matrix (Fin 2) (Fin 2) ℚ) :
    normalize (c • A) = normalize A := by
  -- Scaling by nonzero `c` never flips an entry between zero and nonzero, so the
  -- pivot-selection scan lands on the *same* entry for `c • A` as for `A`.
  simp only [normalize, Matrix.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, hc, false_or]
  split_ifs <;>
    first
      | rfl
      | (simp_all only [mul_eq_zero]; done)
      | (ext i j; fin_cases i <;> fin_cases j <;> simp_all; done)
      | (ext i j; simp only [Matrix.of_apply]; field_simp)

/-- **The render layer's actual dependency.** Composing two Möbius
rotations and normalizing gives the same result as forming the "added"
rotation directly and normalizing it — `mobius_add` plus `normalize_smul`,
chained through `sub_ne_zero`. This is the theorem the finale animates:
the frames the renderer produces from `entries ∘ normalize` applied to
either side must be byte-identical, because the two sides are *equal*,
not merely numerically close. -/
theorem normalized_composition (s t : ℚ) (h : s * t ≠ 1) :
    normalize (M s * M t) = normalize (M ((s + t) / (1 - s * t))) := by
  rw [mobius_add s t h, normalize_smul (1 - s * t) (sub_ne_zero.mpr h.symm)]

/-- **The concrete witness the finale renders.** `1/3` and `1/2` compose
(tangent addition) to parameter `1`: `(1/3 + 1/2) / (1 - 1/3 * 1/2) = 1`.
So `M (1/3) * M (1/2)` and `M 1` are different matrices but the *same*
projective map, and `normalize` — the exact ℚ step the renderer runs
before ever touching `Float` — proves it by making them the same matrix
on the nose.

Kernel `decide` on this goal gets stuck: `ℚ`'s `DecidableEq` unfolds through
`Int`/`Nat` numeral matching that the kernel's `whnf` does not reduce far
enough for the divisions `normalize` introduces (this is a well-known
`decide`-on-`ℚ` limitation, not specific to this file). We route around it
through `normalized_composition` instead — a proof term built from
`mobius_add`/`normalize_smul`, discharging the arithmetic side-conditions
with `norm_num` — so the witness stays `native_decide`-free, as required for
theorems 1–3's `#print axioms` to stay clean of `Lean.ofReduceBool`. -/
example : normalize (M (1/3) * M (1/2)) = normalize (M 1) := by
  have h : (1/3 : ℚ) * (1/2) ≠ 1 := by norm_num
  have := normalized_composition (1/3) (1/2) h
  norm_num at this
  exact this

end Gallery.Mobius
