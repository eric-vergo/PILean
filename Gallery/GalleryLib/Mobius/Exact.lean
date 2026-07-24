import Mathlib.LinearAlgebra.Matrix.Notation

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

end Gallery.Mobius
