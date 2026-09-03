import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# TDCSG common-edge carrier geometry

This is the exact layer behind the carrier-line plates.  It contains the
common-edge construction as a theorem over `ℝ`; the renderer is deliberately
downstream of this file and only rounds the certified geometry to pixels.

For midpoint angle `m`, half-edge angle `h`, and

`s = -cos(m) / cos(h)`,

the consecutive vertices

`(1,0) + s (cos (m-h), sin (m-h))` and
`(1,0) + s (cos (m+h), sin (m+h))`

are collinear with the origin.  Negating the two vertices gives the
corresponding edge of the half-turn-related polygon centered at `(-1,0)`, so
both edges have one supporting line through the origin.
-/

namespace Gallery.TDCSG.CarrierLines

/-- A real plane point used by the exact common-edge theorem. -/
structure RPoint where
  x : ℝ
  y : ℝ

/-- Oriented area determinant.  It vanishes exactly when two vectors are
collinear. -/
def cross (p q : RPoint) : ℝ := p.x * q.y - p.y * q.x

/-- Polygon circumradius which places the chosen edge on a line through the
global origin. -/
noncomputable def commonEdgeScale (m h : ℝ) : ℝ := -Real.cos m / Real.cos h

/-- The earlier endpoint of the right-polygon edge, symmetrically expressed
around its midpoint angle. -/
noncomputable def rightEndpointMinus (m h : ℝ) : RPoint :=
  let s := commonEdgeScale m h
  ⟨1 + s * Real.cos (m - h), s * Real.sin (m - h)⟩

/-- The later endpoint of the right-polygon edge, symmetrically expressed
around its midpoint angle. -/
noncomputable def rightEndpointPlus (m h : ℝ) : RPoint :=
  let s := commonEdgeScale m h
  ⟨1 + s * Real.cos (m + h), s * Real.sin (m + h)⟩

/-- Determinant factorization for an edge written symmetrically about its
midpoint direction.  This exposes exactly why the construction's scale works:
`s = -cos m / cos h` kills the final factor. -/
private theorem cross_midpoint_edge (m h s : ℝ) :
    (1 + s * Real.cos (m - h)) * (s * Real.sin (m + h)) -
        (s * Real.sin (m - h)) * (1 + s * Real.cos (m + h)) =
      2 * s * Real.sin h * (Real.cos m + s * Real.cos h) := by
  rw [Real.cos_sub, Real.cos_add, Real.sin_sub, Real.sin_add]
  linear_combination
    (2 * s ^ 2 * Real.cos h * Real.sin h) * (Real.sin_sq_add_cos_sq m)

/-- The two constructed right-polygon edge endpoints and the global origin
are exactly collinear.  The only excluded case is a vanishing denominator in
the scale formula. -/
theorem commonEdge_collinear (m h : ℝ) (hh : Real.cos h ≠ 0) :
    cross (rightEndpointMinus m h) (rightEndpointPlus m h) = 0 := by
  simp only [cross, rightEndpointMinus, rightEndpointPlus, commonEdgeScale]
  rw [cross_midpoint_edge]
  have hz : Real.cos m + (-Real.cos m / Real.cos h) * Real.cos h = 0 := by
    field_simp [hh]
    ring
  rw [hz]
  ring

/-- Negation is the half-turn about the global origin and moves the right
polygon centered at `+1` to its companion centered at `-1`. -/
def halfTurn (p : RPoint) : RPoint := ⟨-p.x, -p.y⟩

/-- Exact metadata for one reflected pair of common-edge lines.  The renderer
derives every angle from `(order, edgeIndex)`; the stored labels are merely
captions and never drive geometry. -/
structure PhasePair where
  order : Nat
  edgeIndex : Nat
  scaleLabel : String
  deriving Repr, DecidableEq, Inhabited

namespace PhasePair

/-- The reflected phase in the fixed counterclockwise polygon convention. -/
def partner (p : PhasePair) : Nat := p.order - 1 - p.edgeIndex

/-- Full central angle in integer degrees.  The plates only instantiate orders
10 and 20, where this division is exact. -/
def stepDeg (p : PhasePair) : Int := (360 / p.order : Nat)

/-- Half a polygon step, again integral for the rendered orders. -/
def halfStepDeg (p : PhasePair) : Int := (180 / p.order : Nat)

/-- Midpoint angle `(2j+1)π/n`, in mathematical counterclockwise degrees. -/
def midpointDeg (p : PhasePair) : Int :=
  ((2 * p.edgeIndex + 1) * 180 / p.order : Nat)

/-- Unoriented mathematical line angle `m - π/2`. -/
def lineAngleDeg (p : PhasePair) : Int := p.midpointDeg - 90

end PhasePair

/-- The exact Figure-5(b) common-edge pair: phases `j=3,6`, scale
`φ-1=φ⁻¹`, and carrier directions `±π/5`. -/
def n10Pair : PhasePair :=
  { order := 10, edgeIndex := 3, scaleLabel := "1/phi" }

/-- The five reflected phase pairs in the standard-orientation order-20
common-edge family.  They use five different polygon scales. -/
def n20Pairs : Array PhasePair :=
  #[ { order := 20, edgeIndex := 5, scaleLabel := "0.1583844403" },
     { order := 20, edgeIndex := 6, scaleLabel := "0.4596495484" },
     { order := 20, edgeIndex := 7, scaleLabel := "0.7159209562" },
     { order := 20, edgeIndex := 8, scaleLabel := "0.9021130326" },
     { order := 20, edgeIndex := 9, scaleLabel := "1" } ]

/-- Hostile convention fixture for the published order-10 motif.  It binds the
CCW edge indices to the reflected partner and the `+36°` unoriented line; a
word-order or screen-orientation change cannot silently alter these numbers. -/
theorem n10_phase_fixture :
    n10Pair.partner = 6 ∧ n10Pair.halfStepDeg = 18 ∧
      n10Pair.midpointDeg = 126 ∧ n10Pair.lineAngleDeg = 36 := by
  decide

/-- The standard-orientation order-20 atlas contains exactly five independent
scale panels. -/
theorem n20_atlas_size_fixture : n20Pairs.size = 5 := by
  decide

/-- Fixture for the bounded-search focus pair: `j=9` reflects to `j=10` and
its two carrier lines have unoriented angle `±81°`. -/
theorem n20_focus_fixture :
    let p := n20Pairs[4]!
    p.order = 20 ∧ p.edgeIndex = 9 ∧ p.partner = 10 ∧
      p.halfStepDeg = 9 ∧ p.midpointDeg = 171 ∧ p.lineAngleDeg = 81 := by
  decide

/-- Exact squared radius of the published order-10 construction. -/
noncomputable def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

noncomputable def n10RadiusSq : ℝ := 4 - goldenRatio

/-- Algebraic core of the order-10 carrier endpoint calculation.  If `φ` is
the golden ratio, `(c,d)` is a unit vector with `2c=φ` (the direction
`ζ₁₀`), and `s=φ-1`, then `s(c,d)` lies on the boundary of the disk centered
at `-1` with squared radius `4-φ`, while it lies strictly nearer the center
`+1`, at squared distance `s²`.  The half-turned endpoint swaps the two disk
roles. -/
theorem n10_carrierEndpoint_contact
    (φ c d : ℝ)
    (hφ : φ^2 = φ + 1)
    (hunit : c^2 + d^2 = 1)
    (hcos : 2 * c = φ) :
    let s := φ - 1
    ((s * c + 1)^2 + (s * d)^2 = 4 - φ) ∧
      ((s * c - 1)^2 + (s * d)^2 = s^2) := by
  dsimp
  constructor <;> nlinarith [hφ, hunit, hcos]

/-- Retrospective order-20 finite-contact square.  This is intentionally named
`contact`, not `critical`: no critical-radius theorem is claimed. -/
noncomputable def n20ContactSquare : ℝ :=
  let t := 2 * Real.cos (Real.pi / 10)
  (-8 : ℝ) + 6 * t + 7 * t^2 - 4 * t^3

end Gallery.TDCSG.CarrierLines
