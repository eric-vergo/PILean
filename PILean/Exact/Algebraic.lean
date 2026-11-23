/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Exact.Plane

/-!
# Exact algebraic numbers for plane figures

Representations of exact numbers that plane figures often need, with the instances of
`Exact.RealValue` and `Exact.PlanePoint` that turn them into rational balls, and constructions on
exact points:

* `QSqrt d`: the numbers `a + b √d` of the field ℚ(√d) (`d` a natural number that is not a square),
  with sums, products, conjugates (`a - b √d`), norms (`a² - d b²`), exact signs and order, and
  balls from `sqrtBall` (`QSqrt5`, with `QSqrt5.phi`, the golden ratio). That a ball holds its
  number can be checked exactly by squaring (`QSqrt.certifies`).
* `Zeta5`: the ring ℤ[ζ₅] (`ζ₅ = e^{2πi/5}`) as four integer coefficients in the basis
  `1, ζ, ζ², ζ³`, with sums, products (reduced by `ζ⁴ = -1 - ζ - ζ² - ζ³`), the conjugate
  (`ζʲ ↦ ζ⁻ʲ`), the real part and `|z|²` in ℚ(√5), and balls for the real part (in ℚ(√5)) and the
  imaginary part (from `sin 72° = √(10 + 2√5) / 4` and `sin 144° = √(10 - 2√5) / 4`).
* `SqrtOf α`: the square root of a non-negative real value as a real value (`√(3 + φ)`): the ball
  of `√x` from the ball of `x`, its ends' square roots taken by `sqrtBall` (certified by squaring).
* `Enclosed`: a point given by its balls at every precision, the result type of constructions
  whose answer leaves the representation: `midpoint`, `lerp`, `foot` (of the perpendicular on a
  line), `circleCircle` and `lineCircle` (intersections). They work on any `PlanePoint` values
  through ball arithmetic, raising the working precision until each ball's radius is at most
  `2⁻ᵏ` (`Enclosed.refine`); for rational points `midpointQ` and `footQ` stay rational.

The core library has no real numbers: that the balls of these types hold their values is what
the code computes and what the tests check exactly; it is not a theorem here.

## Main definitions

* `QSqrt`, `QSqrt5`, `Zeta5`, `SqrtOf`, `Enclosed`.
* `RatBall.inv`, `RatBall.div`, `RatBall.sqrt`.
* `midpoint`, `lerp`, `foot`, `circleCircle`, `lineCircle`, `midpointQ`, `footQ`.
-/

namespace PILean.Exact

/-! ### Balls -/

namespace RatBall

/-- The ball of `1 / x` for a ball that does not contain 0 (one of its ends' reciprocals as
centre, half their difference as radius); the ball `0 ± ∞`-free fallback `⟨0, 0⟩` when it
contains 0. -/
def inv (b : RatBall) : RatBall :=
  if b.lo > 0 || b.hi < 0 then ofBounds (1 / b.hi) (1 / b.lo) else ⟨0, 0⟩

/-- The ball of a quotient (by a ball that does not contain 0). -/
def div (a b : RatBall) : RatBall := a.mul b.inv

/-- The ball of `√x` at precision `k` for `x` in the ball (its negative part left out): from the
square root of its lower end (rounded down) to that of its upper end (rounded up). -/
def sqrt (b : RatBall) (k : Nat) : RatBall :=
  ofBounds (sqrtBall (max 0 b.lo) k).lo (sqrtBall (max 0 b.hi) k).hi

/-- Whether the ball contains 0. -/
def containsZero (b : RatBall) : Bool := b.lo ≤ 0 && 0 ≤ b.hi

/-- A ball with a dyadic centre and radius (multiples of `2⁻ᵇⁱᵗˢ`) that contains the ball: the
centre rounded down, the radius rounded up and widened by one step. Its numbers stay small, so
they convert to `Float` (a ball computed through quotients can have numerators and denominators
too large for `Float`). -/
def roundTo (b : RatBall) (bits : Nat) : RatBall :=
  let s : Rat := (2 ^ bits : Nat)
  let c : Rat := ((b.centre * s).floor : Int)
  let r : Rat := ((b.radius * s).ceil : Int)
  ⟨c / s, (r + 1) / s⟩

end RatBall

/-- The bits needed above `|q|`: `log₂ ⌈|q|⌉ + 1`. -/
def bitsAbove (q : Rat) : Nat := ((RatBall.absQ q).ceil.toNat).log2 + 1

/-! ### The fields ℚ(√d) -/

/-- The number `a + b √d`. -/
structure QSqrt (d : Nat) where
  /-- The rational part. -/
  a : Rat
  /-- The coefficient of `√d`. -/
  b : Rat := 0
  deriving BEq, DecidableEq, Repr, Inhabited

/-- The numbers of ℚ(√5). -/
abbrev QSqrt5 := QSqrt 5

namespace QSqrt

variable {d : Nat}

/-- A rational as a number of ℚ(√d). -/
def ofRat (q : Rat) : QSqrt d := ⟨q, 0⟩

/-- The sum. -/
def add (x y : QSqrt d) : QSqrt d := ⟨x.a + y.a, x.b + y.b⟩

/-- The negation. -/
def neg (x : QSqrt d) : QSqrt d := ⟨-x.a, -x.b⟩

/-- The difference. -/
def sub (x y : QSqrt d) : QSqrt d := ⟨x.a - y.a, x.b - y.b⟩

/-- The product: `(a + b√d)(c + e√d) = (ac + d be) + (ae + bc)√d`. -/
def mul (x y : QSqrt d) : QSqrt d := ⟨x.a * y.a + d * x.b * y.b, x.a * y.b + x.b * y.a⟩

/-- The conjugate `a - b √d`. -/
def conj (x : QSqrt d) : QSqrt d := ⟨x.a, -x.b⟩

/-- The norm `a² - d b²`, the product of the number and its conjugate. -/
def norm (x : QSqrt d) : Rat := x.a * x.a - d * x.b * x.b

instance : Add (QSqrt d) := ⟨add⟩
instance : Sub (QSqrt d) := ⟨sub⟩
instance : Neg (QSqrt d) := ⟨neg⟩
instance : Mul (QSqrt d) := ⟨mul⟩

/-- Whether `a + b √d ≥ 0`, decided exactly: by the signs of `a` and `b` and, when they differ, by
comparing `a²` with `d b²`. -/
def nonneg (x : QSqrt d) : Bool :=
  if x.a ≥ 0 && x.b ≥ 0 then true
  else if x.a ≤ 0 && x.b ≤ 0 then x.a == 0 && x.b == 0
  else if x.a > 0 then x.a * x.a ≥ d * x.b * x.b
  else d * x.b * x.b ≥ x.a * x.a

/-- Whether `x ≤ y`, exactly. -/
def le (x y : QSqrt d) : Bool := nonneg (sub y x)

/-- The ball at precision `k`: `a + b · sqrtBall d k'` with `k'` large enough that `|b|` times
the radius of the ball of `√d` is at most `2⁻ᵏ`. -/
def ball (x : QSqrt d) (k : Nat) : RatBall :=
  ((sqrtBall d (k + bitsAbove x.b + 1)).smul x.b).add ⟨x.a, 0⟩

/-- Whether a ball holds `a + b √d`, checked exactly: with `t = (v - a) / b` for each end `v`, the
lower end's `t` is at most `√d` and the upper end's at least `√d` (reversed for `b < 0`), each
decided by squaring; for `b = 0` the ball holds `a`. -/
def certifies (x : QSqrt d) (r : RatBall) : Bool :=
  let belowRoot := fun (t : Rat) => t ≤ 0 || t * t ≤ d
  let aboveRoot := fun (t : Rat) => t ≥ 0 && t * t ≥ d
  if x.b == 0 then r.contains x.a
  else
    let tl := (r.lo - x.a) / x.b
    let th := (r.hi - x.a) / x.b
    if x.b > 0 then belowRoot tl && aboveRoot th else belowRoot th && aboveRoot tl

end QSqrt

/-- The golden ratio `φ = (1 + √5) / 2`. -/
def QSqrt5.phi : QSqrt5 := ⟨1 / 2, 1 / 2⟩

/-- A number of ℚ(√d) as a real value. -/
instance {d : Nat} : RealValue (QSqrt d) where
  ball := QSqrt.ball

/-- A pair of numbers of ℚ(√d) as a point. -/
instance {d : Nat} : PlanePoint (QSqrt d × QSqrt d) where
  re p k := QSqrt.ball p.1 k
  im p k := QSqrt.ball p.2 k

/-! ### The ring ℤ[ζ₅] -/

/-- An element `c₀ + c₁ ζ + c₂ ζ² + c₃ ζ³` of ℤ[ζ₅], `ζ = e^{2πi/5}` (missing coefficients are
0). -/
structure Zeta5 where
  /-- The coefficients in the basis `1, ζ, ζ², ζ³`. -/
  c : Array Int
  deriving BEq, Repr, Inhabited

namespace Zeta5

/-- Coefficient `i`. -/
def coeff (z : Zeta5) (i : Nat) : Int := z.c.getD i 0

/-- `0`. -/
def zero : Zeta5 := ⟨#[0, 0, 0, 0]⟩

/-- An integer. -/
def ofInt (n : Int) : Zeta5 := ⟨#[n, 0, 0, 0]⟩

/-- The sum. -/
def add (x y : Zeta5) : Zeta5 := ⟨(List.range 4).toArray.map fun i => x.coeff i + y.coeff i⟩

/-- The negation. -/
def neg (x : Zeta5) : Zeta5 := ⟨(List.range 4).toArray.map fun i => -x.coeff i⟩

/-- The difference. -/
def sub (x y : Zeta5) : Zeta5 := x.add y.neg

/-- The element with coefficients `c` in `1, ζ, …, ζⁿ⁻¹` (any length) reduced to the basis by
`ζ⁵ = 1` and `ζ⁴ = -1 - ζ - ζ² - ζ³`. -/
def reduce (cs : Array Int) : Zeta5 := Id.run do
  let mut r : Array Int := #[0, 0, 0, 0, 0]
  for i in [0:cs.size] do
    r := r.modify (i % 5) (· + cs[i]!)
  let c4 := r[4]!
  return ⟨#[r[0]! - c4, r[1]! - c4, r[2]! - c4, r[3]! - c4]⟩

/-- The product. -/
def mul (x y : Zeta5) : Zeta5 :=
  reduce ((List.range 7).toArray.map fun k =>
    (List.range 4).foldl (fun s i => if k ≥ i && k - i < 4 then s + x.coeff i * y.coeff (k - i)
      else s) 0)

instance : Add Zeta5 := ⟨add⟩
instance : Sub Zeta5 := ⟨sub⟩
instance : Neg Zeta5 := ⟨neg⟩
instance : Mul Zeta5 := ⟨mul⟩

/-- `ζʲ`: `ζ⁴ = -1 - ζ - ζ² - ζ³`, and `ζ⁵ = 1`. -/
def pow (j : Nat) : Zeta5 :=
  match j % 5 with
  | 0 => ⟨#[1, 0, 0, 0]⟩
  | 1 => ⟨#[0, 1, 0, 0]⟩
  | 2 => ⟨#[0, 0, 1, 0]⟩
  | 3 => ⟨#[0, 0, 0, 1]⟩
  | _ => ⟨#[-1, -1, -1, -1]⟩

/-- The complex conjugate: `ζʲ ↦ ζ⁻ʲ = ζ⁵⁻ʲ`. -/
def conj (z : Zeta5) : Zeta5 :=
  reduce #[z.coeff 0, 0, z.coeff 3, z.coeff 2, z.coeff 1]

/-- The real part, in ℚ(√5): `cos 72° = (√5 - 1)/4`, `cos 144° = cos 216° = -(1 + √5)/4`. -/
def realPart (z : Zeta5) : QSqrt5 :=
  let c1 : Rat := z.coeff 1
  let c23 : Rat := z.coeff 2 + z.coeff 3
  ⟨z.coeff 0 - c1 / 4 - c23 / 4, c1 / 4 - c23 / 4⟩

/-- `|z|² = z · z̄`, a real element, in ℚ(√5). -/
def normSq (z : Zeta5) : QSqrt5 := (z.mul z.conj).realPart

/-- A ball around `sin 72° = √(10 + 2√5) / 4` (`plus`) or `sin 144° = √(10 - 2√5) / 4`. -/
def sinBall (plus : Bool) (k : Nat) : RatBall :=
  ((QSqrt.ball (⟨10, if plus then 2 else -2⟩ : QSqrt5) (k + 2)).sqrt (k + 2)).smul (1 / 4)

/-- The imaginary part's ball: `c₁ sin 72° + (c₂ - c₃) sin 144°`, at a precision raised by the
size of the coefficients. -/
def imBall (z : Zeta5) (k : Nat) : RatBall :=
  let c1 : Rat := z.coeff 1
  let d : Rat := z.coeff 2 - z.coeff 3
  let k' := k + bitsAbove c1 + bitsAbove d + 2
  ((sinBall true k').smul c1).add ((sinBall false k').smul d)

end Zeta5

/-- An element of ℤ[ζ₅] as a point of the complex plane. -/
instance : PlanePoint Zeta5 where
  re z k := QSqrt.ball z.realPart k
  im z k := Zeta5.imBall z k

/-! ### Square roots and enclosed points -/

/-- The square root of a non-negative real value (see the module docstring). -/
structure SqrtOf (α : Type) where
  /-- The value under the root. -/
  radicand : α

/-- The ball of `√x` at precision `k`: the ball of `x` at precision `2k + 4`, its ends' square
roots at precision `k + 1`. -/
instance {α : Type} [RealValue α] : RealValue (SqrtOf α) where
  ball s k := (RealValue.ball s.radicand (2 * k + 4)).sqrt (k + 1)

/-- A point given by its balls at every precision. -/
structure Enclosed where
  /-- The ball of the abscissa at precision `k`. -/
  re : Nat → RatBall
  /-- The ball of the ordinate at precision `k`. -/
  im : Nat → RatBall

instance : Inhabited Enclosed := ⟨⟨fun _ => ⟨0, 0⟩, fun _ => ⟨0, 0⟩⟩⟩

/-- An enclosed point is a point. -/
instance : PlanePoint Enclosed where
  re e k := e.re k
  im e k := e.im k

/-- The ball `f w` at the least working precision `w = k, k + 8, k + 16, …` (at most 64 tries)
whose radius is at most `2⁻⁽ᵏ⁺¹⁾`, made dyadic at `k + 2` bits (`RatBall.roundTo`, so its radius is
at most `2⁻ᵏ`), or the last tried. -/
def refine (f : Nat → RatBall) (k : Nat) : RatBall := Id.run do
  let mut w := k
  let mut b := f k
  for _ in [0:64] do
    if b.radius * 2 ^ (k + 1) ≤ 1 then return b.roundTo (k + 2)
    w := w + 8
    b := f w
  return b.roundTo (k + 2)

/-- An enclosed point from functions of the working precision, refined (`refine`). -/
def Enclosed.ofBalls (re im : Nat → RatBall) : Enclosed :=
  ⟨refine re, refine im⟩

variable {α β : Type} [PlanePoint α] [PlanePoint β]

/-- The point `a + t (b - a)` for a rational `t`. -/
def lerp (a b : α) (t : Rat) : Enclosed :=
  .ofBalls (fun k => (PlanePoint.re a k).add (((PlanePoint.re b k).sub (PlanePoint.re a k)).smul t))
    (fun k => (PlanePoint.im a k).add (((PlanePoint.im b k).sub (PlanePoint.im a k)).smul t))

/-- The midpoint of two points. -/
def midpoint (a b : α) : Enclosed := lerp a b (1 / 2)

/-- The foot of the perpendicular from `p` to the line through `a` and `b` (`a ≠ b`). -/
def foot (p : β) (a b : α) : Enclosed :=
  let t := fun (k : Nat) =>
    let ax := PlanePoint.re a k
    let ay := PlanePoint.im a k
    let dx := (PlanePoint.re b k).sub ax
    let dy := (PlanePoint.im b k).sub ay
    let px := (PlanePoint.re p k).sub ax
    let py := (PlanePoint.im p k).sub ay
    ((px.mul dx).add (py.mul dy)).div ((dx.mul dx).add (dy.mul dy))
  .ofBalls (fun k => (PlanePoint.re a k).add (((PlanePoint.re b k).sub (PlanePoint.re a k)).mul
      (t k)))
    (fun k => (PlanePoint.im a k).add (((PlanePoint.im b k).sub (PlanePoint.im a k)).mul (t k)))

/-- The two points where the circles `(c₁, r₁)` and `(c₂, r₂)` meet, the one on the left of the
direction from `c₁` to `c₂` first; `none` when the circles are decided (at the working precision
`k + 32`) not to meet in two points, or their centres not to differ. -/
def circleCircle {γ : Type} [RealValue γ] (c₁ c₂ : α) (r₁ r₂ : γ) :
    Option (Enclosed × Enclosed) :=
  let parts := fun (k : Nat) =>
    let x1 := PlanePoint.re c₁ k
    let y1 := PlanePoint.im c₁ k
    let vx := (PlanePoint.re c₂ k).sub x1
    let vy := (PlanePoint.im c₂ k).sub y1
    let d2 := (vx.mul vx).add (vy.mul vy)
    let s1 := (RealValue.ball r₁ k).mul (RealValue.ball r₁ k)
    let s2 := (RealValue.ball r₂ k).mul (RealValue.ball r₂ k)
    -- the fraction of the way along `v` of the chord's foot, and the half chord over |v|
    let a := ((d2.add s1).sub s2).div (d2.smul 2)
    let h2 := (s1.div d2).sub (a.mul a)
    (x1, y1, vx, vy, d2, a, h2)
  let (_, _, _, _, d2, _, h2) := parts 64
  if d2.containsZero || h2.hi ≤ 0 then none
  else
    let point := fun (side : Rat) => Enclosed.ofBalls
      (fun k => let (x1, _, vx, vy, _, a, h2) := parts (k + 32)
        (x1.add (vx.mul a)).sub ((vy.mul (h2.sqrt (k + 32))).smul side))
      (fun k => let (_, y1, vx, vy, _, a, h2) := parts (k + 32)
        (y1.add (vy.mul a)).add ((vx.mul (h2.sqrt (k + 32))).smul side))
    some (point 1, point (-1))

/-- The points where the line through `a` and `b` meets the circle `(c, r)`, in the order of the
line's direction; `none` when they are decided (at the working precision 64) not to meet in two
points or `a = b`. -/
def lineCircle {γ : Type} [RealValue γ] (a b c : α) (r : γ) : Option (Enclosed × Enclosed) :=
  let parts := fun (k : Nat) =>
    let ax := PlanePoint.re a k
    let ay := PlanePoint.im a k
    let dx := (PlanePoint.re b k).sub ax
    let dy := (PlanePoint.im b k).sub ay
    let fx := ax.sub (PlanePoint.re c k)
    let fy := ay.sub (PlanePoint.im c k)
    let qa := (dx.mul dx).add (dy.mul dy)
    let qb := ((fx.mul dx).add (fy.mul dy)).smul 2
    let qc := ((fx.mul fx).add (fy.mul fy)).sub ((RealValue.ball r k).mul (RealValue.ball r k))
    let disc := (qb.mul qb).sub ((qa.mul qc).smul 4)
    (ax, ay, dx, dy, qa, qb, disc)
  let (_, _, _, _, qa, _, disc) := parts 64
  if qa.containsZero || disc.hi ≤ 0 then none
  else
    let point := fun (side : Rat) =>
      let t := fun (k : Nat) => let (_, _, _, _, qa, qb, disc) := parts (k + 32)
        ((qb.neg).add ((disc.sqrt (k + 32)).smul side)).div (qa.smul 2)
      Enclosed.ofBalls
        (fun k => let (ax, _, dx, _, _, _, _) := parts (k + 32); ax.add (dx.mul (t k)))
        (fun k => let (_, ay, _, dy, _, _, _) := parts (k + 32); ay.add (dy.mul (t k)))
    some (point (-1), point 1)

/-- The midpoint of two rational points, rational. -/
def midpointQ (a b : Rat × Rat) : Rat × Rat := ((a.1 + b.1) / 2, (a.2 + b.2) / 2)

/-- The foot of the perpendicular from a rational point to the line through two rational points,
rational (`a` itself when `a = b`). -/
def footQ (p a b : Rat × Rat) : Rat × Rat :=
  let dx := b.1 - a.1
  let dy := b.2 - a.2
  let n := dx * dx + dy * dy
  if n == 0 then a
  else
    let t := ((p.1 - a.1) * dx + (p.2 - a.2) * dy) / n
    (a.1 + t * dx, a.2 + t * dy)

/-- The midpoint of `(0, 0)` and `(1, 2)` is `(1/2, 1)`. -/
example : midpointQ (0, 0) (1, 2) = (1 / 2, 1) := by decide +kernel

end PILean.Exact
