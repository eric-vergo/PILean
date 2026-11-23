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
* `SqrtOf α`: the square root of a real value as a real value (`√(3 + φ)`): the ball of `√x`
  from the ball of `x`, its ends' square roots taken by `sqrtBall` (certified by squaring). Of a
  negative value it is `√⁺x = √(max x 0) = 0`: the square root is total here, and an author who
  needs `x ≥ 0` checks it (exactly, for `QSqrt d`, with `QSqrt.nonneg`).
* `Enclosed`: a point given by its balls at every precision, the result type of constructions
  whose answer leaves the representation: `midpoint`, `lerp`, `foot` (of the perpendicular on a
  line), and the meetings `circleCircle` and `lineCircle` (`Meeting`: two points, a tangent
  point, none, or undecided). They work on any `PlanePoint` values through ball arithmetic, and
  raise the working precision until each ball's radius is at most `2⁻ᵏ` (`refine`;
  `Enclosed.meetsPrecision` says whether it got there). For rational points `midpointQ` and
  `footQ` stay rational.
* **Nothing is made up.** An operation that is not defined on every number of its input's ball
  says so in its result: `RatBall.inv` and `RatBall.div` are `none` on a ball that contains 0.
  A construction that divides first decides, from balls at `signPrecisions`, that the divisor is
  at least some `m > 0` (`positiveBound?`), and at every precision divides by the part of the
  divisor's ball above `m` (`RatBall.invAbove`); it decides the sign under a square root the
  same way. What the balls tried do not decide is `none` (`foot`) or `Meeting.undecided`, never a
  guess.

The core library has no real numbers: that the balls of these types hold their values is what
the code computes and what the tests check exactly; it is not a theorem here.

## Main definitions

* `QSqrt`, `QSqrt5`, `Zeta5`, `Zeta5.normalForm`, `SqrtOf`, `Enclosed`, `Meeting`.
* `RatBall.inv`, `RatBall.div` (partial), `RatBall.invAbove`, `RatBall.sqrt` (of `max x 0`),
  `RatBall.roundTo`, `positiveBound?`, `decidedNegative`, `refine`.
* `midpoint`, `lerp`, `foot`, `circleCircle`, `lineCircle`, `midpointQ`, `footQ`.
-/

namespace PILean.Exact

/-! ### Balls -/

namespace RatBall

/-- The ball of `1 / x` for every `x` in the ball, from the reciprocals of its ends; `none` when
the ball contains 0, where `1 / x` is undefined or unbounded. -/
def inv (b : RatBall) : Option RatBall :=
  if b.lo > 0 || b.hi < 0 then some (ofBounds (1 / b.hi) (1 / b.lo)) else none

/-- The ball of `a / b` for every quotient of numbers in the two balls; `none` when the divisor's
ball contains 0 (`inv`). -/
def div (a b : RatBall) : Option RatBall := b.inv.map a.mul

/-- The ball of `1 / x` for the numbers `x` of the ball that are at least `m > 0`: the ball's part
below `m` is left out first. A construction uses it for a number it has decided, from another
enclosure, to be at least `m`, so the result holds `1 / x` even when the ball itself reaches 0. -/
def invAbove (b : RatBall) (m : Rat) (_ : 0 < m) : RatBall :=
  ofBounds (1 / max b.hi m) (1 / max b.lo m)

/-- The ball of `√⁺x = √(max x 0)` for every `x` in the ball: from the square root of its lower
end (rounded down) to that of its upper end (rounded up), a negative end read as 0. The square
root of a negative number is not defined; the constructions here take it only of numbers decided
to be positive, where `√⁺` is the square root. -/
def sqrt (b : RatBall) (k : Nat) : RatBall :=
  ofBounds (sqrtBall (max 0 b.lo) k).lo (sqrtBall (max 0 b.hi) k).hi

/-- Whether the ball contains 0. -/
def containsZero (b : RatBall) : Bool := b.lo ≤ 0 && 0 ≤ b.hi

/-- Whether the ball is the number 0 itself (centre and radius 0), as exact data gives it. -/
def isExactZero (b : RatBall) : Bool := b.centre == 0 && b.radius == 0

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

/-- The precisions at which a construction tries to decide a sign: `64, 128, 256, 512`. -/
def signPrecisions : List Nat := [64, 128, 256, 512]

/-- A positive lower bound of the number the balls `f k` enclose: the lower end of the ball at
the first of `signPrecisions` where it is positive; `none` when no ball tried lies above 0. -/
def positiveBound? (f : Nat → RatBall) : Option { m : Rat // 0 < m } :=
  signPrecisions.findSome? fun k =>
    let lo := (f k).lo
    if h : 0 < lo then some ⟨lo, h⟩ else none

/-- Whether the number the balls `f k` enclose is decided to be negative: the ball at one of
`signPrecisions` lies below 0. -/
def decidedNegative (f : Nat → RatBall) : Bool := signPrecisions.any fun k => (f k).hi < 0

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

/-- An element of ℤ[ζ₅], `ζ = e^{2πi/5}`, by integer coefficients of `1, ζ, ζ², …`: an array of
any length stands for the element it sums to (`ζ⁵ = 1`, `ζ⁴ = -1 - ζ - ζ² - ζ³`), and every
operation and the equality read it through its normal form (`Zeta5.normalForm`), the coefficients
`c₀, c₁, c₂, c₃` of `c₀ + c₁ ζ + c₂ ζ² + c₃ ζ³`. -/
structure Zeta5 where
  /-- The coefficients of `1, ζ, ζ², …` (missing ones are 0). -/
  c : Array Int
  deriving Repr, Inhabited

namespace Zeta5

/-- The coefficients of `cs` (any length) in the basis `1, ζ, ζ², ζ³`: indices taken modulo 5,
then `ζ⁴` replaced by `-1 - ζ - ζ² - ζ³`. Always four coefficients. -/
def normalForm (cs : Array Int) : Array Int := Id.run do
  let mut r : Array Int := #[0, 0, 0, 0, 0]
  for i in [0:cs.size] do
    r := r.modify (i % 5) (· + cs[i]!)
  let c4 := r[4]!
  return #[r[0]! - c4, r[1]! - c4, r[2]! - c4, r[3]! - c4]

/-- Coefficient `i` (of `1, ζ, ζ², ζ³`) of the element's normal form, whatever the length of its
array; 0 for `i ≥ 4`. -/
def coeff (z : Zeta5) (i : Nat) : Int := (normalForm z.c).getD i 0

/-- Two elements are equal when their normal forms are: the equality of the numbers, not of the
arrays (`⟨#[1]⟩ == ⟨#[1, 0, 0, 0]⟩` and `⟨#[0, 0, 0, 0, 1]⟩ == ⟨#[-1, -1, -1, -1]⟩`). -/
instance : BEq Zeta5 := ⟨fun x y => normalForm x.c == normalForm y.c⟩

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

/-- The element with coefficients `cs` of `1, ζ, …, ζⁿ⁻¹` (any length), in normal form. -/
def reduce (cs : Array Int) : Zeta5 := ⟨normalForm cs⟩

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

/-- The square root `√⁺x = √(max x 0)` of a real value (see the module docstring). -/
structure SqrtOf (α : Type) where
  /-- The value under the root. -/
  radicand : α

/-- The ball of `√x` at precision `k`: the ball of `x` at precision `2k + 4`, its ends' square
roots at precision `k + 1`. -/
instance {α : Type} [RealValue α] : RealValue (SqrtOf α) where
  ball s k := (RealValue.ball s.radicand (2 * k + 4)).sqrt (k + 1)

/-- A point given by its balls at every precision `k`, and whether each reached its precision
(`meetsPrecision k`: both radii at most `2⁻ᵏ`). Every ball the constructions here make holds the
point for inputs whose balls hold theirs; a ball that did not reach its precision (inputs whose
balls do not shrink) is wider than asked, and `meetsPrecision` says so. -/
structure Enclosed where
  /-- The ball of the abscissa at precision `k`. -/
  re : Nat → RatBall
  /-- The ball of the ordinate at precision `k`. -/
  im : Nat → RatBall
  /-- Whether both balls at precision `k` have radius at most `2⁻ᵏ`. -/
  meetsPrecision : Nat → Bool := fun _ => true

instance : Inhabited Enclosed := ⟨⟨fun _ => ⟨0, 0⟩, fun _ => ⟨0, 0⟩, fun _ => true⟩⟩

/-- An enclosed point is a point. It has no `LawfulPlanePoint` instance: a ball may miss its
precision (`Enclosed.meetsPrecision`). -/
instance : PlanePoint Enclosed where
  re e k := e.re k
  im e k := e.im k

/-- The ball `f w` at the least working precision `w = k, k + 8, k + 16, …` (at most 64 tries)
whose radius is at most `2⁻⁽ᵏ⁺¹⁾`, made dyadic at `k + 2` bits (`RatBall.roundTo`, so its radius is
at most `2⁻ᵏ`), with `true`; when none reaches it, the last ball tried, made dyadic, with `false`.
Either ball contains every ball `f w` it was made from. -/
def refine (f : Nat → RatBall) (k : Nat) : RatBall × Bool := Id.run do
  let mut w := k
  let mut b := f k
  for _ in [0:64] do
    if b.radius * 2 ^ (k + 1) ≤ 1 then return (b.roundTo (k + 2), true)
    w := w + 8
    b := f w
  return (b.roundTo (k + 2), false)

/-- An enclosed point from functions of the working precision, refined (`refine`). -/
def Enclosed.ofBalls (re im : Nat → RatBall) : Enclosed :=
  ⟨fun k => (refine re k).1, fun k => (refine im k).1,
    fun k => (refine re k).2 && (refine im k).2⟩

/-- Where two curves meet, as far as the balls of their data decide it (at `signPrecisions`): in
two points (in the order the construction states), in one point (tangency, decided only for exact
data, where the deciding number is the exact 0), in none (`apart`), or `undecided` (the balls
tried do not separate the deciding number from 0, as for curves too near tangency, a line through
two points not decided to differ, or circles about centres not decided to differ unless their
radii are decided to differ). -/
inductive Meeting where
  /-- Two points. -/
  | two (first second : Enclosed)
  /-- One point: the curves touch. -/
  | tangent (point : Enclosed)
  /-- No common point. -/
  | apart
  /-- Not decided. -/
  | undecided
  deriving Inhabited

/-- The points of a meeting: two, one, or none (for `apart` and `undecided`). -/
def Meeting.points : Meeting → Array Enclosed
  | .two p q => #[p, q]
  | .tangent p => #[p]
  | _ => #[]

/-- The two points of a meeting in two points. -/
def Meeting.two? : Meeting → Option (Enclosed × Enclosed)
  | .two p q => some (p, q)
  | _ => none

/-- Whether the meeting is decided (anything but `undecided`). -/
def Meeting.decided : Meeting → Bool
  | .undecided => false
  | _ => true

variable {α β : Type} [PlanePoint α] [PlanePoint β]

/-- The point `a + t (b - a)` for a rational `t`. -/
def lerp (a b : α) (t : Rat) : Enclosed :=
  .ofBalls (fun k => (PlanePoint.re a k).add (((PlanePoint.re b k).sub (PlanePoint.re a k)).smul t))
    (fun k => (PlanePoint.im a k).add (((PlanePoint.im b k).sub (PlanePoint.im a k)).smul t))

/-- The midpoint of two points. -/
def midpoint (a b : α) : Enclosed := lerp a b (1 / 2)

/-- The foot of the perpendicular from `p` to the line through `a` and `b`; `none` when `|b - a|²`
is not decided to be positive (`positiveBound?`: `a = b`, or too near to be told apart). -/
def foot (p : β) (a b : α) : Option Enclosed :=
  let parts := fun (k : Nat) =>
    let ax := PlanePoint.re a k
    let ay := PlanePoint.im a k
    let dx := (PlanePoint.re b k).sub ax
    let dy := (PlanePoint.im b k).sub ay
    let px := (PlanePoint.re p k).sub ax
    let py := (PlanePoint.im p k).sub ay
    (ax, ay, dx, dy, (px.mul dx).add (py.mul dy), (dx.mul dx).add (dy.mul dy))
  match positiveBound? fun k => (parts k).2.2.2.2.2 with
  | none => none
  | some ⟨m, hm⟩ =>
    let t := fun (k : Nat) => let (_, _, _, _, num, n) := parts k; num.mul (n.invAbove m hm)
    some (.ofBalls (fun k => let (ax, _, dx, _, _, _) := parts k; ax.add (dx.mul (t k)))
      (fun k => let (_, ay, _, dy, _, _) := parts k; ay.add (dy.mul (t k))))

/-- Where the circles `(c₁, r₁)` and `(c₂, r₂)` meet (`Meeting`): two points, the one on the left
of the direction from `c₁` to `c₂` first, when `|c₂ - c₁|²` and the squared half chord are decided
to be positive; `apart` when the squared half chord is decided negative, or the centres are
exactly equal and the radii decided to differ; `tangent` when the squared half chord is exactly 0. -/
def circleCircle {γ : Type} [RealValue γ] (c₁ c₂ : α) (r₁ r₂ : γ) : Meeting :=
  let base := fun (k : Nat) =>
    let x1 := PlanePoint.re c₁ k
    let y1 := PlanePoint.im c₁ k
    let vx := (PlanePoint.re c₂ k).sub x1
    let vy := (PlanePoint.im c₂ k).sub y1
    let d2 := (vx.mul vx).add (vy.mul vy)
    let s1 := (RealValue.ball r₁ k).mul (RealValue.ball r₁ k)
    let s2 := (RealValue.ball r₂ k).mul (RealValue.ball r₂ k)
    (x1, y1, vx, vy, d2, s1, s2)
  let d2At := fun (k : Nat) => (base k).2.2.2.2.1
  match positiveBound? d2At with
  | none =>
    let diff := fun (k : Nat) => let (_, _, _, _, _, s1, s2) := base k; s1.sub s2
    if (d2At 64).isExactZero && ((positiveBound? diff).isSome || decidedNegative diff) then .apart
    else .undecided
  | some ⟨m, hm⟩ =>
    -- the fraction of the way along `v` of the chord's foot, and the squared half chord over
    -- `|v|²`, with `1 / |v|²` from the part of its ball above `m`
    let parts := fun (k : Nat) =>
      let (x1, y1, vx, vy, d2, s1, s2) := base k
      let inv := d2.invAbove m hm
      let a := (((d2.add s1).sub s2).mul inv).smul (1 / 2)
      (x1, y1, vx, vy, a, (s1.mul inv).sub (a.mul a))
    let h2At := fun (k : Nat) => (parts k).2.2.2.2.2
    let point := fun (side : Rat) => Enclosed.ofBalls
      (fun k => let (x1, _, vx, vy, a, h2) := parts (k + 32)
        (x1.add (vx.mul a)).sub ((vy.mul (h2.sqrt (k + 32))).smul side))
      (fun k => let (_, y1, vx, vy, a, h2) := parts (k + 32)
        (y1.add (vy.mul a)).add ((vx.mul (h2.sqrt (k + 32))).smul side))
    if (positiveBound? h2At).isSome then .two (point 1) (point (-1))
    else if decidedNegative h2At then .apart
    else if (h2At 64).isExactZero then .tangent (point 0)
    else .undecided

/-- Where the line through `a` and `b` meets the circle `(c, r)` (`Meeting`): two points in the
order of the line's direction when `|b - a|²` and the discriminant are decided to be positive;
`apart` when the discriminant is decided negative; `tangent` when it is exactly 0; `undecided`
otherwise, and when `a` and `b` are not decided to differ. -/
def lineCircle {γ : Type} [RealValue γ] (a b c : α) (r : γ) : Meeting :=
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
  match positiveBound? fun k => (parts k).2.2.2.2.1 with
  | none => .undecided
  | some ⟨m, hm⟩ =>
    let discAt := fun (k : Nat) => (parts k).2.2.2.2.2.2
    let point := fun (side : Rat) =>
      let t := fun (k : Nat) => let (_, _, _, _, qa, qb, disc) := parts (k + 32)
        ((qb.neg).add ((disc.sqrt (k + 32)).smul side)).mul
          ((qa.smul 2).invAbove (2 * m) (by
            have h2 : (0 : Rat) < 2 := by decide
            exact Rat.mul_pos h2 hm))
      Enclosed.ofBalls
        (fun k => let (ax, _, dx, _, _, _, _) := parts (k + 32); ax.add (dx.mul (t k)))
        (fun k => let (_, ay, _, dy, _, _, _) := parts (k + 32); ay.add (dy.mul (t k)))
    if (positiveBound? discAt).isSome then .two (point (-1)) (point 1)
    else if decidedNegative discAt then .apart
    else if (discAt 64).isExactZero then .tangent (point 0)
    else .undecided

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
