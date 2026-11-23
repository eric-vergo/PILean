/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean

/-!
# Checks of the enclosures

That the balls of the exact layer hold their numbers, checked exactly (by squaring, or against
values known in closed form), on the inputs where a ball is easiest to get wrong: divisors whose
balls reach 0, circles that nearly coincide or touch, lines through a centre, and balls that do not
shrink. A check passes only on a positive statement: a meeting is `two`, a ball certifies, an
incidence is the one stated.
-/

namespace PILeanTest.Enclosures

open PILean PILean.Exact

/-- `√5` in ℚ(√5). -/
def s5 : QSqrt5 := ⟨0, 1⟩

/-- The point `(x, y)` of ℚ(√5)². -/
def q5 (x y : QSqrt5) : QSqrt5 × QSqrt5 := (x, y)

/-- Two unit circles about `(√5, 0)` and `(√5 + 2⁻⁶⁰, 0)`: their centres' balls overlap until
precision 60, so a division by `|c₂ - c₁|²` at a lower precision divides by a ball that contains
0. -/
def nearCentres : Meeting :=
  circleCircle (q5 s5 ⟨0, 0⟩) (q5 (s5 + ⟨1 / 2 ^ 60, 0⟩) ⟨0, 0⟩) (1 : Rat) (1 : Rat)

/-- Whether a ball holds `√q`, checked by squaring its ends. -/
def holdsSqrt (q : Rat) (b : RatBall) : Bool := sqrtCertified q b

/-- Whether the abscissa and ordinate balls of `p` at the precisions `ks` hold `x` and `y` of
ℚ(√5)² and have radius at most `2⁻ᵏ`. -/
def holdsQ5 (p : Enclosed) (x y : QSqrt5) (ks : List Nat := [8, 20, 40, 70]) : Bool :=
  ks.all fun k =>
    x.certifies (p.re k) && y.certifies (p.im k) && p.meetsPrecision k &&
      (p.re k).radius * 2 ^ k ≤ 1 && (p.im k).radius * 2 ^ k ≤ 1

/-- Whether the abscissa ball of `p` holds `x` of ℚ(√3) at the precisions `ks`. -/
def reHoldsQ3 (p : Enclosed) (x : QSqrt 3) (ks : List Nat := [8, 20, 40]) : Bool :=
  ks.all fun k => x.certifies (p.re k)

/-- Whether the ordinate ball of `p` holds `y` of ℚ(√3) at the precisions `ks`. -/
def imHoldsQ3 (p : Enclosed) (y : QSqrt 3) (ks : List Nat := [8, 20, 40]) : Bool :=
  ks.all fun k => y.certifies (p.im k)

/-- Some balls, those containing 0 among them, for the checks of the ball operations. -/
def balls : List RatBall :=
  [⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩, ⟨2, 1⟩, ⟨-3, 1 / 2⟩, ⟨1 / 3, 1 / 7⟩, ⟨5, 0⟩, ⟨-2, 0⟩]

/-- The ends and the centre of a ball. -/
def samplesOf (b : RatBall) : List Rat := [b.lo, b.centre, b.hi]

/-- The checks of the ball operations: each result holds the results of the operation on the
numbers of its inputs' balls (their ends and centres); `inv` and `div` are undefined, and say so,
on a ball that contains 0. -/
def ballChecks : Array (String × Bool) :=
  #[("ball: a product holds the products of its inputs' numbers",
      balls.all fun a => balls.all fun b =>
        (samplesOf a).all fun x => (samplesOf b).all fun y => (a.mul b).contains (x * y)),
    ("ball: a sum and a difference hold theirs",
      balls.all fun a => balls.all fun b =>
        (samplesOf a).all fun x => (samplesOf b).all fun y =>
          (a.add b).contains (x + y) && (a.sub b).contains (x - y)),
    ("ball: inv is undefined on a ball that contains 0, its end included",
      (RatBall.inv ⟨0, 1⟩).isNone && (RatBall.inv ⟨1, 1⟩).isNone &&
      (RatBall.inv ⟨-1, 1⟩).isNone && (RatBall.inv ⟨0, 0⟩).isNone),
    ("ball: inv holds the reciprocals of its input's numbers",
      balls.all fun b => match b.inv with
        | some r => (samplesOf b).all fun x => r.contains (1 / x)
        | none => b.containsZero),
    ("ball: div is undefined by a ball that contains 0, and holds the quotients otherwise",
      (RatBall.div ⟨1, 0⟩ ⟨0, 1⟩).isNone &&
      balls.all fun a => balls.all fun b => match a.div b with
        | some q => (samplesOf a).all fun x => (samplesOf b).all fun y => q.contains (x / y)
        | none => b.containsZero),
    ("ball: invAbove holds 1/x for the numbers of the ball at least m, though the ball holds 0",
      let b : RatBall := ⟨0, 1⟩
      let r := b.invAbove (1 / 4) (by decide +kernel)
      [1 / 4, 1 / 2, 1].all fun (x : Rat) => r.contains (1 / x)),
    ("ball: the square root holds √⁺ of its input's numbers, a negative end read as 0",
      [(⟨4, 1⟩ : RatBall), ⟨0, 1⟩, ⟨1 / 9, 0⟩, ⟨-1, 1 / 2⟩].all fun b =>
        let r := b.sqrt 20
        (samplesOf b).all fun x =>
          let x := max 0 x
          decide (0 ≤ r.lo) && r.lo * r.lo ≤ x && x ≤ r.hi * r.hi),
    ("ball: roundTo holds the ball it rounds, at a dyadic radius",
      balls.all fun b => [0, 3, 10].all fun bits =>
        let r := b.roundTo bits
        r.contains b.lo && r.contains b.hi &&
          (r.radius * (2 ^ bits : Nat)).den == 1),
    ("ball: exact zero is told from a ball that only holds 0",
      RatBall.isExactZero ⟨0, 0⟩ && !RatBall.isExactZero ⟨0, 1 / 2 ^ 70⟩)]

/-- The checks of refinement: a ball that does not shrink is reported, not passed off as one
of the asked radius. -/
def refineChecks : Array (String × Bool) :=
  let stuck : Nat → RatBall := fun _ => ⟨1, 1⟩
  let shrinking : Nat → RatBall := fun w => ⟨1, 1 / 2 ^ w⟩
  #[("refine: a ball that does not shrink is returned with false, and still holds its number",
      let (b, ok) := refine stuck 10
      !ok && b.contains 0 && b.contains 2),
    ("refine: a ball that shrinks meets the precision",
      (refine shrinking 10).2 && (refine shrinking 10).1.radius * 2 ^ 10 ≤ 1),
    ("refine: an enclosed point says whether it met the precision",
      !(Enclosed.ofBalls stuck shrinking).meetsPrecision 10 &&
      (Enclosed.ofBalls shrinking shrinking).meetsPrecision 10)]

/-- The checks of the constructions on the inputs where a division or a square root would meet
0: each answer is `two`, `tangent`, `apart` or `undecided` as stated, and every ball holds its
point. -/
def meetingChecks : Array (String × Bool) :=
  let zero : Rat := 0
  let one : Rat := 1
  let two : Rat := 2
  let o : Rat × Rat := (zero, zero)
  -- the unit circles about 0 and 1 meet at (1/2, ±√3/2)
  let unitPair := circleCircle o (one, zero) one one
  let phi : QSqrt5 := QSqrt5.phi
  #[("circles: centres 2⁻⁶⁰ apart, decided from balls that hold 0 at low precision",
      match nearCentres with
      | .two p q =>
        -- the points are (√5 + 2⁻⁶¹, ±√(1 - 2⁻¹²²))
        let x : QSqrt5 := ⟨1 / 2 ^ 61, 1⟩
        let y2 : Rat := 1 - 1 / 2 ^ 122
        [8, 20, 40, 70].all fun k =>
          x.certifies (p.re k) && x.certifies (q.re k) && holdsSqrt y2 (p.im k) &&
            holdsSqrt y2 ((q.im k).neg) && p.meetsPrecision k && q.meetsPrecision k
      | _ => false),
    ("circles: the first crossing of the near circles is inside the disk about (√5, 1) of radius \
      1/2",
      match nearCentres with
      | .two p _ => diskIncidence? p (q5 s5 ⟨1, 0⟩) (1 / 2 : Rat) == some .inside
      | _ => false),
    ("circles: unit circles a unit apart cross at (1/2, ±√3/2), the left one first",
      match unitPair with
      | .two p q =>
        reHoldsQ3 p ⟨1 / 2, 0⟩ && imHoldsQ3 p ⟨0, 1 / 2⟩ && reHoldsQ3 q ⟨1 / 2, 0⟩ &&
          imHoldsQ3 q ⟨0, -1 / 2⟩
      | _ => false),
    ("circles: externally tangent rational circles touch at one exact point",
      match circleCircle o (two, zero) one one with
      | .tangent p => (p.re 30).contains 1 && (p.im 30).contains 0
      | _ => false),
    ("circles: tangent circles with irrational radii are undecided, never two points",
      -- radii φ and 2 - φ about centres 2 apart: exactly tangent
      match circleCircle o (two, zero) phi (⟨2, 0⟩ - phi) with
      | .undecided => true
      | _ => false),
    ("circles: far apart, nested and concentric circles are apart; one circle twice undecided",
      (match circleCircle o ((3 : Rat), zero) one one with | .apart => true | _ => false) &&
      (match circleCircle o ((1 / 4 : Rat), zero) (3 : Rat) one with
        | .apart => true | _ => false) &&
      (match circleCircle o o one two with | .apart => true | _ => false) &&
      (match circleCircle o o one one with | .undecided => true | _ => false)),
    ("radii: a zero or negative radius is degenerate for circles and lines, `-1` is not read as \
      `1`, and a disk of such a radius records no incidence",
      let deg := fun (m : Meeting) => match m with | .degenerate => true | _ => false
      deg (circleCircle o (two, zero) (-1 : Rat) one) &&
        deg (circleCircle o (two, zero) one zero) &&
        deg (circleCircle o (two, zero) (SqrtOf.mk (-1 : Rat)) (SqrtOf.mk one)) &&
        deg (lineCircle ((-2 : Rat), zero) (two, zero) o (-1 : Rat)) &&
        deg (lineCircle ((-2 : Rat), zero) (two, zero) o zero) &&
        !(circleCircle o (two, zero) (-1 : Rat) one).decided &&
        diskIncidence? (one, zero) o (-1 : Rat) == none &&
        diskIncidence? (zero, zero) o zero == none &&
        diskIncidence? (one, zero) o one == some .on),
    ("lines: a line through the centre meets the unit circle at (±1, 0), in the line's order",
      match lineCircle ((-2 : Rat), zero) (two, zero) o one with
      | .two p q => (p.re 30).contains (-1) && (q.re 30).contains 1 &&
          (p.im 30).contains 0 && (q.im 30).contains 0
      | _ => false),
    ("lines: a rational tangent touches at one exact point; a line beyond the circle is apart",
      (match lineCircle ((-2 : Rat), one) (two, one) o one with
        | .tangent p => (p.re 30).contains 0 && (p.im 30).contains 1
        | _ => false) &&
      (match lineCircle ((-2 : Rat), two) (two, two) o one with
        | .apart => true | _ => false)),
    ("lines: an irrational tangent and a line through one point twice are undecided",
      -- x + y = 2 touches the circle of radius √2 about 0 at (1, 1)
      (match lineCircle (two, zero) (zero, two) o (SqrtOf.mk two) with
        | .undecided => true | _ => false) &&
      (match lineCircle o o o one with | .undecided => true | _ => false)),
    ("foot: undefined for a line through one point twice; exact otherwise",
      (foot (one, one) o o).isNone &&
      match foot ((3 : Rat), (4 : Rat)) o (one, zero) with
      | some f => (f.re 40).contains 3 && (f.im 40).contains 0 && f.meetsPrecision 40
      | none => false),
    ("foot: from a point of ℚ(√5)² to a line 2⁻⁷⁰ long",
      let a := q5 s5 ⟨0, 0⟩
      let b := q5 (s5 + ⟨1 / 2 ^ 70, 0⟩) ⟨0, 0⟩
      match foot (q5 ⟨3, 0⟩ ⟨1, 0⟩) a b with
      | some f => [10, 40].all fun k =>
          (⟨3, 0⟩ : QSqrt5).certifies (f.re k) && (f.im k).contains 0
      | none => false),
    ("lerp and midpoint: exact rational points",
      let p := lerp o (two, (4 : Rat)) (1 / 4)
      let m := midpoint (one, zero) (zero, one)
      (p.re 20).contains (1 / 2) && (p.im 20).contains 1 && (m.re 20).contains (1 / 2) &&
        (m.im 20).contains (1 / 2) && midpointQ (1, 3) (2, -1) == (3 / 2, 1) &&
        footQ (1, 1) (0, 0) (0, 0) == (0, 0))]

/-- The checks of ℤ[ζ₅]'s equality: the numbers, not the arrays. -/
def zetaChecks : Array (String × Bool) :=
  #[("ζ5: an array of any length is the number it sums to",
      (⟨#[1]⟩ : Zeta5) == Zeta5.ofInt 1 && (⟨#[0, 0, 0, 0, 1]⟩ : Zeta5) == Zeta5.pow 4 &&
      (⟨#[1, 0, 0, 0, 0, 1]⟩ : Zeta5) == Zeta5.ofInt 2 && !((⟨#[1]⟩ : Zeta5) == Zeta5.ofInt 2)),
    ("ζ5: the coefficients and the drawing of an unreduced array are those of its number",
      (⟨#[0, 0, 0, 0, 1]⟩ : Zeta5).coeff 0 == -1 &&
      (PlanePoint.toPoint (⟨#[0, 0, 0, 0, 1]⟩ : Zeta5)).x ==
        (PlanePoint.toPoint (Zeta5.pow 4)).x)]

/-! ### The order and the equality of ℚ(√d)

They are available for a `d` that is not a square and correct there (2 and 5 below); for a square
`d` (0, 1, 4 and 9) and for a negative one they cannot be written, while sums, products and balls
can, and the balls hold their numbers. -/

#guard_msgs (drop info) in
#check_failure (QSqrt.lt (⟨0, -1⟩ : QSqrt 0) ⟨0, 0⟩)
#guard_msgs (drop info) in
#check_failure (QSqrt.le (⟨0, 0⟩ : QSqrt 1) ⟨0, 0⟩)
#guard_msgs (drop info) in
#check_failure (decide ((⟨2, 0⟩ : QSqrt 4) = ⟨0, 1⟩))
#guard_msgs (drop info) in
#check_failure ((⟨3, 0⟩ : QSqrt 9) == ⟨0, 1⟩)
#guard_msgs (drop info) in
#check_failure (QSqrt.nonneg (⟨-1, 1⟩ : QSqrt 4))
#guard_msgs (drop info) in
#check_failure (QSqrt (-1))

/-- 0, 1, 4 and 9 are squares, so none of them has the instance. -/
example : ¬ QSqrt.NonSquare 0 ∧ ¬ QSqrt.NonSquare 1 ∧ ¬ QSqrt.NonSquare 4 ∧
    ¬ QSqrt.NonSquare 9 :=
  ⟨fun h => absurd h.not_square (by decide +kernel),
    fun h => absurd h.not_square (by decide +kernel),
    fun h => absurd h.not_square (by decide +kernel),
    fun h => absurd h.not_square (by decide +kernel)⟩

/-- The checks of ℚ(√d) for square and non-square `d`. -/
def qsqrtChecks : Array (String × Bool) :=
  #[("ℚ(√2): 1 < √2 < 3/2, √2 - 1 > 0, (1, 1) ≠ (2, 0), and order and equality agree",
      QSqrt.lt (⟨1, 0⟩ : QSqrt 2) ⟨0, 1⟩ && QSqrt.lt (⟨0, 1⟩ : QSqrt 2) ⟨3 / 2, 0⟩ &&
        QSqrt.nonneg (⟨-1, 1⟩ : QSqrt 2) && !QSqrt.nonneg (⟨-3 / 2, 1⟩ : QSqrt 2) &&
        (⟨1, 1⟩ : QSqrt 2) != ⟨2, 0⟩ && QSqrt.le (⟨1, 1⟩ : QSqrt 2) ⟨1, 1⟩ &&
        !QSqrt.lt (⟨1, 1⟩ : QSqrt 2) ⟨1, 1⟩),
    ("ℚ(√5): 2 < √5 < 9/4, φ > 1.6, φ² = φ + 1",
      QSqrt.lt (⟨2, 0⟩ : QSqrt5) ⟨0, 1⟩ && QSqrt.lt (⟨0, 1⟩ : QSqrt5) ⟨9 / 4, 0⟩ &&
        QSqrt.lt (⟨8 / 5, 0⟩ : QSqrt5) QSqrt5.phi &&
        QSqrt5.phi * QSqrt5.phi == QSqrt5.phi + ⟨1, 0⟩),
    ("ℚ(√d) for squares d = 0, 1, 4, 9: the balls hold the numbers a + b n",
      #[(0, 0), (1, 1), (4, 2), (9, 3)].all fun ((d : Nat), (n : Nat)) =>
        [8, 30, 64].all fun k =>
          (QSqrt.ball (⟨1 / 3, 2⟩ : QSqrt d) k).contains (1 / 3 + 2 * n) &&
            (⟨1 / 3, 2⟩ : QSqrt d).certifies ⟨1 / 3 + 2 * n, 0⟩)]

/-- The checks. -/
def checks : Array (String × Bool) :=
  ballChecks ++ refineChecks ++ meetingChecks ++ zetaChecks ++ qsqrtChecks

end PILeanTest.Enclosures
