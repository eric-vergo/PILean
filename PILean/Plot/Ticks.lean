/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# Axis ticks

Tick positions chosen by a nice-numbers rule and their labels.

## Main definitions

* `niceStep`: the step `1`, `2` or `5` times a power of ten that puts closest to the target
  number of ticks on an interval.
* `Ticks`, `niceTicks`: the step, the interval widened to whole steps, and the tick values (each
  an integer multiple of the step, so no error accumulates).
* `fmtFixed`, `tickLabel`: a value with a fixed number of decimals, the minus sign as U+2212.

## References

* Paul S. Heckbert, "Nice numbers for graph labels", in *Graphics Gems*, Academic Press, 1990
  (the 1-2-5 rule; here the step is chosen by the number of ticks it gives).
-/

namespace PILean.Plot

/-- `10 ^ k` for an integer `k`. -/
def pow10 (k : Int) : Float :=
  if k ≥ 0 then (10 : Float) ^ k.toNat.toFloat else 1 / (10 : Float) ^ (-k).toNat.toFloat

/-- `⌊x⌋` as an integer (0 for a non-finite value; magnitudes clamped at 2⁶²). -/
def floorInt (x : Float) : Int :=
  if x.isNaN || x.isInf then 0
  else
    let y := if x > 4.6e18 then 4.6e18 else if x < -4.6e18 then -4.6e18 else x
    if y ≥ 0 then y.floor.toUInt64.toNat else -((-y).ceil.toUInt64.toNat : Int)

/-- `⌈x⌉` as an integer. -/
def ceilInt (x : Float) : Int := -floorInt (-x)

/-- The number of multiples of `step` in `[lo, hi]`. -/
def ticksIn (lo hi step : Float) : Nat := (floorInt (hi / step) - ceilInt (lo / step) + 1).toNat

/-- The decimal exponent of a step: the `k` with `step = m · 10^k`, `m ∈ {1, 2, 5}`. -/
def stepExponent (step : Float) : Int := floorInt (step.log10 + 1e-9)

/-- The step among `{1, 2, 5} · 10^k` whose multiples in `[lo, hi]` number closest to `target`
(the larger step on a tie); `1` for an empty or non-finite interval. -/
def niceStep (lo hi : Float) (target : Nat := 5) : Float := Id.run do
  let span := hi - lo
  if !(span > 0) || span.isInf then return 1
  let k := floorInt (span / (max target 1).toFloat).log10
  let mut best : Float := 1
  let mut bestErr : Nat := 1000000
  for e in [k - 1, k, k + 1] do
    for m in [1, 2, 5] do
      let s := m * pow10 e
      let n := ticksIn lo hi s
      let err := if n ≥ target then n - target else target - n
      if err < bestErr || (err == bestErr && s > best) then best := s; bestErr := err
  return best

/-- Ticks on an axis. -/
structure Ticks where
  /-- The step between ticks. -/
  step : Float
  /-- The interval shown: the data interval, widened to whole steps when asked. -/
  lo : Float
  /-- The upper end of the interval shown. -/
  hi : Float
  /-- The tick values, ascending. -/
  values : Array Float
  /-- The decimals the labels need. -/
  decimals : Nat
  deriving Inhabited, Repr

/-- The ticks of `[lo, hi]` by `niceStep`; with `snap` the interval is widened to the multiples
of the step around it. A degenerate interval is widened by one unit (or half its magnitude) each
way; a non-finite one becomes `[0, 1]`. -/
def niceTicks (lo0 hi0 : Float) (target : Nat := 5) (snap : Bool := true) : Ticks :=
  let bad := lo0.isNaN || hi0.isNaN || lo0.isInf || hi0.isInf
  let (lo1, hi1) := if bad then (0, 1) else (min lo0 hi0, max lo0 hi0)
  let (lo, hi) :=
    if lo1 < hi1 then (lo1, hi1)
    else let d := if lo1 == 0 then 1 else lo1.abs / 2
      (lo1 - d, hi1 + d)
  let step := niceStep lo hi target
  -- A relative slack of 1e-9 keeps a bound that is a multiple up to rounding a multiple.
  let (a, b) := if snap then (floorInt (lo / step + 1e-9), ceilInt (hi / step - 1e-9))
    else (ceilInt (lo / step - 1e-9), floorInt (hi / step + 1e-9))
  let values := ((List.range (b - a + 1).toNat).map fun (i : Nat) =>
    Float.ofInt (a + (i : Int)) * step).toArray
  let (slo, shi) := if snap then (Float.ofInt a * step, Float.ofInt b * step) else (lo, hi)
  { step, lo := slo, hi := shi, values, decimals := (-(stepExponent step)).toNat }

/-- `x` with exactly `decimals` decimals, rounded half away from zero; the minus sign is U+2212
and no `−0` is written. -/
def fmtFixed (x : Float) (decimals : Nat) : String :=
  if x.isNaN then "NaN" else if x.isInf then (if x > 0 then "∞" else "−∞")
  else
    let p := 10 ^ decimals
    let n : Nat := (x.abs * p.toFloat).round.toUInt64.toNat
    let whole := toString (n / p)
    let fd := Nat.toDigits 10 (n % p)
    let frac := String.ofList (List.replicate (decimals - fd.length) '0' ++ fd)
    let body := if decimals == 0 then whole else whole ++ "." ++ frac
    if x < 0 && n != 0 then "−" ++ body else body

/-- The label of a tick value. -/
def tickLabel (t : Ticks) (v : Float) : String := fmtFixed v t.decimals

end PILean.Plot
