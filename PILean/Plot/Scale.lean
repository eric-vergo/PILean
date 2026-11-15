/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Plot.Ticks

/-!
# Scales

How data values become positions on an axis, and the ticks each kind of axis shows.

* **Linear** axes take `niceTicks` (multiples of 1, 2 or 5 times a power of ten) and minor
  ticks between them: five per step for steps 1 and 5, four for step 2.
* **Logarithmic** axes (base 10) take the powers of ten in the domain as major ticks (every
  `k`th when there are many decades) and 2–9 times them as minor ticks. Values at or below zero
  are not shown on a logarithmic axis (they are dropped from the data, and a domain that reaches
  them is moved to the positive values).
* **Labels**: decimals from the step; magnitudes of 10⁶ and more, or below 10⁻⁴, in
  E-notation (`1.5e7`); the minus sign is U+2212.

## Main definitions

* `ScaleKind`, `Scale`, `Scale.map`, `Scale.ofDomain`.
* `minorValues`, `logTicks`.
* `formatTick`.
-/

namespace PILean.Plot

/-- The kind of an axis's scale. -/
inductive ScaleKind where
  /-- Values map linearly to positions. -/
  | linear
  /-- Base-10 logarithms of values map linearly to positions. -/
  | log
  deriving BEq, Inhabited, Repr

/-- A scale: its kind, its domain (data values at the two ends) and its ticks. -/
structure Scale where
  /-- The kind. -/
  kind : ScaleKind := .linear
  /-- The data value at the start of the axis. -/
  lo : Float := 0
  /-- The data value at its end. -/
  hi : Float := 1
  /-- Major tick values, ascending. -/
  major : Array Float := #[]
  /-- Minor tick values, ascending, not at major ticks. -/
  minor : Array Float := #[]
  /-- The decimals labels of a linear scale need. -/
  decimals : Nat := 0
  deriving Inhabited, Repr

/-- The base-10 logarithm, or `none` for a value that is not positive and finite. -/
def log10? (v : Float) : Option Float :=
  if v > 0 && !v.isInf then some v.log10 else none

/-- The position of `v` on a scale whose ends are at `a` and `b` (`none` when the value has no
position: not finite, or not positive on a logarithmic scale). -/
def Scale.map (s : Scale) (a b v : Float) : Option Float :=
  if v.isNaN || v.isInf then none
  else match s.kind with
    | .linear => some (mapLinear s.lo s.hi a b v)
    | .log => do
      let l ← log10? s.lo
      let h ← log10? s.hi
      let x ← log10? v
      some (mapLinear l h a b x)

/-- The scale widened so that `[lo, hi]` maps to `[low, span - high]` of an axis `span` pixels
long instead of to all of it (on a logarithmic scale, in the logarithms): the ticks stay, the
data gets `low` and `high` pixels of room at the ends. Unchanged if the room would not leave a
positive length. -/
def Scale.padded (s : Scale) (low high span : Float) : Scale :=
  let inner := span - low - high
  if inner ≤ 0 || !(low ≥ 0) || !(high ≥ 0) then s else
  match s.kind with
  | .linear =>
    let k := (s.hi - s.lo) / inner
    { s with lo := s.lo - k * low, hi := s.hi + k * high }
  | .log =>
    match log10? s.lo, log10? s.hi with
    | some l, some h =>
      let k := (h - l) / inner
      { s with lo := pow10f (l - k * low), hi := pow10f (h + k * high) }
    | _, _ => s
where
  /-- `10 ^ x` for a real `x`. -/
  pow10f (x : Float) : Float := Float.exp (x * Float.log 10)

/-- Minor ticks between the major ticks of a linear axis (and beyond them up to the domain's
ends): five intervals per step for a step of mantissa 1 or 5, four for 2. -/
def minorValues (t : Ticks) : Array Float := Id.run do
  let m := t.step / pow10 (stepExponent t.step)
  let n : Nat := if (m - 2).abs < 0.01 then 4 else 5
  let sub := t.step / n.toFloat
  if !(sub > 0) then return #[]
  let a := ceilInt (t.lo / sub - 1e-9)
  let b := floorInt (t.hi / sub + 1e-9)
  if b - a > 2000 then return #[]
  let mut out := #[]
  for k in tickMultipliers a b do
    if k % (n : Int) != 0 then out := out.push (Float.ofInt k * sub)
  return out

/-- Logarithmic ticks for `[lo, hi]` (both positive): the decades, every `k`th so that there are
at most `target + 2` of them, and minor ticks 2–9 times each decade when the decades are not
thinned. -/
def logTicks (lo hi : Float) (target : Nat) : Array Float × Array Float := Id.run do
  let some l := log10? lo | return (#[], #[])
  let some h := log10? hi | return (#[], #[])
  let a := ceilInt (l - 1e-9)
  let b := floorInt (h + 1e-9)
  if b - a > 600 then return (#[], #[])
  let decades := (b - a + 1).toNat
  let k := max 1 ((decades + target + 1) / (target + 2))
  let major := (tickMultipliers a b).filter (fun e => (e - a) % (k : Int) == 0) |>.toArray
    |>.map pow10
  let mut minor := #[]
  if k == 1 then
    for e in tickMultipliers (floorInt (l - 1e-9)) (ceilInt (h + 1e-9)) do
      for m in [2:10] do
        let v := m.toFloat * pow10 e
        if v ≥ lo * (1 - 1e-9) && v ≤ hi * (1 + 1e-9) then minor := minor.push v
  return (major, minor)

/-- A scale for a data extent `[lo, hi]` (or a fixed domain): linear ticks by `niceTicks`,
widened to whole steps unless the domain is fixed; logarithmic ticks by `logTicks`, the
domain widened to whole decades unless fixed. -/
def Scale.ofDomain (kind : ScaleKind) (lo hi : Float) (target : Nat) (fixed : Bool) : Scale :=
  match kind with
  | .linear =>
    let t := niceTicks lo hi target (snap := !fixed)
    { kind, lo := t.lo, hi := t.hi, major := t.values, minor := minorValues t,
      decimals := t.decimals }
  | .log =>
    let lo := if lo > 0 && !lo.isInf then lo else if hi > 0 && !hi.isInf then hi / 10 else 1
    let hi := if hi > lo && !hi.isInf then hi else lo * 10
    let (lo, hi) := if fixed then (lo, hi)
      else (pow10 (floorInt (lo.log10 + 1e-9)), pow10 (ceilInt (hi.log10 - 1e-9)))
    let hi := if hi ≤ lo then lo * 10 else hi
    let (major, minor) := logTicks lo hi target
    { kind, lo, hi, major, minor }

/-- The digits of an integer as superscript characters (`⁻` for the sign), for exponents. -/
def superscript (e : Int) : String :=
  let digit : Char → Char := fun c => match c with
    | '0' => '⁰' | '1' => '¹' | '2' => '²' | '3' => '³' | '4' => '⁴' | '5' => '⁵'
    | '6' => '⁶' | '7' => '⁷' | '8' => '⁸' | _ => '⁹'
  (if e < 0 then "⁻" else "") ++ (toString e.natAbs).map digit

/-- A mantissa with at most `d` decimals and no trailing zeros. -/
def trimmed (m : Float) (d : Nat) : String :=
  let ms := fmtFixed m d
  if ms.contains '.' then
    let t := (ms.toList.reverse.dropWhile (· == '0')).reverse
    String.ofList (if t.getLast? == some '.' then t.dropLast else t)
  else ms

/-- The text of `v` as a multiple of `10^e`: `0` for zero, `10ᵉ` for `v = 10^e`, else the
mantissa (at most two decimals) `× 10ᵉ`, the exponent in superscript digits. -/
def timesPow10 (v : Float) (e : Int) : String :=
  if v == 0 then "0" else
    let m := v / pow10 e
    let ms := trimmed m 2
    if ms == "1" then "10" ++ superscript e
    else if ms == "-1" then "−10" ++ superscript e
    else (if m < 0 then "−" ++ (ms.drop 1).toString else ms) ++ "×10" ++ superscript e

/-- The text of a value `v` as `m×10ᵉ` with `e` its own exponent (see `timesPow10`). -/
def eNotation (v : Float) : String :=
  if v == 0 then "0" else timesPow10 v (floorInt (v.abs.log10 + 1e-9))

/-- Whether a linear scale's labels need powers of ten: a major tick of magnitude 10⁶ or more,
or a non-zero one below 10⁻⁴. -/
def Scale.needsPowers (s : Scale) : Bool :=
  s.major.any fun v => v != 0 && (v.abs ≥ 1e6 || v.abs < 1e-4)

/-- A tick label, in one style for the whole axis. On a linear scale: with the scale's decimals,
or, when a tick needs it (`needsPowers`), every tick as a multiple of one power of ten, that of
the largest tick (`0.5×10¹⁰`, `10¹⁰`, `1.5×10¹⁰`). On a logarithmic scale: every power of ten
as a number when they all lie between 10⁻³ and 10⁴, else every one as `10ᵉ`. -/
def formatTick (s : Scale) (v : Float) : String :=
  match s.kind with
  | .linear =>
    if s.needsPowers then
      let big := s.major.foldl (fun m x => max m x.abs) 0
      let e := if big > 0 then floorInt (big.log10 + 1e-9) else 0
      timesPow10 v e
    else fmtFixed v s.decimals
  | .log =>
    let plain := s.major.all fun x =>
      let e := floorInt (x.log10 + 1e-9)
      e ≥ -3 && e ≤ 4
    let e := floorInt (v.log10 + 1e-9)
    if plain then (if e ≥ 0 then fmtFixed v 0 else fmtFixed v e.natAbs)
    else "10" ++ superscript e

end PILean.Plot
