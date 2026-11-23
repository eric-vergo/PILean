/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanMathlib.CertifiedPlot
import PILean.Trust.Attr

/-!
# Certified plots of real functions: the figures

Five figures of the kind `CertifiedPlot`, each an exact rational approximant plotted on a grid
with a bound on its distance to the graph of the real function: the exponential on `[-2, 2]`, the
cosine on `[-3, 3]`, the logarithm on `[1/2, 3/2]`, the square root on `[1/4, 4]` and the
arctangent on `[-3/4, 3/4]`. This module imports nothing from Mathlib;
`PILeanMathlib.Examples.Real` proves each bound.
-/

namespace PILeanMathlib.Examples

open PILean PILean.Plot PILeanMathlib

/-- The Taylor polynomial of the exponential at `0` of degree 15. -/
def expTaylor (x : Rat) : Rat :=
  1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 / 720 + x ^ 7 / 5040
    + x ^ 8 / 40320 + x ^ 9 / 362880 + x ^ 10 / 3628800 + x ^ 11 / 39916800
    + x ^ 12 / 479001600 + x ^ 13 / 6227020800 + x ^ 14 / 87178291200
    + x ^ 15 / 1307674368000

/-- The exponential on `[-2, 2]`: 129 samples of its Taylor polynomial of degree 15, within
`1/1000` of the graph. -/
def expPlot : CertifiedPlot :=
  { name := "exp x", curve := "Taylor polynomial of degree 15", approx := expTaylor,
    lo := -2, hi := 2, steps := 128, delta := 1 / 1000 }

/-- The exponential. -/
@[figure]
def expFigure : Figure := expPlot.figure

/-- The Taylor polynomial of the cosine at `0` of degree 16. -/
def cosTaylor (x : Rat) : Rat :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800
    + x ^ 12 / 479001600 - x ^ 14 / 87178291200 + x ^ 16 / 20922789888000

/-- The cosine on `[-3, 3]`: 97 samples of its Taylor polynomial of degree 16, within `1/2000`
of the graph. -/
def cosPlot : CertifiedPlot :=
  { name := "cos x", curve := "Taylor polynomial of degree 16", approx := cosTaylor,
    lo := -3, hi := 3, steps := 96, delta := 1 / 2000 }

/-- The cosine. -/
@[figure]
def cosFigure : Figure := cosPlot.figure

/-- `∑ i < n, u ^ (i + 1) / (i + 1)`, the series of `-log (1 - u)`. -/
def logSum : Nat → Rat → Rat
  | 0, _ => 0
  | n + 1, u => logSum n u + u ^ (n + 1) / (n + 1)

/-- The logarithm near `1`: `-∑ i < 20, (1 - x) ^ (i + 1) / (i + 1)`. -/
def logApprox (x : Rat) : Rat := -logSum 20 (1 - x)

/-- The logarithm on `[1/2, 3/2]`: 65 samples of its series at `1` to 20 terms, within `1/8000`
of the graph. -/
def logPlot : CertifiedPlot :=
  { name := "log x", curve := "20 terms of its series at 1", approx := logApprox,
    lo := 1 / 2, hi := 3 / 2, steps := 64, delta := 1 / 8000 }

/-- The logarithm. -/
@[figure]
def logFigure : Figure := logPlot.figure

/-- `∑ i < n, (-1) ^ i x ^ (2 i + 1) / (2 i + 1)`, the series of the arctangent. -/
def arctanSum : Nat → Rat → Rat
  | 0, _ => 0
  | n + 1, x => arctanSum n x + (-1) ^ n * x ^ (2 * n + 1) / (2 * n + 1)

/-- The arctangent on `[-3/4, 3/4]`: 49 samples of its series to 20 terms, within `1/5000` of the
graph. -/
def arctanPlot : CertifiedPlot :=
  { name := "arctan x", curve := "20 terms of its series at 0", approx := arctanSum 20,
    lo := -3 / 4, hi := 3 / 4, steps := 48, delta := 1 / 5000 }

/-- The arctangent. -/
@[figure]
def arctanFigure : Figure := arctanPlot.figure

/-- The integer square root of `n` by bisection, `fuel` halvings at most: the greatest `s` with
`s * s ≤ n`, given `lo * lo ≤ n < hi * hi` and enough fuel. -/
def isqrtAux : Nat → Nat → Nat → Nat → Nat
  | 0, lo, _, _ => lo
  | f + 1, lo, hi, n =>
    if hi ≤ lo + 1 then lo
    else
      let m := (lo + hi) / 2
      if m * m ≤ n then isqrtAux f m hi n else isqrtAux f lo m n

/-- The square root of `x ≥ 0` to 30 binary digits: `⌊√⌊x 4³⁰⌋⌋ / 2³⁰`. -/
def sqrtApprox (x : Rat) : Rat :=
  let n := (x * 4 ^ 30).floor.toNat
  (isqrtAux 64 0 (n + 1) n : Rat) / 2 ^ 30

/-- The square root on `[1/4, 4]`: 121 samples to 30 binary digits, within `1/4000` of the
graph. -/
def sqrtPlot : CertifiedPlot :=
  { name := "√x", curve := "square roots to 30 binary digits", approx := sqrtApprox,
    lo := 1 / 4, hi := 4, steps := 120, delta := 1 / 4000 }

/-- The square root. -/
@[figure]
def sqrtFigure : Figure := sqrtPlot.figure

/-- The figures by file stem. -/
def realFigures : Array (String × Figure) :=
  #[("exp-proved", expFigure), ("cos-proved", cosFigure), ("log-proved", logFigure),
    ("arctan-proved", arctanFigure), ("sqrt-proved", sqrtFigure)]

end PILeanMathlib.Examples
