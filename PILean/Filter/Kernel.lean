import PILean.Core.Image

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# Convolution filters

Kernel convolution and the standard blur/sharpen filters built on it
(WP19). Edge handling: clamp-to-edge (PIL behavior). Weights are applied
per channel; alpha is convolved too for alpha modes.
-/

namespace PILean

/-- A square convolution kernel: `size × size` weights (row-major),
`size` odd. Output = `(Σ weightᵢ·pixelᵢ) / scale + offset`, clamped. -/
structure Kernel where
  size : Nat
  weights : Array Float
  scale : Float := 1.0
  offset : Float := 0.0
  deriving Repr, Inhabited

namespace Image

/-- Convolve with `k` (clamp-to-edge borders). -/
def convolve (img : Image) (k : Kernel) : Image :=
  panic! "PILean.Image.convolve: not implemented yet (WP19)"

/-- Box blur with the given radius (radius 0 = unchanged). -/
def boxBlur (img : Image) (radius : Nat) : Image :=
  panic! "PILean.Image.boxBlur: not implemented yet (WP19)"

/-- Gaussian blur with standard deviation ≈ `radius` (PIL-style). -/
def gaussianBlur (img : Image) (radius : Float) : Image :=
  panic! "PILean.Image.gaussianBlur: not implemented yet (WP19)"

/-- Sharpen (PIL `SHARPEN` kernel). -/
def sharpen (img : Image) : Image :=
  panic! "PILean.Image.sharpen: not implemented yet (WP19)"

end Image

end PILean
