import PILean.Core.Image

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# Resizing

`Image.resize` with selectable resampling. WP7 implements `nearest` and
`bilinear`; WP20 adds `bicubic` and `lanczos` (until then they fall back
to `bilinear` — documented, not silent: the docstring states the v1
behavior).
-/

namespace PILean

/-- Resampling filter for `Image.resize`. -/
inductive Resample where
  | nearest
  | bilinear
  | bicubic
  | lanczos
  deriving Repr, DecidableEq, Inhabited

namespace Image

/-- Resize to `width × height`. v1 implements `nearest` and `bilinear`;
`bicubic`/`lanczos` fall back to `bilinear` until WP20 lands. -/
def resize (img : Image) (width height : Nat)
    (resample : Resample := .bilinear) : Image :=
  panic! "PILean.Image.resize: not implemented yet (WP7)"

end Image

end PILean
