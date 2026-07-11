import PILean.Core.Image

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# Point operations

Per-pixel adjustments (WP7): invert, brightness, contrast, threshold.
Alpha channels are preserved unchanged. Pillow-parity operations
(autocontrast, equalize, posterize, solarize, channel ops, enhancers)
are added by WP19 as new defs in this namespace.
-/

namespace PILean.Image

/-- Invert every channel except alpha (`255 - v`). -/
def invert (img : Image) : Image :=
  panic! "PILean.Image.invert: not implemented yet (WP7)"

/-- Scale brightness by `factor` (0.0 = black, 1.0 = unchanged, > 1
brighter; clamped). -/
def adjustBrightness (img : Image) (factor : Float) : Image :=
  panic! "PILean.Image.adjustBrightness: not implemented yet (WP7)"

/-- Scale contrast about the mean by `factor` (0.0 = solid gray,
1.0 = unchanged; clamped). -/
def adjustContrast (img : Image) (factor : Float) : Image :=
  panic! "PILean.Image.adjustContrast: not implemented yet (WP7)"

/-- Binarize by luma: pixels with luma ≥ `t` become white, others black.
Alpha is preserved. -/
def threshold (img : Image) (t : UInt8) : Image :=
  panic! "PILean.Image.threshold: not implemented yet (WP7)"

end PILean.Image
