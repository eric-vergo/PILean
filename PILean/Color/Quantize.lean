import PILean.Core.Image

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# Color quantization

Adaptive palette generation for `.palette` conversion and GIF encoding
(WP13). Median-cut with an exact-palette fast path when the image already
has ≤ `colors` distinct colors (matching Pillow). No dithering in v1
(Floyd–Steinberg comes later).

Test policy: quantizer output is **never** compared against Pillow's
(different quantizers legitimately differ) — it is property-tested
(palette size ≤ `colors`, bounded mean squared error, exactness for
≤ `colors`-color inputs).
-/

namespace PILean.Image

/-- Quantize to a `.palette`-mode image with at most `colors` palette
entries (median cut; exact palette when the input has few colors). -/
def quantize (img : Image) (colors : Nat := 256) : Image :=
  panic! "PILean.Image.quantize: not implemented yet (WP13)"

end PILean.Image
