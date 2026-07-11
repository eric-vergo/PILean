import PILean.Core.Image

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# Mode conversion

`Image.convert` — total conversion between all `Mode`s, hub-and-spoke
through RGBA with fast paths for the common gray↔rgb and rgb↔rgba pairs.
Grayscale targets use `Color.luma` (Pillow-exact). Conversion **to**
`.palette` uses nearest-match against `Palette.webSafe`; adaptive
quantization is `Image.quantize`.
-/

namespace PILean.Image

/-- Convert the image to `mode`. Total: every mode converts to every other.
Converting to `.palette` uses the web-safe palette (see `Image.quantize`
for adaptive palettes). -/
def convert (img : Image) (mode : Mode) : Image :=
  panic! "PILean.Image.convert: not implemented yet (WP1)"

end PILean.Image
