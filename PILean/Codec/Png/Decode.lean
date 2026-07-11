import PILean.Codec.Types
import PILean.Codec.Png.Chunk
import PILean.Codec.Png.Filter
import PILean.Codec.Png.Interlace
import PILean.Compress.Zlib

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# PNG decoding

WP12. v1 policy (normalize on load): all five color types; bit depths
1/2/4 scale up to 8 (`x * 255 / (2^d − 1)`); 16-bit takes the high byte
(documented lossy until 16-bit modes land); palette + tRNS preserved;
multiple IDATs concatenated before inflating; Adam7 handled on decode;
ancillary chunks gAMA/pHYs/tEXt/zTXt/tIME parsed into `Image.info`,
unknown ancillary skipped, unknown critical → `unsupported`.
-/

namespace PILean.Png

/-- Decode a PNG. -/
def decode (bytes : ByteArray) : Except DecodeError Image :=
  .error (.unsupported "png" "decoder not implemented yet (WP12)")

end PILean.Png
