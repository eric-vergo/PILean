import PILean.Codec.Types
import PILean.Binary.Reader
import PILean.Binary.Writer

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# BMP

Windows bitmaps (WP4). v1 scope: BI_RGB (uncompressed) 24-bit
and 32-bit, plus 8-bit paletted; BITMAPINFOHEADER; decode both bottom-up
(positive height) and top-down (negative height) row orders; rows are
padded to 4-byte boundaries. Encode: `.rgb` → 24-bit, `.rgba` → 32-bit,
`.palette`/`.gray` → 8-bit paletted, `.grayAlpha` → 32-bit via RGBA.
-/

namespace PILean.Bmp

/-- Decode a BMP (BI_RGB 8/24/32-bit, BITMAPINFOHEADER). -/
def decode (bytes : ByteArray) : Except DecodeError Image :=
  .error (.unsupported "bmp" "decoder not implemented yet (WP4)")

/-- Encode as an uncompressed BMP. -/
def encode (img : Image) : Except EncodeError ByteArray :=
  .error (.invalidArg "bmp encoder not implemented yet (WP4)")

/-- BMP codec (registered in `PILean.codecs`). -/
def codec : Codec where
  name := "bmp"
  extensions := [".bmp", ".dib"]
  sniff := fun b => b.size ≥ 2 && b.get! 0 == 66 && b.get! 1 == 77  -- "BM"
  decode := decode
  encode := encode

end PILean.Bmp
