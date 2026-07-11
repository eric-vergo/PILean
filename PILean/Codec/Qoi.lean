import PILean.Codec.Types
import PILean.Binary.Reader
import PILean.Binary.Writer

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# QOI — the Quite OK Image format

Tiny spec (qoiformat.org), lossless RGB/RGBA. Implemented in WP13 as a
confidence-builder and an extra lossless interchange format.
-/

namespace PILean.Qoi

/-- Decode a QOI image (to `.rgb` or `.rgba` by channel count). -/
def decode (bytes : ByteArray) : Except DecodeError Image :=
  .error (.unsupported "qoi" "decoder not implemented yet (WP13)")

/-- Encode as QOI (non-RGB/RGBA modes are converted to RGBA first). -/
def encode (img : Image) : Except EncodeError ByteArray :=
  .error (.invalidArg "qoi encoder not implemented yet (WP13)")

/-- QOI codec (registered in `PILean.codecs`). -/
def codec : Codec where
  name := "qoi"
  extensions := [".qoi"]
  sniff := fun b =>
    b.size ≥ 4 && b.get! 0 == 113 && b.get! 1 == 111 &&
    b.get! 2 == 105 && b.get! 3 == 102  -- "qoif"
  decode := decode
  encode := encode

end PILean.Qoi
