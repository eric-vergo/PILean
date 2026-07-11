import PILean.Codec.Types
import PILean.Binary.Reader
import PILean.Binary.Writer

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# Netpbm (PPM/PGM/PBM)

The simplest viewable formats — both ASCII (P1–P3) and binary (P4–P6)
variants, encode and decode (WP4). Header comments (`#` to end of line)
must be skipped. Encode: gray → P5, everything else → P6 via RGB
conversion (binary variants; maxval 255). Decode maps P1/P4 (bitmap) and
P2/P5 (graymap) to `.gray`, P3/P6 (pixmap) to `.rgb`.
-/

namespace PILean.Netpbm

/-- Decode any of P1–P6. -/
def decode (bytes : ByteArray) : Except DecodeError Image :=
  .error (.unsupported "netpbm" "decoder not implemented yet (WP4)")

/-- Encode as binary PGM (P5) for `.gray`, otherwise binary PPM (P6). -/
def encode (img : Image) : Except EncodeError ByteArray :=
  .error (.invalidArg "netpbm encoder not implemented yet (WP4)")

/-- Netpbm codec (registered in `PILean.codecs`). -/
def codec : Codec where
  name := "netpbm"
  extensions := [".ppm", ".pgm", ".pbm", ".pnm"]
  sniff := fun b =>
    b.size ≥ 2 && b.get! 0 == 80 &&  -- 'P'
    49 ≤ b.get! 1 && b.get! 1 ≤ 54   -- '1'–'6'
  decode := decode
  encode := encode

end PILean.Netpbm
