import PILean.Codec.Types
import PILean.Binary.Reader
import PILean.Binary.Writer
import PILean.Compress.Lzw
import PILean.Compress.Zlib

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# TIFF

Baseline TIFF (WP21): both byte orders, uncompressed + LZW
(`earlyChange := true` — the TIFF quirk) + Deflate compression, strip
layout, the baseline tag set. Multi-page and tiled TIFFs are post-v1
(`unsupported`).
-/

namespace PILean.Tiff

/-- Decode a baseline TIFF. -/
def decode (bytes : ByteArray) : Except DecodeError Image :=
  .error (.unsupported "tiff" "decoder not implemented yet (WP21)")

/-- Encode as an uncompressed baseline TIFF. -/
def encode (img : Image) : Except EncodeError ByteArray :=
  .error (.invalidArg "tiff encoder not implemented yet (WP21)")

/-- TIFF codec (registered in `PILean.codecs`). -/
def codec : Codec where
  name := "tiff"
  extensions := [".tif", ".tiff"]
  sniff := fun b =>
    b.size ≥ 4 &&
    ((b.get! 0 == 73 && b.get! 1 == 73 && b.get! 2 == 42 && b.get! 3 == 0) ||   -- II*\0
     (b.get! 0 == 77 && b.get! 1 == 77 && b.get! 2 == 0 && b.get! 3 == 42))     -- MM\0*
  decode := decode
  encode := encode

end PILean.Tiff
