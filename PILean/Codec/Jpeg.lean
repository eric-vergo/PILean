import PILean.Codec.Types
import PILean.Binary.Reader
import PILean.Binary.Writer

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# JPEG

Baseline sequential (SOF0), Huffman, 8-bit. Decode (WP17): grayscale and
3-component YCbCr with sampling factors h,v ∈ {1,2}; restart markers
supported; integer IDCT implemented from the AAN/T.81 papers (never from
libjpeg source); replication chroma upsampling in v1. Clean
`unsupported` errors for progressive (SOF2), arithmetic coding, 12-bit,
CMYK. APP1/EXIF preserved opaquely in `Image.info`; no orientation
auto-rotation (Pillow parity). Encode (WP18): Annex K tables scaled by the
standard quality mapping, standard Huffman tables, 4:4:4 and 4:2:0.

WP17/18 split this into submodules under `PILean/Codec/Jpeg/` (markers,
MSB-first bit reader with 0xFF-stuffing, Huffman, DCT, color) — those
internals are theirs to shape; only `decode`/`encodeWith`/`encode`/`codec`
and `Options` are frozen.
-/

namespace PILean.Jpeg

/-- Chroma subsampling for encoding. -/
inductive Subsampling where
  | s444
  | s422
  | s420
  deriving Repr, DecidableEq, Inhabited

/-- JPEG encode options. -/
structure Options where
  /-- 1–100, PIL-compatible quality scaling of the Annex K tables. -/
  quality : Nat := 75
  subsampling : Subsampling := .s444
  deriving Repr, Inhabited

/-- Decode a baseline JPEG. -/
def decode (bytes : ByteArray) : Except DecodeError Image :=
  .error (.unsupported "jpeg" "decoder not implemented yet (WP17)")

/-- Encode as baseline JPEG with explicit options. -/
def encodeWith (opts : Options) (img : Image) : Except EncodeError ByteArray :=
  .error (.invalidArg "jpeg encoder not implemented yet (WP18)")

/-- Encode as baseline JPEG with default options (quality 75, 4:4:4). -/
def encode (img : Image) : Except EncodeError ByteArray :=
  encodeWith {} img

/-- JPEG codec (registered in `PILean.codecs`). -/
def codec : Codec where
  name := "jpeg"
  extensions := [".jpg", ".jpeg", ".jfif"]
  sniff := fun b => b.size ≥ 3 && b.get! 0 == 0xFF && b.get! 1 == 0xD8 && b.get! 2 == 0xFF
  decode := decode
  encode := encode

end PILean.Jpeg
