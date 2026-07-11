import PILean.Codec.Types
import PILean.Codec.Png.Chunk
import PILean.Codec.Png.Filter
import PILean.Compress.Zlib

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# PNG encoding

WP11. v1 writes bit depth 8 only: `.gray` → color type 0, `.grayAlpha` → 4,
`.rgb` → 2, `.rgba` → 6, `.palette` → 3 (8-bit PLTE even for small
palettes — valid, just not minimal). Works the moment stored-block DEFLATE
exists; compression quality improves transparently as WP10 lands.
-/

namespace PILean.Png

/-- PNG encode options. -/
structure Options where
  /-- DEFLATE compression level, 0 (stored) – 9. -/
  level : Nat := 6
  /-- Scanline filter heuristic. -/
  heuristic : FilterHeuristic := .msad
  deriving Repr, Inhabited

/-- Encode as PNG with explicit options. -/
def encodeWith (opts : Options) (img : Image) : Except EncodeError ByteArray :=
  .error (.invalidArg "png encoder not implemented yet (WP11)")

/-- Encode as PNG with default options. -/
def encode (img : Image) : Except EncodeError ByteArray :=
  encodeWith {} img

end PILean.Png
