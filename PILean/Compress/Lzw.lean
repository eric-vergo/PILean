import PILean.Core.Error

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# LZW (GIF and TIFF variants)

Variable-code-width LZW with clear/EOI codes, parameterized by
`earlyChange` so TIFF can reuse it: the code width bumps one code *early*
in TIFF, but not in GIF — GIF callers always pass `false`.

Decoder must-handle cases (WP14): KwKwK (code equals the next unassigned
slot), deferred clear (dictionary full at 4096 and the encoder never sends
a clear — freeze and keep decoding at 12 bits, do not error), first code
after clear must be a literal, missing EOI (be lenient). `maxOutput` caps
decompression bombs (callers pass `width * height`).
-/

namespace PILean.Compress.Lzw

/-- Decompress an LZW stream. `minCodeSize` is the GIF "LZW minimum code
size" (initial width is `minCodeSize + 1`); `maxOutput` bounds the output
(error past it). `earlyChange := true` selects the TIFF width-bump quirk. -/
def decompress (minCodeSize : Nat) (data : ByteArray) (maxOutput : Nat)
    (earlyChange : Bool := false) : Except DecodeError ByteArray :=
  .error (.unsupported "lzw" "decompress not implemented yet (WP14)")

/-- Compress with LZW (GIF variant; emits clear/EOI codes). -/
def compress (minCodeSize : Nat) (data : ByteArray) : ByteArray :=
  panic! "PILean.Compress.Lzw.compress: not implemented yet (WP14)"

end PILean.Compress.Lzw
