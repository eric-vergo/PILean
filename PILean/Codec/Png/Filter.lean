import PILean.Core.Error

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# PNG scanline filters

The five per-row filters (None/Sub/Up/Average/Paeth), encode and decode
(WP11). Paeth predictor selection uses `Int` arithmetic per the spec. This
module is deliberately isolated: `unfilterScanlines ∘ filterScanlines = id`
is property-tested on random rows before any PNG file exists.

Each raw scanline is prefixed by one filter-type byte; `bytesPerRow` is
the *unfiltered* row width (`width * bytesPerPixel`), so the filtered
buffer holds `height * (1 + bytesPerRow)` bytes.
-/

namespace PILean.Png

/-- Filter-choice heuristic for encoding. `.none` writes filter 0
everywhere (valid, fast); `.msad` picks per-row minimum sum of absolute
differences across all five filters (the spec-recommended default). -/
inductive FilterHeuristic where
  | none
  | msad
  deriving Repr, DecidableEq, Inhabited

/-- Remove scanline filters: `raw` is `height` rows of
`1 + bytesPerRow` bytes each; the result is the plain pixel bytes. -/
def unfilterScanlines (bpp bytesPerRow : Nat) (raw : ByteArray) : Except DecodeError ByteArray :=
  .error (.unsupported "png" "unfilterScanlines not implemented yet (WP11)")

/-- Apply scanline filters to plain pixel bytes (inverse of
`unfilterScanlines`). -/
def filterScanlines (bpp bytesPerRow : Nat) (pix : ByteArray)
    (heuristic : FilterHeuristic := .msad) : ByteArray :=
  panic! "PILean.Png.filterScanlines: not implemented yet (WP11)"

end PILean.Png
