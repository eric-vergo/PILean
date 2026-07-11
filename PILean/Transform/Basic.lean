import PILean.Core.Image

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# Basic transforms

Lossless orientation transforms (WP7): flips, quarter-turn rotations, and
transposition. All are pure pixel-shuffles — output size is the input size
with width/height swapped where appropriate.
-/

namespace PILean.Image

/-- Mirror horizontally (left↔right). -/
def flipH (img : Image) : Image :=
  panic! "PILean.Image.flipH: not implemented yet (WP7)"

/-- Mirror vertically (top↔bottom). -/
def flipV (img : Image) : Image :=
  panic! "PILean.Image.flipV: not implemented yet (WP7)"

/-- Rotate 90° counter-clockwise (PIL's `ROTATE_90`). -/
def rotate90 (img : Image) : Image :=
  panic! "PILean.Image.rotate90: not implemented yet (WP7)"

/-- Rotate 180°. -/
def rotate180 (img : Image) : Image :=
  panic! "PILean.Image.rotate180: not implemented yet (WP7)"

/-- Rotate 270° counter-clockwise. -/
def rotate270 (img : Image) : Image :=
  panic! "PILean.Image.rotate270: not implemented yet (WP7)"

/-- Transpose across the main diagonal (swap x and y). -/
def transpose (img : Image) : Image :=
  panic! "PILean.Image.transpose: not implemented yet (WP7)"

end PILean.Image
