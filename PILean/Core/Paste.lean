import PILean.Core.Image

set_option linter.unusedVariables false  -- stub file; remove when implementing

/-!
# Crop, paste, and compositing

Region extraction and image-onto-image copying. All operations clip
silently; `crop` regions outside the source are filled with zero bytes
(PIL semantics).
-/

namespace PILean.Image

/-- Extract rectangle `r`. Regions of `r` outside the image are filled with
zero bytes (PIL crop semantics). The result is `r.width × r.height` in the
source's mode. -/
def crop (img : Image) (r : Rect) : Image :=
  panic! "PILean.Image.crop: not implemented yet (WP1)"

/-- Copy `src` onto `dst` with `src`'s top-left at `pos`, clipped to `dst`.
Plain copy, no blending; `src` is converted to `dst`'s mode first. -/
def paste (dst : Image) (src : Image) (pos : Point) : Image :=
  panic! "PILean.Image.paste: not implemented yet (WP1)"

/-- Like `paste` but alpha-composites using `src`'s alpha (`Color.over`). -/
def alphaComposite (dst : Image) (src : Image) (pos : Point) : Image :=
  panic! "PILean.Image.alphaComposite: not implemented yet (WP1)"

end PILean.Image
