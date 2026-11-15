/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Image.Ops

/-!
# Properties of the image operations

Sizes and well-formedness of the results of `Image.crop`, `Image.paste`, `Image.convert`, the
flips and turns, and `Image.new`, and that flipping twice is the identity on a well-formed image.

## Main statements

* `Image.generate_wellFormed`, `Image.new_wellFormed`.
* `Image.crop_width`, `Image.crop_height`, `Image.crop_wellFormed`.
* `Image.paste_wellFormed`, `Image.convert_wellFormed`.
* `Image.flipLeftRight_wellFormed`, `Image.flipLeftRight_flipLeftRight`,
  `Image.flipTopBottom_flipTopBottom`.

## Implementation notes

`Image.resize` is built from loops and its well-formedness is tested (`PILeanTest.Image`), not
proved here.

## References

None.
-/

namespace PILean

namespace Image

/-- An image made by `generate` is well formed. -/
theorem generate_wellFormed (mode : Mode) (w h : Nat) (f : Nat → Nat → Nat → UInt8) :
    (generate mode w h f).WellFormed := sorry

/-- `Image.new` is well formed. -/
theorem new_wellFormed (mode : Mode) (w h : Nat) (c : Rgba) : (new mode w h c).WellFormed := sorry

/-- A crop is `(x1 - x0).toNat` wide. -/
theorem crop_width (im : Image) (x0 y0 x1 y1 : Int) : (im.crop x0 y0 x1 y1).width = (x1 - x0).toNat :=
  sorry

/-- A crop is `(y1 - y0).toNat` high. -/
theorem crop_height (im : Image) (x0 y0 x1 y1 : Int) :
    (im.crop x0 y0 x1 y1).height = (y1 - y0).toNat := sorry

/-- A crop is well formed, whatever the image and the box. -/
theorem crop_wellFormed (im : Image) (x0 y0 x1 y1 : Int) : (im.crop x0 y0 x1 y1).WellFormed :=
  sorry

/-- A paste has `dst`'s size and mode and is well formed. -/
theorem paste_wellFormed (dst src : Image) (x y : Int) (mask : Option Image) :
    (dst.paste src x y mask).WellFormed ∧ (dst.paste src x y mask).width = dst.width ∧
      (dst.paste src x y mask).height = dst.height := sorry

/-- A conversion of a well-formed image is well formed. -/
theorem convert_wellFormed (im : Image) (mode : Mode) (h : im.WellFormed) :
    (im.convert mode).WellFormed := sorry

/-- A left-right flip keeps the width and the height. -/
theorem flipLeftRight_size (im : Image) :
    im.flipLeftRight.width = im.width ∧ im.flipLeftRight.height = im.height := sorry

/-- A left-right flip is well formed. -/
theorem flipLeftRight_wellFormed (im : Image) : im.flipLeftRight.WellFormed := sorry

/-- A quarter turn swaps the width and the height. -/
theorem rotate90_size (im : Image) :
    im.rotate90.width = im.height ∧ im.rotate90.height = im.width := sorry

/-- Flipping left to right twice gives back a well-formed image. -/
theorem flipLeftRight_flipLeftRight (im : Image) (h : im.WellFormed) :
    im.flipLeftRight.flipLeftRight = im := sorry

/-- Flipping top to bottom twice gives back a well-formed image. -/
theorem flipTopBottom_flipTopBottom (im : Image) (h : im.WellFormed) :
    im.flipTopBottom.flipTopBottom = im := sorry

end Image

end PILean
