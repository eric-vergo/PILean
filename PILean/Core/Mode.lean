/-!
# Image modes

The pixel-storage modes supported by PILean. Each mode fixes how many bytes
one pixel occupies in an `Image`'s backing buffer and how those bytes are
interpreted.
-/

namespace PILean

/-- Pixel storage layout and interpretation (PIL's "mode").

* `gray` — 8-bit grayscale (PIL `L`)
* `grayAlpha` — 8-bit grayscale with alpha (PIL `LA`)
* `rgb` — 8-bit red/green/blue (PIL `RGB`)
* `rgba` — 8-bit RGB with alpha (PIL `RGBA`)
* `palette` — 8-bit indices into a color palette (PIL `P`)

Future modes (16-bit grayscale, float, CMYK) extend this inductive. -/
inductive Mode where
  | gray
  | grayAlpha
  | rgb
  | rgba
  | palette
  deriving Repr, DecidableEq, Inhabited, Hashable

namespace Mode

/-- Number of bytes used to store one pixel in this mode. -/
def bytesPerPixel : Mode → Nat
  | .gray => 1
  | .grayAlpha => 2
  | .rgb => 3
  | .rgba => 4
  | .palette => 1

/-- Does the mode carry an alpha channel? -/
def hasAlpha : Mode → Bool
  | .grayAlpha | .rgba => true
  | _ => false

instance : ToString Mode :=
  ⟨fun
    | .gray => "gray"
    | .grayAlpha => "grayAlpha"
    | .rgb => "rgb"
    | .rgba => "rgba"
    | .palette => "palette"⟩

end Mode

end PILean
