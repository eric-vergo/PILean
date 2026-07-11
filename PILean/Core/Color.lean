/-!
# Colors

The universal color type used at every PILean API surface. All image modes
promote to and from 8-bit RGBA `Color`; the image's mode determines how a
color is actually stored (grayscale via `Color.luma`, palette via nearest
entry, and so on).
-/

namespace PILean

/-- An 8-bit RGBA color. The alpha channel defaults to fully opaque. -/
structure Color where
  r : UInt8
  g : UInt8
  b : UInt8
  a : UInt8 := 255
  deriving Repr, DecidableEq, Inhabited

namespace Color

/-- An opaque RGB color. -/
@[inline] def rgb (r g b : UInt8) : Color := ⟨r, g, b, 255⟩

/-- An RGBA color. -/
@[inline] def rgba (r g b a : UInt8) : Color := ⟨r, g, b, a⟩

/-- An opaque gray color. -/
@[inline] def gray (v : UInt8) : Color := ⟨v, v, v, 255⟩

def black : Color := gray 0
def white : Color := gray 255
def transparent : Color := ⟨0, 0, 0, 0⟩
def red : Color := rgb 255 0 0
def green : Color := rgb 0 255 0
def blue : Color := rgb 0 0 255

/-- ITU-R 601-2 luma, matching Pillow's rounded fixed-point conversion:
`(r*19595 + g*38470 + b*7471 + 2¹⁵) >> 16` — i.e. `L = 0.299 R + 0.587 G + 0.114 B`
with rounding. Grayscale conversions must use this so PILean's `L` pixels are
byte-identical to Pillow's. -/
def luma (c : Color) : UInt8 :=
  UInt8.ofNat ((c.r.toNat * 19595 + c.g.toNat * 38470 + c.b.toNat * 7471 + 0x8000) >>> 16)

/-- Source-over alpha compositing of `src` onto `dst` (straight, non-premultiplied
alpha, with rounding). -/
def over (src dst : Color) : Color :=
  let sa := src.a.toNat
  if sa == 255 then src
  else
    let da := dst.a.toNat
    let n := sa * 255 + da * (255 - sa)
    if n == 0 then transparent
    else
      let blend (s d : UInt8) : UInt8 :=
        UInt8.ofNat ((s.toNat * sa * 255 + d.toNat * da * (255 - sa) + n / 2) / n)
      ⟨blend src.r dst.r, blend src.g dst.g, blend src.b dst.b,
       UInt8.ofNat ((n + 127) / 255)⟩

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Parse `"#rgb"`, `"#rgba"`, `"#rrggbb"`, or `"#rrggbbaa"` (leading `#` optional).
Shorthand digits are doubled, CSS-style: `"#f0a"` = `"#ff00aa"`. -/
def ofHex? (s : String) : Option Color := do
  let s := if s.startsWith "#" then (s.drop 1).toString else s
  let ds ← s.toList.mapM hexDigit?
  let u (n : Nat) : UInt8 := UInt8.ofNat n
  match ds with
  | [r, g, b] => some ⟨u (r * 17), u (g * 17), u (b * 17), 255⟩
  | [r, g, b, a] => some ⟨u (r * 17), u (g * 17), u (b * 17), u (a * 17)⟩
  | [r₁, r₂, g₁, g₂, b₁, b₂] =>
    some ⟨u (r₁ * 16 + r₂), u (g₁ * 16 + g₂), u (b₁ * 16 + b₂), 255⟩
  | [r₁, r₂, g₁, g₂, b₁, b₂, a₁, a₂] =>
    some ⟨u (r₁ * 16 + r₂), u (g₁ * 16 + g₂), u (b₁ * 16 + b₂), u (a₁ * 16 + a₂)⟩
  | _ => none

end Color

end PILean
