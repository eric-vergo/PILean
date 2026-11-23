/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# Colour science

The colour arithmetic of the image library: 8-bit sRGB with straight alpha, its linear light,
Björn Ottosson's OKLab and its polar form OKLCH, mapping an OKLCH colour into the sRGB gamut, the
WCAG 2 relative luminance and contrast ratio, hexadecimal notation, alpha compositing and
interpolation. Everything here is pure arithmetic on `Float`s and bytes.

## Main definitions

* `Rgba`: an 8-bit sRGB colour with straight alpha; `Rgba.hex` and `Rgba.ofHex?` convert to and
  from `#rrggbb[aa]` notation.
* `LinearRgba`: linear-light `Float` channels with straight alpha; `Rgba.toLinear` and
  `LinearRgba.toRgba` convert, using `srgbDecode` and `srgbEncode`.
* `OkLab`, `OkLch`: Ottosson's perceptual space and its lightness / chroma / hue form;
  `LinearRgba.toOkLab`, `OkLab.toLinear`, `OkLab.toLch`, `OkLch.toLab`, `Rgba.toOkLch`,
  `deltaEOK`.
* `gamutMap`, `Rgba.ofOkLch`: an OKLCH colour inside sRGB by CSS Color 4's chroma reduction.
* `relLum`, `contrast`: the WCAG 2 relative luminance and contrast ratio.
* `Rgba.over`: Porter–Duff source-over in linear light.
* `Rgba.mixOk`: interpolation in OKLab.

## Implementation notes

* Hue is in degrees, in `[0, 360)`; an achromatic colour gets hue 0.
* `gamutMap` follows CSS Color 4 section "Gamut Mapping" (binary search on chroma at fixed
  lightness and hue, just-noticeable difference 0.02 in ΔE OK, ε 0.0001), with a fixed bound on the
  number of halvings so that it is a plain `for` loop; its result is clamped into `[0, 1]`, so it is
  inside sRGB whatever the input (also `NaN`).
* The WCAG linearisation threshold is 0.04045 (WCAG 2.2; the 0.03928 of earlier WCAG 2 texts gives
  the same value for every 8-bit channel).
* Conversions from `Float` to bytes clamp to `[0, 1]` first, round half up, and map `NaN` to 0.
* `Rgba.ofHex?` reads untrusted text: it rejects any string longer than nine bytes before looking
  at its characters.

## References

* <https://bottosson.github.io/posts/oklab/> (OKLab and its matrices).
* <https://www.w3.org/TR/css-color-4/> (OKLCH, gamut mapping).
* <https://www.w3.org/WAI/WCAG22/Understanding/contrast-minimum.html> (WCAG 2 contrast).
* <https://www.w3.org/TR/compositing-1/> (Porter–Duff source-over).
-/

namespace PILean

/-! ### Types -/

/-- An 8-bit sRGB colour with straight (non-premultiplied) alpha; `a = 255` is opaque. -/
structure Rgba where
  /-- Red, 0 to 255. -/
  r : UInt8
  /-- Green, 0 to 255. -/
  g : UInt8
  /-- Blue, 0 to 255. -/
  b : UInt8
  /-- Alpha, 0 (transparent) to 255 (opaque). -/
  a : UInt8
deriving BEq, Inhabited, Repr

/-- The opaque colour with the given 8-bit sRGB channels. -/
def Rgba.rgb (r g b : UInt8) : Rgba := ⟨r, g, b, 255⟩

/-- A colour in linear light: channels nominally in `[0, 1]`, straight alpha in `[0, 1]`. -/
structure LinearRgba where
  /-- Red, linear light. -/
  r : Float
  /-- Green, linear light. -/
  g : Float
  /-- Blue, linear light. -/
  b : Float
  /-- Alpha, straight. -/
  a : Float
deriving Repr, Inhabited

/-- A colour in OKLab: perceived lightness `l` (0 black, 1 white) and the opponent axes `a`
(green to red) and `b` (blue to yellow). -/
structure OkLab where
  /-- Lightness. -/
  l : Float
  /-- Green (negative) to red (positive). -/
  a : Float
  /-- Blue (negative) to yellow (positive). -/
  b : Float
deriving Repr, Inhabited

/-- A colour in OKLCH: lightness, chroma (distance from grey) and hue in degrees in `[0, 360)`. -/
structure OkLch where
  /-- Lightness, as `OkLab.l`. -/
  l : Float
  /-- Chroma, `√(a² + b²)`. -/
  c : Float
  /-- Hue in degrees. -/
  h : Float
deriving Repr, Inhabited

/-! ### sRGB transfer functions -/

/-- `x` clamped into `[0, 1]`; `NaN` gives 0. -/
private def clampUnit (x : Float) : Float := if x ≥ 0 then (if x ≤ 1 then x else 1) else 0

/-- The nearest 8-bit value of a unit-scale channel: clamped into `[0, 1]`, scaled by 255 and
rounded half up; `NaN` gives 0. -/
private def toByte (x : Float) : UInt8 :=
  let v := (clampUnit x * 255 + 0.5).floor
  if v ≥ 255 then 255 else if v ≥ 0 then v.toUInt8 else 0

/-- One sRGB-encoded channel to linear light: the sRGB transfer curve (threshold 0.04045),
extended linearly below 0. -/
def srgbDecode (x : Float) : Float :=
  if x ≤ 0.04045 then x / 12.92 else Float.pow ((x + 0.055) / 1.055) 2.4

/-- One linear-light channel to sRGB encoding, the inverse of `srgbDecode` (threshold 0.0031308). -/
def srgbEncode (x : Float) : Float :=
  if x ≤ 0.0031308 then 12.92 * x else 1.055 * Float.pow x (1 / 2.4) - 0.055

/-- An 8-bit channel on the unit scale, still sRGB-encoded. -/
private def unitOf (x : UInt8) : Float := x.toNat.toFloat / 255

/-- The linear-light colour of an 8-bit sRGB colour; alpha is `a / 255`. -/
def Rgba.toLinear (c : Rgba) : LinearRgba :=
  ⟨srgbDecode (unitOf c.r), srgbDecode (unitOf c.g), srgbDecode (unitOf c.b), unitOf c.a⟩

/-- The 8-bit sRGB colour of a linear-light colour: every channel (alpha included) is clamped into
`[0, 1]`, colour channels are sRGB-encoded, and all are rounded half up to 8 bits. `NaN` gives 0. -/
def LinearRgba.toRgba (c : LinearRgba) : Rgba :=
  ⟨toByte (srgbEncode (clampUnit c.r)), toByte (srgbEncode (clampUnit c.g)),
   toByte (srgbEncode (clampUnit c.b)), toByte c.a⟩

/-! ### OKLab and OKLCH -/

/-- Linear sRGB to OKLab (Ottosson's two matrices with a cube root between); alpha is ignored. -/
def LinearRgba.toOkLab (c : LinearRgba) : OkLab :=
  let l := 0.4122214708 * c.r + 0.5363325363 * c.g + 0.0514459929 * c.b
  let m := 0.2119034982 * c.r + 0.6806995451 * c.g + 0.1073969566 * c.b
  let s := 0.0883024619 * c.r + 0.2817188376 * c.g + 0.6299787005 * c.b
  let (l, m, s) := (l.cbrt, m.cbrt, s.cbrt)
  ⟨0.2104542553 * l + 0.7936177850 * m - 0.0040720468 * s,
   1.9779984951 * l - 2.4285922050 * m + 0.4505937099 * s,
   0.0259040371 * l + 0.7827717662 * m - 0.8086757660 * s⟩

/-- OKLab to linear sRGB with alpha 1, the inverse of `LinearRgba.toOkLab` (outside `[0, 1]` for a
colour outside the sRGB gamut). -/
def OkLab.toLinear (c : OkLab) : LinearRgba :=
  let l := c.l + 0.3963377774 * c.a + 0.2158037573 * c.b
  let m := c.l - 0.1055613458 * c.a - 0.0638541728 * c.b
  let s := c.l - 0.0894841775 * c.a - 1.2914855480 * c.b
  let (l, m, s) := (l * l * l, m * m * m, s * s * s)
  ⟨4.0767416621 * l - 3.3077115913 * m + 0.2309699292 * s,
   -1.2684380046 * l + 2.6097574011 * m - 0.3413193965 * s,
   -0.0041960863 * l - 0.7034186147 * m + 1.7076147010 * s, 1⟩

/-- π, for the degree conversions. -/
private def pi : Float := 3.14159265358979323846

/-- OKLab to OKLCH; the hue is in `[0, 360)` and 0 for grey. -/
def OkLab.toLch (c : OkLab) : OkLch :=
  let h := Float.atan2 c.b c.a * 180 / pi
  ⟨c.l, Float.sqrt (c.a * c.a + c.b * c.b), if h < 0 then h + 360 else h⟩

/-- OKLCH to OKLab. -/
def OkLch.toLab (c : OkLch) : OkLab :=
  let r := c.h * pi / 180
  ⟨c.l, c.c * Float.cos r, c.c * Float.sin r⟩

/-- The OKLab coordinates of an 8-bit colour (alpha ignored). -/
def Rgba.toOkLab (c : Rgba) : OkLab := c.toLinear.toOkLab

/-- The OKLCH coordinates of an 8-bit colour (alpha ignored). -/
def Rgba.toOkLch (c : Rgba) : OkLch := c.toOkLab.toLch

/-- ΔE OK: the Euclidean distance in OKLab (CSS Color 4's colour difference). -/
def deltaEOK (x y : OkLab) : Float :=
  let (dl, da, db) := (x.l - y.l, x.a - y.a, x.b - y.b)
  Float.sqrt (dl * dl + da * da + db * db)

/-! ### Gamut mapping -/

/-- Every colour channel in `[0, 1]` (no tolerance; `NaN` is outside). -/
private def LinearRgba.inUnit (c : LinearRgba) : Bool :=
  0 ≤ c.r && c.r ≤ 1 && 0 ≤ c.g && c.g ≤ 1 && 0 ≤ c.b && c.b ≤ 1

/-- Every colour channel clamped into `[0, 1]`; alpha is set to 1. -/
private def LinearRgba.clampColor (c : LinearRgba) : LinearRgba :=
  ⟨clampUnit c.r, clampUnit c.g, clampUnit c.b, 1⟩

/-- The just-noticeable difference of CSS Color 4's gamut mapping, in ΔE OK. -/
private def jnd : Float := 0.02

/-- The chroma precision at which `gamutMap`'s search stops. -/
private def gamutEps : Float := 0.0001

/-- The most halvings `gamutMap` makes: enough to bring any finite chroma below `gamutEps` long
before it ends (64 halvings divide by more than 10¹⁹). -/
private def gamutSteps : Nat := 64

/-- `OkLch.toLab` with the hue's cosine `cs` and sine `sn` given (the same numbers). -/
private def OkLch.toLabWith (c : OkLch) (cs sn : Float) : OkLab := ⟨c.l, c.c * cs, c.c * sn⟩

/-- An OKLCH colour clipped into sRGB, in linear light, with its ΔE OK from the unclipped one;
the hue's cosine `cs` and sine `sn` are given. -/
private def clipOfWith (c : OkLch) (cs sn : Float) : LinearRgba × Float :=
  let lab := c.toLabWith cs sn
  let cl := lab.toLinear.clampColor
  (cl, deltaEOK cl.toOkLab lab)

/-- The gamut mapping of `gamutMap`, with the hue's cosine `cs` and sine `sn` given. -/
private def gamutMapWith (c : OkLch) (cs sn : Float) : LinearRgba := Id.run do
  if c.l ≥ 1 then return ⟨1, 1, 1, 1⟩
  if c.l ≤ 0 then return ⟨0, 0, 0, 1⟩
  let lin := (c.toLabWith cs sn).toLinear
  if lin.inUnit then return lin.clampColor
  let (cl0, e0) := clipOfWith c cs sn
  if e0 < jnd then return cl0
  let mut lo := 0.0
  let mut hi := c.c
  let mut loIn := true
  let mut clipped := cl0
  for _ in [0:gamutSteps] do
    if hi - lo ≤ gamutEps then break
    let mid := (lo + hi) / 2
    let cur : OkLch := { c with c := mid }
    if loIn && (cur.toLabWith cs sn).toLinear.inUnit then
      lo := mid
      continue
    let (cl, e) := clipOfWith cur cs sn
    clipped := cl
    if e < jnd then
      if jnd - e < gamutEps then return clipped
      loIn := false
      lo := mid
    else
      hi := mid
  return clipped

/-- An OKLCH colour inside sRGB, as linear-light channels (alpha 1) by CSS Color 4's gamut mapping:
lightness 1 or more is white, 0 or less black; a colour already inside is kept; otherwise chroma is
reduced at fixed lightness and hue until clipping the colour moves it less than 0.02 in ΔE OK, and
the clipped colour is the answer. Every colour channel of the result is in `[0, 1]`, whatever the
input (also `NaN`). -/
def gamutMap (c : OkLch) : LinearRgba :=
  let r := c.h * pi / 180
  gamutMapWith c (Float.cos r) (Float.sin r)

/-- The 8-bit colour of an OKLCH colour, gamut-mapped and rounded, with the given alpha. -/
def Rgba.ofOkLch (c : OkLch) (alpha : UInt8 := 255) : Rgba :=
  let m := (gamutMap c).toRgba
  { m with a := alpha }

/-! ### WCAG 2 contrast -/

/-- The WCAG 2 relative luminance of an 8-bit colour, from 0 (black) to 1 (white): the channels
through `srgbDecode`, weighted. Alpha is ignored. -/
def relLum (c : Rgba) : Float :=
  0.2126 * srgbDecode (unitOf c.r) + 0.7152 * srgbDecode (unitOf c.g) +
    0.0722 * srgbDecode (unitOf c.b)

/-- The WCAG 2 contrast ratio of two colours, from 1 to 21, symmetric in its arguments. Alpha is
ignored. -/
def contrast (x y : Rgba) : Float :=
  let (a, b) := (relLum x, relLum y)
  (max a b + 0.05) / (min a b + 0.05)

/-! ### Hexadecimal notation -/

/-- The lower-case hexadecimal digit of a value below 16. -/
private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Two lower-case hexadecimal digits of a byte. -/
private def hexByte (x : UInt8) : String :=
  String.ofList [hexDigit (x.toNat / 16), hexDigit (x.toNat % 16)]

/-- The value of a hexadecimal digit, either case. -/
private def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
  else none

/-- The values of a list of hexadecimal digits, or `none` if one is not a digit. -/
private def hexVals? : List Char → Option (List Nat)
  | [] => some []
  | c :: cs => do
    let v ← hexVal? c
    let vs ← hexVals? cs
    pure (v :: vs)

/-- `#rrggbb` in lower case, the alpha left out (SVG writes it as an opacity). -/
def Rgba.rgbHex (c : Rgba) : String := "#" ++ hexByte c.r ++ hexByte c.g ++ hexByte c.b

/-- `#rrggbb` in lower case when the colour is opaque, `#rrggbbaa` otherwise. -/
def Rgba.hex (c : Rgba) : String := c.rgbHex ++ (if c.a == 255 then "" else hexByte c.a)

/-- The colour written as `#rgb`, `#rgba`, `#rrggbb` or `#rrggbbaa` (digits in either case; the
short forms repeat each digit), or `none` for any other text. Input longer than nine bytes is
rejected without being scanned. -/
def Rgba.ofHex? (s : String) : Option Rgba :=
  if s.utf8ByteSize > 9 then none else
  match s.toList with
  | '#' :: rest => do
    let vs ← hexVals? rest
    match vs with
    | [r, g, b] => some ⟨(r * 17).toUInt8, (g * 17).toUInt8, (b * 17).toUInt8, 255⟩
    | [r, g, b, a] =>
      some ⟨(r * 17).toUInt8, (g * 17).toUInt8, (b * 17).toUInt8, (a * 17).toUInt8⟩
    | [r1, r2, g1, g2, b1, b2] =>
      some ⟨(r1 * 16 + r2).toUInt8, (g1 * 16 + g2).toUInt8, (b1 * 16 + b2).toUInt8, 255⟩
    | [r1, r2, g1, g2, b1, b2, a1, a2] =>
      some ⟨(r1 * 16 + r2).toUInt8, (g1 * 16 + g2).toUInt8, (b1 * 16 + b2).toUInt8,
        (a1 * 16 + a2).toUInt8⟩
    | _ => none
  | _ => none

/-! ### Compositing and interpolation -/

/-- Porter–Duff source-over of `src` on `dst`, computed in linear light with straight alpha: the
result alpha is `as + ad (1 - as)`, the colour is the premultiplied sum divided by that alpha. A
fully transparent result is `⟨0, 0, 0, 0⟩`. -/
def Rgba.over (src dst : Rgba) : Rgba :=
  let s := src.toLinear
  let d := dst.toLinear
  let ao := s.a + d.a * (1 - s.a)
  if ao ≤ 0 then ⟨0, 0, 0, 0⟩ else
  let mix (cs cd : Float) : Float := (cs * s.a + cd * d.a * (1 - s.a)) / ao
  ({ r := mix s.r d.r, g := mix s.g d.g, b := mix s.b d.b, a := ao } : LinearRgba).toRgba

/-- Interpolation from `x` (at `t = 0`) to `y` (at `t = 1`) in OKLab, alpha linearly. `t` is
clamped into `[0, 1]` (`NaN` gives 0). The OKLab result is gamut-mapped, so the colour is always a
valid sRGB colour. -/
def Rgba.mixOk (x y : Rgba) (t : Float) : Rgba :=
  let t := clampUnit t
  let p := x.toOkLab
  let q := y.toOkLab
  let lab : OkLab := ⟨p.l + (q.l - p.l) * t, p.a + (q.a - p.a) * t, p.b + (q.b - p.b) * t⟩
  let alpha := unitOf x.a + (unitOf y.a - unitOf x.a) * t
  let m := (gamutMap lab.toLch).toRgba
  { m with a := toByte alpha }

end PILean
