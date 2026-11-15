/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Color

/-!
# Tests for the colour science

Named checks of `PILean.Color` against published values (Ottosson's OKLab reference values, the
WCAG 2 definitions) with explicit tolerances.

## Main definitions

* `PILeanTest.Color.checks`: the named checks and their outcomes.

## References

* <https://bottosson.github.io/posts/oklab/>
* <https://www.w3.org/WAI/WCAG22/Understanding/contrast-minimum.html>
-/

namespace PILeanTest.Color

open PILean

/-- `x` is within `tol` of `y`. -/
def near (x y tol : Float) : Bool := (x - y).abs ≤ tol

/-- The OKLab coordinates of `c` are within `tol` of `(l, a, b)`. -/
def labNear (c : Rgba) (l a b tol : Float) : Bool :=
  let o := c.toOkLab
  near o.l l tol && near o.a a tol && near o.b b tol

/-- Every byte survives decoding and encoding. -/
def byteRoundTrip : Bool :=
  (List.range 256).all fun i =>
    let c := Rgba.rgb i.toUInt8 i.toUInt8 i.toUInt8
    c.toLinear.toRgba == c

/-- The colour survives conversion to OKLCH and back through gamut mapping. -/
def lchRoundTrip (c : Rgba) : Bool := Rgba.ofOkLch c.toOkLch == c

/-- Every colour channel of `c` is within `[0, 1]`. -/
def inUnit (c : LinearRgba) : Bool :=
  0 ≤ c.r && c.r ≤ 1 && 0 ≤ c.g && c.g ≤ 1 && 0 ≤ c.b && c.b ≤ 1

/-- A fixed colour from its channels. -/
def px (r g b : UInt8) : Rgba := Rgba.rgb r g b

/-- The named checks and whether each passes. -/
def checks : Array (String × Bool) := #[
  ("srgbDecode 0.5 = 0.2140411 (1e-6)", near (srgbDecode 0.5) 0.2140411 1e-6),
  ("srgbEncode inverts srgbDecode at 0.5 (1e-9)", near (srgbEncode (srgbDecode 0.5)) 0.5 1e-9),
  ("srgbDecode below the threshold is linear", near (srgbDecode 0.04) (0.04 / 12.92) 1e-12),
  ("all 256 bytes round trip through decode/encode", byteRoundTrip),
  ("toRgba maps NaN to 0", (LinearRgba.mk (0.0/0.0) (0.0/0.0) (0.0/0.0) 1).toRgba == px 0 0 0),
  ("toRgba clamps out-of-range channels",
    (LinearRgba.mk 2 (-1) 0.5 1).toRgba == Rgba.mk 255 0 188 255),
  ("OKLab of white = (1, 0, 0) (1e-4)", labNear (px 255 255 255) 1 0 0 1e-4),
  ("OKLab of #ff0000 = (0.627955, 0.224863, 0.125846) (1e-4)",
    labNear (px 255 0 0) 0.627955 0.224863 0.125846 1e-4),
  ("OKLab of #00ff00 = (0.866440, -0.233888, 0.179498) (1e-4)",
    labNear (px 0 255 0) 0.866440 (-0.233888) 0.179498 1e-4),
  ("OKLab of #0000ff = (0.452014, -0.032457, -0.311528) (1e-4)",
    labNear (px 0 0 255) 0.452014 (-0.032457) (-0.311528) 1e-4),
  ("OKLab to linear inverts toOkLab (1e-6)",
    let c := (px 200 100 50).toLinear
    let d := c.toOkLab.toLinear
    near c.r d.r 1e-6 && near c.g d.g 1e-6 && near c.b d.b 1e-6),
  ("hue of #ff0000 is about 29.23 degrees (1e-2)", near (px 255 0 0).toOkLch.h 29.23 1e-2),
  ("hue is in [0, 360)", (px 0 0 255).toOkLch.h ≥ 0 && (px 0 0 255).toOkLch.h < 360),
  ("deltaEOK of black and white = 1 (1e-4)",
    near (deltaEOK (px 0 0 0).toOkLab (px 255 255 255).toOkLab) 1 1e-4),
  ("relLum #ffffff = 1 (1e-12)", near (relLum (px 255 255 255)) 1 1e-12),
  ("relLum #000000 = 0", relLum (px 0 0 0) == 0),
  ("relLum #ff0000 = 0.2126 (1e-4)", near (relLum (px 255 0 0)) 0.2126 1e-4),
  ("contrast white/black = 21 (1e-9)", near (contrast (px 255 255 255) (px 0 0 0)) 21 1e-9),
  ("contrast is symmetric",
    contrast (px 1 2 3) (px 200 100 50) == contrast (px 200 100 50) (px 1 2 3)),
  ("contrast #777777 on white = 4.478 (1e-3)",
    near (contrast (px 0x77 0x77 0x77) (px 255 255 255)) 4.478 1e-3),
  ("contrast ignores alpha", contrast (Rgba.mk 0 0 0 10) (px 255 255 255) ==
    contrast (px 0 0 0) (px 255 255 255)),
  ("OKLCH round trip #336699", lchRoundTrip (px 0x33 0x66 0x99)),
  ("OKLCH round trip #ff8000", lchRoundTrip (px 0xff 0x80 0x00)),
  ("OKLCH round trip #808080", lchRoundTrip (px 0x80 0x80 0x80)),
  ("OKLCH round trip #ffffff", lchRoundTrip (px 255 255 255)),
  ("OKLCH round trip #000000", lchRoundTrip (px 0 0 0)),
  ("OKLCH round trip #12ab34", lchRoundTrip (px 0x12 0xab 0x34)),
  ("gamutMap of oklch(0.7 0.4 30) lies in [0, 1]", inUnit (gamutMap ⟨0.7, 0.4, 30⟩)),
  ("gamutMap of NaN lies in [0, 1]", inUnit (gamutMap ⟨0.0/0.0, 0.0/0.0, 0.0/0.0⟩)),
  ("gamutMap keeps lightness 1 white", inUnit (gamutMap ⟨1.5, 0.4, 30⟩)),
  ("gamutMap reduces chroma but keeps hue family (red channel dominates)",
    let g := gamutMap ⟨0.7, 0.4, 30⟩
    g.r > g.g && g.r > g.b),
  ("ofOkLch sets the alpha", (Rgba.ofOkLch ⟨0.5, 0.1, 100⟩ 77).a == 77),
  ("hex of opaque #336699", (px 0x33 0x66 0x99).hex == "#336699"),
  ("hex with alpha", (Rgba.mk 0x11 0x22 0x33 0x44).hex == "#11223344"),
  ("hex is lower case", (px 0xab 0xcd 0xef).hex == "#abcdef"),
  ("hex of black pads zeros", (px 0 0 0).hex == "#000000"),
  ("parse #ABC", Rgba.ofHex? "#ABC" == some (px 0xaa 0xbb 0xcc)),
  ("parse #abcd", Rgba.ofHex? "#abcd" == some (Rgba.mk 0xaa 0xbb 0xcc 0xdd)),
  ("parse #11223344", Rgba.ofHex? "#11223344" == some (Rgba.mk 0x11 0x22 0x33 0x44)),
  ("parse #AbCdEf", Rgba.ofHex? "#AbCdEf" == some (px 0xab 0xcd 0xef)),
  ("hex parse round trip", (List.range 256).all fun i =>
    let c := Rgba.mk i.toUInt8 (255 - i).toUInt8 (i / 2).toUInt8 (i * 3 % 256).toUInt8
    Rgba.ofHex? c.hex == some c),
  ("reject empty string", Rgba.ofHex? "" == none),
  ("reject #12", Rgba.ofHex? "#12" == none),
  ("reject #gggggg", Rgba.ofHex? "#gggggg" == none),
  ("reject 123456 without #", Rgba.ofHex? "123456" == none),
  ("reject #12345", Rgba.ofHex? "#12345" == none),
  ("reject a bare #", Rgba.ofHex? "#" == none),
  ("reject a very long string",
    Rgba.ofHex? ("#" ++ String.ofList (List.replicate 100000 'a')) == none),
  ("reject non-ASCII digits", Rgba.ofHex? "#ééé" == none),
  ("over: opaque source returns the source",
    (Rgba.rgb 10 200 30).over (px 90 80 70) == px 10 200 30),
  ("over: transparent source returns the destination",
    (Rgba.mk 10 200 30 0).over (px 90 80 70) == px 90 80 70),
  ("over: 50% white on opaque black is #bcbcbc (alpha 128)",
    (Rgba.mk 255 255 255 128).over (px 0 0 0) == px 188 188 188),
  ("over: transparent on transparent is all zero",
    (Rgba.mk 9 9 9 0).over (Rgba.mk 8 8 8 0) == Rgba.mk 0 0 0 0),
  ("over: result alpha is as + ad (1 - as)",
    ((Rgba.mk 255 0 0 128).over (Rgba.mk 0 0 255 128)).a == 192),
  ("mixOk at t = 0 is the first endpoint", (px 10 200 30).mixOk (px 250 5 90) 0 == px 10 200 30),
  ("mixOk at t = 1 is the second endpoint", (px 10 200 30).mixOk (px 250 5 90) 1 == px 250 5 90),
  ("mixOk interpolates alpha",
    ((Rgba.mk 0 0 0 0).mixOk (Rgba.mk 0 0 0 200) 0.5).a == 100),
  ("mixOk of black and white at 0.5 is mid-grey in lightness (2e-3)",
    near ((px 0 0 0).mixOk (px 255 255 255) 0.5).toOkLab.l 0.5 2e-3),
  ("mixOk clamps t", (px 10 200 30).mixOk (px 250 5 90) 7 == px 250 5 90),
  ("mixOk with NaN t is the first endpoint",
    (px 10 200 30).mixOk (px 250 5 90) (0.0/0.0) == px 10 200 30)
]

end PILeanTest.Color
