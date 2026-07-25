import PILean
import GalleryLib.Mobius.Exact

/-!
# Möbius flow — the Float render layer

Domain-colors `f(w) = (w³ − 1)/(w³ + 1)` after warping the plane through a
Möbius rotation `M t` from the exact ℚ layer (`Gallery.Mobius.Exact`). Every
frame — swirl or finale — is produced by the same pipeline:

`ℚ matrix → normalize (exact) → entries (exact) → Float, once per frame
→ per-pixel z ↦ mobius z ↦ f (mobius z) ↦ HSV → Color`.

The finale renders `M (1/3) * M (1/2)` and `M 1` — provably the same
projective map by `normalized_composition` — and reports the *runtime*
`ByteArray` equality of their rendered art as a caption, so the theorem is
witnessed by the pixels themselves, not just cited.
-/

namespace Gallery.Mobius

open PILean

/-! ## Float complex mini-ops

A "complex number" is just `Float × Float` (`.1` = real, `.2` = imaginary)
— no new structure, per the render work package's spec. Division guards a
zero denominator by returning a large-but-finite sentinel instead of
producing `inf`/`NaN`: poles must render as extreme-but-colorable pixels,
never crash or corrupt the frame. -/

/-- A Float-valued complex number, as the pair `(re, im)`. -/
abbrev C := Float × Float

/-- Complex addition. -/
def cAdd (z w : C) : C := (z.1 + w.1, z.2 + w.2)

/-- Complex subtraction. -/
def cSub (z w : C) : C := (z.1 - w.1, z.2 - w.2)

/-- Complex multiplication. -/
def cMul (z w : C) : C := (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- Complex division. Guards a zero (or numerically-indistinguishable-from-
zero) denominator by returning a large-but-finite sentinel value instead of
`inf`/`NaN`, so poles render as extreme colors rather than crashing or
poisoning downstream `Float.log2`/`Float.floor` with `NaN`. -/
def cDiv (z w : C) : C :=
  let d := w.1 * w.1 + w.2 * w.2
  if d < 1e-300 then
    (1e30, 1e30)
  else
    ((z.1 * w.1 + z.2 * w.2) / d, (z.2 * w.1 - z.1 * w.2) / d)

/-- Complex scalar multiplication by a real `Float`. -/
def cScale (s : Float) (z : C) : C := (s * z.1, s * z.2)

/-- Complex absolute value (modulus). -/
def cAbs (z : C) : Float := Float.sqrt (z.1 * z.1 + z.2 * z.2)

/-- Complex argument, in `(-π, π]` (the range of `Float.atan2`). -/
def cArg (z : C) : Float := Float.atan2 z.2 z.1

/-! ## HSV → RGB -/

/-- `2π` as a `Float`, the period of `cArg`/hue. -/
def twoPi : Float := 6.283185307179586

/-- Clamp a `Float` into `[0, 1]`. -/
def clamp01 (x : Float) : Float := if x < 0.0 then 0.0 else if x > 1.0 then 1.0 else x

/-- Convert a `Float` channel (clamped to `[0,1]`) to a rounded `UInt8`. -/
def toByte (x : Float) : UInt8 := UInt8.ofNat (clamp01 x * 255.0 + 0.5).toUInt64.toNat

/-- HSV → RGB. `h` is corrected into `[0, 2π)` if slightly negative (the
range `cArg` produces); `s`/`v` are clamped to `[0,1]`. -/
def hsvToColor (h s v : Float) : Color :=
  let h' := if h < 0.0 then h + twoPi else h
  let sector6 := h' / twoPi * 6.0
  let i := Float.floor sector6
  let f := sector6 - i
  let s := clamp01 s
  let v := clamp01 v
  let p := v * (1.0 - s)
  let q := v * (1.0 - s * f)
  let t := v * (1.0 - s * (1.0 - f))
  let (r, g, b) :=
    match i.toUInt64.toNat % 6 with
    | 0 => (v, t, p)
    | 1 => (q, v, p)
    | 2 => (p, v, t)
    | 3 => (p, q, v)
    | 4 => (t, p, v)
    | _ => (v, p, q)
  Color.rgb (toByte r) (toByte g) (toByte b)

/-! ## Domain coloring of `f(w) = (w³ − 1)/(w³ + 1)` -/

/-- Complex cube, via two multiplications. -/
def cCube (z : C) : C := cMul z (cMul z z)

/-- The function domain-colored by the showcase: `f(w) = (w³ − 1)/(w³ + 1)`.
Its zeros are the six 6th roots of unity (`w³ = 1`), its poles the six 6th
roots of `-1` (`w³ = -1`); the hue winds once around each. -/
def evalF (w : C) : C :=
  let w3 := cCube w
  cDiv (cSub w3 (1.0, 0.0)) (cAdd w3 (1.0, 0.0))

/-- Domain-color a value `F = f(w)`: hue from `arg F`; value from the
fractional part of `log2 |F|`, so magnitude doublings read as crisp rings;
saturation ≈ 0.9 with a rolloff toward white near zeros (`|F|` small) and
toward black near poles (`|F|` huge). -/
def colorAtF (F : C) : Color :=
  let m := cAbs F
  let mSafe := if m < 1e-300 then 1e-300 else m
  let hue := cArg F
  let logm := Float.log2 mSafe
  let value0 := 0.55 + 0.45 * (logm - Float.floor logm)
  -- k0 → 1 as `|F| → 0` (near a zero); k1 → 1 as `|F| → ∞` (near a pole).
  let k0 := clamp01 ((-2.0 - logm) / 6.0)
  let k1 := clamp01 ((logm - 2.0) / 6.0)
  let sat := 0.9 * (1.0 - k0) * (1.0 - k1)
  let value := (value0 * (1.0 - k0) + 1.0 * k0) * (1.0 - k1)
  hsvToColor hue sat value

/-! ## Exact ℚ matrix → Float Möbius map -/

/-- The Möbius map `z ↦ (a·z + b)/(c·z + d)` for a matrix's exact `ℚ`
entries, projectively normalized (`normalize`) *before* the one-time
`ℚ → Float` conversion `Float.ofInt q.num / Float.ofNat q.den` — so any two
`ℚ` matrices that are equal after `normalize` (per `normalize_smul`)
produce the exact same four `Float`s and hence byte-identical renders. -/
def mobiusOfRat (A : Matrix (Fin 2) (Fin 2) ℚ) : C → C :=
  let (a, b, c, d) := entries (normalize A)
  let toF (q : ℚ) : Float := Float.ofInt q.num / Float.ofNat q.den
  let af := toF a
  let bf := toF b
  let cf := toF c
  let df := toF d
  fun z => cDiv (cAdd (cScale af z) (bf, 0.0)) (cAdd (cScale cf z) (df, 0.0))

/-! ## The view and the render loop -/

/-- Render width, in pixels. -/
def viewW : Nat := 384

/-- Render height, in pixels. -/
def viewH : Nat := 288

/-- Pixel `(px, py)` (top-left origin) → plane point, over
`[-1.6, 1.6] × [-1.2, 1.2]` (math-oriented: `y` increases upward). -/
def pixelToZ (px py : Nat) : C :=
  let x := -1.6 + 3.2 * (px.toFloat + 0.5) / viewW.toFloat
  let y := 1.2 - 2.4 * (py.toFloat + 0.5) / viewH.toFloat
  (x, y)

/-- Render one `viewW × viewH` `.rgb` frame: every pixel maps through
`mobius`, then `evalF`, then `colorAtF`. Builds the pixel `ByteArray`
directly with `push` in a single `Id.run do` loop (repo hot-loop law) —
no per-pixel `putPixel`. -/
def renderArt (mobius : C → C) : Image := Id.run do
  let mut data := ByteArray.emptyWithCapacity (viewW * viewH * 3)
  for py in [0:viewH] do
    for px in [0:viewW] do
      let col := colorAtF (evalF (mobius (pixelToZ px py)))
      data := data.push col.r |>.push col.g |>.push col.b
  return { width := viewW, height := viewH, mode := .rgb, data, palette? := none }

/-! ## Captions -/

/-- Caption bar height, in pixels. -/
def captionBarH : Nat := 18

/-- Append an 18px black caption bar *below* the art (never overlaid) and
draw `label` on it. Built via `Image.new` + `Image.paste`, the `.rgb`-mode
analogue of the tall-canvas pattern `Codec/Gif.lean` uses for its own
frame-strip rendering (`PixelSort.Render`'s `.data ++ bar` append only
works for 1-byte/pixel `.palette` mode; art here is `.rgb`, pre-quantize). -/
def frameWithCaption (art : Image) (label : String) : Image :=
  let canvas := Image.new art.width (art.height + captionBarH) .rgb Color.black
  let withArt := canvas.paste art ⟨0, 0⟩
  Draw.text withArt ⟨4, Int.ofNat art.height + 1⟩ label Color.white

/-! ## Swirl frames -/

/-- The animation parameter sequence: `k = 0…20`, then `20…−20`, then
`−20…0` — a full loop, `t = k / 24` feeding `M t` each frame. -/
def swirlKs : Array Int := Id.run do
  let mut ks : Array Int := #[]
  for k in [0:21] do
    ks := ks.push (Int.ofNat k)
  for k in [0:41] do
    ks := ks.push (20 - Int.ofNat k)
  for k in [0:21] do
    ks := ks.push (-20 + Int.ofNat k)
  return ks

/-- One swirl frame: `t = k / 24` fed through the exact ℚ layer's `M`
before ever touching `Float`, captioned with the exact parameter driving
it. Captioned (not bare) so every frame in the GIF shares one canvas size
with the finale frames below — `Gif.saveGif` requires uniform frame size. -/
def swirlFrame (k : Int) : Image :=
  frameWithCaption (renderArt (mobiusOfRat (M ((k : ℚ) / 24)))) s!"t = {k}/24"

/-- The swirl animation: `swirlKs.size` frames, 60ms each. -/
def swirlFrames : Array Gif.Frame := Id.run do
  let mut frames : Array Gif.Frame := Array.emptyWithCapacity swirlKs.size
  for k in swirlKs do
    frames := frames.push { image := swirlFrame k, durationMs := 60 }
  return frames

/-! ## Finale: the theorem made visible -/

/-- `M (1/3) * M (1/2)` — the left side of `normalized_composition`,
computed with `Matrix`'s computable `Mul` instance directly from the
frozen `M`. -/
def composedMat : Matrix (Fin 2) (Fin 2) ℚ := M (1/3) * M (1/2)

/-- `M 1` — the right side of `normalized_composition` (`1/3` and `1/2`
compose, by the tangent addition law, to parameter `1`). -/
def directMat : Matrix (Fin 2) (Fin 2) ℚ := M 1

/-- The art rendered from the composed matrix `M (1/3) * M (1/2)`. -/
def finaleArtA : Image := renderArt (mobiusOfRat composedMat)

/-- The art rendered from the direct matrix `M 1`. -/
def finaleArtB : Image := renderArt (mobiusOfRat directMat)

/-- The runtime witness: are the two finale renders' pixel data
byte-identical? `normalized_composition` guarantees this is `true` — if a
future edit ever makes it `false`, the render pipeline has diverged from
the exact layer (e.g. normalizing after the `Float` conversion instead of
before, or hand-written entries drifting from the `Matrix` `Mul` instance). -/
def byteWitness : Bool := finaleArtA.data == finaleArtB.data

/-- The three held finale frames, 1600ms each: the composed matrix, the
direct matrix, and the composed matrix again captioned with the runtime
byte-equality witness. -/
def finaleFrames : Array Gif.Frame :=
  #[ { image := frameWithCaption finaleArtA "M(1/3) then M(1/2)", durationMs := 1600 },
     { image := frameWithCaption finaleArtB "M(1) directly", durationMs := 1600 },
     { image := frameWithCaption finaleArtA
         s!"byte-identical: {byteWitness} (normalized_composition)", durationMs := 1600 } ]

/-! ## Assembled outputs -/

/-- The full GIF: the swirl loop, then the finale. -/
def allFrames : Array Gif.Frame := swirlFrames ++ finaleFrames

/-- The hero still: the `t = 1/2` swirl frame, full art, no caption bar. -/
def heroImage : Image := renderArt (mobiusOfRat (M (1/2)))

end Gallery.Mobius
