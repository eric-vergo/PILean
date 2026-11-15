/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean

/-!
# Image operation tests

Known answers and identities of `Image.crop`, `Image.paste`, `Image.convert`, the flips and
turns and `Image.resize`, on images of many shapes (1×1, 1×n, n×1, odd sizes, empty), and a
timing of resizing a 2000×1200 RGBA image with each filter.
-/

namespace PILeanTest.Image

open PILean PILean.Image

/-- A pseudo-random sample for a position, mode-independent and reproducible. -/
def noise (x y k : Nat) : UInt8 := ((x * 37 + y * 101 + k * 59 + x * y * 13) % 251).toUInt8

/-- A noise image. -/
def noisy (mode : Mode) (w h : Nat) : Image := generate mode w h noise

/-- Whether two images are equal. -/
def same (a b : Image) : Bool :=
  a.mode == b.mode && a.width == b.width && a.height == b.height && a.data == b.data

/-- Whether an image has the given size and is well formed. -/
def okSize (im : Image) (w h : Nat) : Bool :=
  im.width == w && im.height == h && im.data.size == w * h * im.mode.channels

/-- The shapes the operations are tried on. -/
def shapes : List (Nat × Nat) :=
  [(1, 1), (1, 5), (5, 1), (3, 7), (7, 3), (4, 4), (9, 6), (0, 4), (4, 0), (0, 0)]

/-- The modes. -/
def modes : List Mode := [.l, .rgb, .rgba]

/-- Whether a property holds for noise images of every shape and mode. -/
def forAll (p : Image → Bool) : Bool :=
  modes.all fun m => shapes.all fun (w, h) => p (noisy m w h)

/-- The same, for shapes with both sides positive. -/
def forAllPos (p : Image → Bool) : Bool :=
  modes.all fun m => shapes.all fun (w, h) => w == 0 || h == 0 || p (noisy m w h)

/-- Whether a pixel is as given. -/
def px (im : Image) (x y : Nat) (c : Rgba) : Bool := im.getpixel x y == c

/-- The checks of crop, paste and convert. -/
def editChecks : Array (String × Bool) :=
  let im := generate .rgba 4 4 fun x y k => (x * 16 + y * 4 + k).toUInt8
  let rgb := generate .rgb 4 4 fun x y k => (x * 16 + y * 4 + k + 100).toUInt8
  let red : Image := Image.new .rgb 2 2 ⟨255, 0, 0, 255⟩
  let blue := Image.new .rgb 4 4 ⟨0, 0, 255, 255⟩
  #[("crop: inside", okSize (im.crop 1 1 3 3) 2 2 &&
      (im.crop 1 1 3 3).getpixel 0 0 == im.getpixel 1 1 &&
      (im.crop 1 1 3 3).getpixel 1 1 == im.getpixel 2 2),
    ("crop: the whole image", same (im.crop 0 0 4 4) im),
    ("crop: partly outside, RGBA is transparent black",
      okSize (im.crop (-1) (-2) 2 2) 3 4 && px (im.crop (-1) (-2) 2 2) 0 0 ⟨0, 0, 0, 0⟩ &&
      px (im.crop (-1) (-2) 2 2) 1 2 (im.getpixel 0 0) &&
      px (im.crop (-1) (-2) 2 2) 2 3 (im.getpixel 1 1)),
    ("crop: partly outside, RGB and L are black",
      px (rgb.crop (-1) (-1) 2 2) 0 0 ⟨0, 0, 0, 255⟩ &&
      px ((noisy .l 3 3).crop 2 2 5 5) 2 2 ⟨0, 0, 0, 255⟩ &&
      px ((noisy .l 3 3).crop 2 2 5 5) 0 0 ((noisy .l 3 3).getpixel 2 2)),
    ("crop: wholly outside", okSize (im.crop 10 10 12 13) 2 3 &&
      (im.crop 10 10 12 13).data.data.all (· == 0)),
    ("crop: empty and inverted boxes", okSize (im.crop 2 2 2 5) 0 3 &&
      okSize (im.crop 3 3 1 1) 0 0),
    ("paste: replaces", let r := blue.paste red 1 1
      px r 1 1 ⟨255, 0, 0, 255⟩ && px r 2 2 ⟨255, 0, 0, 255⟩ && px r 0 0 ⟨0, 0, 255, 255⟩ &&
      px r 3 3 ⟨0, 0, 255, 255⟩ && okSize r 4 4),
    ("paste: clipped at the right and bottom", let r := blue.paste red 3 3
      px r 3 3 ⟨255, 0, 0, 255⟩ && px r 2 3 ⟨0, 0, 255, 255⟩ && okSize r 4 4),
    ("paste: clipped at the left and top", let r := blue.paste red (-1) (-1)
      px r 0 0 ⟨255, 0, 0, 255⟩ && px r 1 0 ⟨0, 0, 255, 255⟩ && okSize r 4 4),
    ("paste: wholly outside changes nothing", same (blue.paste red 9 9) blue &&
      same (blue.paste red (-9) 0) blue),
    ("paste: converts the mode",
      px (blue.paste (Image.new .l 1 1 ⟨7, 7, 7, 255⟩) 0 0) 0 0 ⟨7, 7, 7, 255⟩ &&
      px (blue.paste (Image.new .rgba 1 1 ⟨9, 8, 7, 3⟩) 0 0) 0 0 ⟨9, 8, 7, 255⟩ &&
      px ((Image.new .l 2 2 ⟨0, 0, 0, 255⟩).paste red 0 0) 0 0 ⟨76, 76, 76, 255⟩ &&
      px ((Image.new .rgba 2 2 ⟨1, 1, 1, 1⟩).paste red 0 0) 1 1 ⟨255, 0, 0, 255⟩),
    ("paste: mask 255 takes src, 0 keeps dst, 128 blends", Id.run do
      let m := generate .l 2 2 fun x _ _ => if x == 0 then 255 else 0
      let r := blue.paste red 0 0 (some m)
      let h := blue.paste red 0 0 (some (Image.new .l 2 2 ⟨128, 128, 128, 255⟩))
      return px r 0 0 ⟨255, 0, 0, 255⟩ && px r 1 0 ⟨0, 0, 255, 255⟩ && px r 0 1 ⟨255, 0, 0, 255⟩ &&
        px h 0 0 ⟨128, 0, 127, 255⟩),
    ("paste: the alpha of an RGBA mask", Id.run do
      let m := generate .rgba 2 2 fun x _ k => if k == 3 then (if x == 0 then 255 else 0) else 9
      let r := blue.paste red 1 1 (some m)
      return px r 1 1 ⟨255, 0, 0, 255⟩ && px r 2 1 ⟨0, 0, 255, 255⟩),
    ("paste: a mask smaller than src counts as 0", Id.run do
      let r := blue.paste red 0 0 (some (Image.new .l 1 1 ⟨255, 255, 255, 255⟩))
      return px r 0 0 ⟨255, 0, 0, 255⟩ && px r 1 1 ⟨0, 0, 255, 255⟩),
    ("blend: rounding", blend 0 255 128 == 128 && blend 255 0 128 == 127 &&
      blend 10 20 0 == 10 && blend 10 20 255 == 20 && blend 200 100 255 == 100),
    ("convert: L to RGB replicates", px ((noisy .l 3 3).convert .rgb) 1 2
      ⟨(noisy .l 3 3).getpixel 1 2 |>.r, (noisy .l 3 3).getpixel 1 2 |>.r,
        (noisy .l 3 3).getpixel 1 2 |>.r, 255⟩),
    ("convert: RGB to L is BT.601 luma", px ((Image.new .rgb 1 1 ⟨255, 0, 0, 255⟩).convert .l) 0 0
      ⟨76, 76, 76, 255⟩ && px ((Image.new .rgb 1 1 ⟨255, 255, 255, 255⟩).convert .l) 0 0
      ⟨255, 255, 255, 255⟩),
    ("convert: RGBA to RGB drops alpha without compositing",
      px ((Image.new .rgba 1 1 ⟨10, 20, 30, 0⟩).convert .rgb) 0 0 ⟨10, 20, 30, 255⟩ &&
      px ((Image.new .rgba 1 1 ⟨10, 20, 30, 0⟩).convert .l) 0 0 ⟨18, 18, 18, 255⟩),
    ("convert: L to RGB to L is the identity", forAll fun im =>
      let g := noisy .l im.width im.height
      same ((g.convert .rgb).convert .l) g),
    ("convert: RGB to RGBA to RGB is the identity", forAll fun im =>
      let g := noisy .rgb im.width im.height
      same ((g.convert .rgba).convert .rgb) g),
    ("convert: same mode, and the size is kept", forAll fun im =>
      same (im.convert im.mode) im &&
      modes.all fun m => okSize (im.convert m) im.width im.height && (im.convert m).mode == m)]

/-- The checks of the flips and the turns. -/
def turnChecks : Array (String × Bool) :=
  #[("flip: left-right twice is the identity", forAll fun im =>
      same im.flipLeftRight.flipLeftRight im),
    ("flip: top-bottom twice is the identity", forAll fun im =>
      same im.flipTopBottom.flipTopBottom im),
    ("flip: known answer", let im := noisy .l 3 2
      px im.flipLeftRight 0 0 (im.getpixel 2 0) && px im.flipTopBottom 1 0 (im.getpixel 1 1)),
    ("rotate90: four times is the identity", forAll fun im =>
      same im.rotate90.rotate90.rotate90.rotate90 im),
    ("rotate90 then rotate270 is the identity", forAll fun im =>
      same im.rotate90.rotate270 im && same im.rotate270.rotate90 im),
    ("rotate180 is the two flips", forAll fun im =>
      same im.rotate180 im.flipLeftRight.flipTopBottom &&
      same im.rotate180 im.rotate90.rotate90),
    ("rotate90: counter-clockwise, known answer", let im := noisy .rgb 3 2
      okSize im.rotate90 2 3 && px im.rotate90 0 0 (im.getpixel 2 0) &&
      px im.rotate90 1 0 (im.getpixel 2 1) && px im.rotate90 0 2 (im.getpixel 0 0)),
    ("rotate270: clockwise, known answer", let im := noisy .rgb 3 2
      okSize im.rotate270 2 3 && px im.rotate270 0 0 (im.getpixel 0 1) &&
      px im.rotate270 1 2 (im.getpixel 2 0)),
    ("transpose is rotate90 then top-bottom flip", forAll fun im =>
      same im.transpose im.rotate90.flipTopBottom &&
      same im.transpose im.rotate270.flipLeftRight),
    ("transpose twice is the identity", forAll fun im => same im.transpose.transpose im),
    ("turns: sizes", forAll fun im =>
      okSize im.flipLeftRight im.width im.height && okSize im.flipTopBottom im.width im.height &&
      okSize im.rotate180 im.width im.height && okSize im.rotate90 im.height im.width &&
      okSize im.rotate270 im.height im.width && okSize im.transpose im.height im.width)]

/-- The filters. -/
def filters : List Filter := [.nearest, .bilinear, .box, .lanczos]

/-- The checks of resizing. -/
def resizeChecks : Array (String × Bool) :=
  let checker := generate .l 2 2 fun x y _ => if (x + y) % 2 == 0 then 0 else 255
  let sizes : List (Nat × Nat) := [(1, 1), (1, 4), (4, 1), (3, 5), (7, 2), (13, 11), (0, 3)]
  #[("resize: the same size returns the same pixels, every filter", forAll fun im =>
      filters.all fun f => same (im.resize im.width im.height f) im),
    ("resize box: 2x downscale of a checker is the mean",
      same (checker.resize 1 1) (Image.new .l 1 1 ⟨128, 128, 128, 255⟩)),
    ("resize box: exact for integer ratios", Id.run do
      let im := generate .l 4 4 fun x y _ => (x * 10 + y).toUInt8
      let r := im.resize 2 2 .box
      -- block means 5.5 -> 6 and 27.5 -> 28; the whole image 16.5 -> 17
      return px r 0 0 ⟨6, 6, 6, 255⟩ && px r 1 1 ⟨28, 28, 28, 255⟩ &&
        px (im.resize 1 1) 0 0 ⟨17, 17, 17, 255⟩),
    ("resize box: a non-integer ratio takes area weights", Id.run do
      -- 3 -> 2 pixels: output 0 covers input 0 and half of input 1
      let im := generate .l 3 1 fun x _ _ => [0, 90, 180].getD x 0
      let r := im.resize 2 1 .box
      return px r 0 0 ⟨30, 30, 30, 255⟩ && px r 1 0 ⟨150, 150, 150, 255⟩),
    ("resize nearest: an upscale replicates", Id.run do
      let im := generate .rgb 2 2 fun x y k => (x * 100 + y * 20 + k).toUInt8
      let r := im.resize 4 4 .nearest
      let ok := (List.range 4).all fun y => (List.range 4).all fun x =>
        r.getpixel x y == im.getpixel (x / 2) (y / 2)
      return ok && okSize r 4 4),
    ("resize nearest: a downscale picks pixels", Id.run do
      let im := generate .l 4 1 fun x _ _ => (x * 10).toUInt8
      let r := im.resize 2 1 .nearest
      return px r 0 0 ⟨10, 10, 10, 255⟩ && px r 1 0 ⟨30, 30, 30, 255⟩),
    ("resize: a constant image stays constant, every filter and mode", modes.all fun m =>
      filters.all fun f => sizes.all fun (w, h) =>
        [(1, 1), (3, 3), (5, 2), (16, 9)].all fun (iw, ih) =>
          let c := Image.new m iw ih ⟨200, 100, 50, 255⟩
          same (c.resize w h f) (generate m w h fun _ _ k => c.sample 0 0 k)),
    ("resize bilinear: constant is exactly constant", Id.run do
      let c := Image.new .l 5 3 ⟨77, 77, 77, 255⟩
      return (c.resize 11 7 .bilinear).data.data.all (· == 77) &&
        (c.resize 2 2 .bilinear).data.data.all (· == 77)),
    ("resize lanczos: constant is exactly constant", Id.run do
      let c := Image.new .l 5 3 ⟨77, 77, 77, 255⟩
      return (c.resize 11 7 .lanczos).data.data.all (· == 77) &&
        (c.resize 2 2 .lanczos).data.data.all (· == 77)),
    ("resize bilinear: interpolates a ramp", Id.run do
      let im := generate .l 2 1 fun x _ _ => if x == 0 then 0 else 200
      let r := im.resize 4 1 .bilinear
      -- centres at -0.25.. : weights 1, .75/.25, .25/.75, 1 (edges clamp)
      return px r 0 0 ⟨0, 0, 0, 255⟩ && px r 1 0 ⟨50, 50, 50, 255⟩ &&
        px r 2 0 ⟨150, 150, 150, 255⟩ && px r 3 0 ⟨200, 200, 200, 255⟩),
    ("resize RGBA: transparent pixels do not bleed colour", filters.all fun f => Id.run do
      let im := generate .rgba 4 4 fun x _ k =>
        if x < 2 then (if k == 3 then 255 else 10) else (if k == 3 then 0 else 250)
      -- wherever an output pixel has any opacity, its colour is the opaque side's colour
      let good := fun (q : Image) => (List.range q.height).all fun y => (List.range q.width).all
        fun x => let c := q.getpixel x y
          c.a == 0 || (c.r == 10 && c.g == 10 && c.b == 10)
      return good (im.resize 2 2 f) && good (im.resize 8 8 f) && good (im.resize 3 3 f) &&
        (f != .box || px (im.resize 2 2 f) 0 0 ⟨10, 10, 10, 255⟩ &&
          px (im.resize 2 2 f) 1 0 ⟨0, 0, 0, 0⟩)),
    ("resize RGBA: half-transparent mean keeps colour", Id.run do
      let im := generate .rgba 2 1 fun x _ k =>
        if x == 0 then (if k == 3 then 255 else 100) else 0
      return px (im.resize 1 1 .box) 0 0 ⟨100, 100, 100, 128⟩),
    ("resize: sizes and mode on many shapes", filters.all fun f => forAll fun im =>
      [(1, 1), (1, 6), (6, 1), (5, 3), (2, 9), (0, 3), (3, 0)].all fun (w, h) =>
        okSize (im.resize w h f) w h && (im.resize w h f).mode == im.mode),
    ("resize: an empty source gives zero samples", filters.all fun f =>
      let r := (noisy .rgba 0 3).resize 2 2 f
      okSize r 2 2 && r.data.data.all (· == 0))]

/-- The checks that need no clock. -/
def checks : Array (String × Bool) := editChecks ++ turnChecks ++ resizeChecks

/-- Resizes a 2000×1200 RGBA image to 1000×600 with each filter, printing the times. The checks
are that the results have the right size. -/
def perfChecks : IO (Array (String × Bool)) := do
  let big := generate .rgba 2000 1200 fun x y k =>
    ((x * 7 + y * 3 + k * 50) % 256).toUInt8
  let mut out := #[]
  for (name, f) in [("nearest", Filter.nearest), ("bilinear", .bilinear), ("box", .box),
      ("lanczos", .lanczos)] do
    let t0 ← IO.monoNanosNow
    let r := big.resize 1000 600 f
    let ok := r.data.size == 1000 * 600 * 4
    let t1 ← IO.monoNanosNow
    IO.println s!"resize 2000x1200 RGBA -> 1000x600 {name}: {(t1 - t0) / 1000000} ms"
    out := out.push (s!"resize timing {name}", ok)
  return out

end PILeanTest.Image
