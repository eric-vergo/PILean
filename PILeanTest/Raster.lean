/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILeanTest.Examples

/-!
# Rasteriser checks

Named checks of the rasteriser: coverage of shapes whose areas are known, both fill rules,
clipping to a rectangle and to a path, hostile input, strokes (widths, caps, joins, dashes,
hairlines on pixel centres), paints (gradients in linear light), compositing (source over in
linear light, group opacity), the sRGB tables against the transfer function, and determinism.

`lake exe pilean-test --compare-out DIR` writes, for each gallery figure, its SVG and its PNG
without text (`*-notext.svg`, `*-notext.png`) for `tools/compare-render.py`, which renders the
SVG with macOS `sips` and compares the pixels. `--bench` times a 2000 × 1200 plot.
-/

namespace PILeanTest.Raster

open PILean PILean.Raster PILean.Plot

/-- The sum of the coverage of every pixel of the spans, in 1/255 pixels. -/
def area (spans : Array Span) : Nat := spans.foldl (fun n s => n + s.len * s.alpha.toNat) 0

/-- The spans of polygons in a 64 × 64 image. -/
def cov (polys : Array (Array Point)) (rule : FillRule := .nonZero) (clip : IRect := ⟨0, 0, 64, 64⟩) :
    Array Span := (coverage polys rule 64 64 clip).getD #[]

/-- A square of side `s` at `(x, y)`. -/
def square (x y s : Float) : Array Point := #[⟨x, y⟩, ⟨x + s, y⟩, ⟨x + s, y + s⟩, ⟨x, y + s⟩]

/-- Whether `a` is within `tol` of `b`. -/
def near (a b tol : Nat) : Bool := (if a ≥ b then a - b else b - a) ≤ tol

/-- The coverage checks. -/
def coverageChecks : Array (String × Bool) :=
  let sq := cov #[square 10 10 8]
  let half := cov #[square 10.5 10.5 8]
  let tri := cov #[#[⟨0, 0⟩, ⟨20, 0⟩, ⟨0, 20⟩]]
  let circle := (Path.ellipse ⟨32, 32⟩ 20 20).flatten 0.01 |>.map (·.points)
  let ring := cov ((Path.ellipse ⟨32, 32⟩ 20 20).append (Path.ellipse ⟨32, 32⟩ 10 10)
    |>.flatten 0.01 |>.map (·.points)) .evenOdd
  let ringNz := cov ((Path.ellipse ⟨32, 32⟩ 20 20).append (Path.ellipse ⟨32, 32⟩ 10 10)
    |>.flatten 0.01 |>.map (·.points)) .nonZero
  #[("coverage: an aligned 8 × 8 square covers 64 pixels exactly",
      area sq == 64 * 255 && sq.all (·.alpha == 255)),
    ("coverage: a square off the grid by half a pixel covers 64 pixels in all",
      near (area half) (64 * 255) 32),
    ("coverage: a half-pixel-offset square's corner pixels are a quarter covered",
      spansAlpha half 10 10 == 64 && spansAlpha half 18 18 == 64),
    ("coverage: a right triangle of legs 20 covers 200 pixels", near (area tri) (200 * 255) 32),
    ("coverage: a disc of radius 20 covers π · 400 pixels within 0.5 %",
      near (area (cov circle)) (1256 * 255) (6 * 255)),
    ("coverage: even-odd ring has a hole", spansAlpha ring 32 32 == 0 &&
      spansAlpha ring 32 18 == 255),
    ("coverage: non-zero fills the same-direction inner circle", spansAlpha ringNz 32 32 == 255),
    ("coverage: reversed inner circle under non-zero is a hole",
      spansAlpha (cov #[square 10 10 40, (square 20 20 20).reverse]) 30 30 == 0),
    ("coverage: every alpha in [1, 255]", (cov circle).all (fun s => s.alpha > 0)),
    ("coverage: clipped to a rectangle stays inside it",
      (cov circle .nonZero ⟨20, 25, 40, 30⟩).all fun s =>
        20 ≤ s.x && s.x + s.len ≤ 40 && 25 ≤ s.y && s.y < 30),
    ("coverage: a shape outside the image covers nothing",
      (cov #[square (-100) (-100) 50]).isEmpty && (cov #[square 100 100 50]).isEmpty),
    ("coverage: a shape far left still covers the pixels it reaches",
      area (cov #[#[⟨-1000000, 5⟩, ⟨3, 5⟩, ⟨3, 6⟩, ⟨-1000000, 6⟩]]) == 3 * 255),
    ("coverage: non-finite and huge coordinates end cleanly",
      (coverage #[#[⟨0 / 0, 1⟩, ⟨1e300, -1e300⟩, ⟨5, 5⟩]] .nonZero 64 64 ⟨0, 0, 64, 64⟩).isSome),
    ("coverage: too many points are refused",
      (coverage #[Array.replicate (maxPoints + 1) ⟨1, 1⟩] .nonZero 4 4 ⟨0, 0, 4, 4⟩).isNone),
    ("coverage: degenerate polygons cover nothing",
      (cov #[#[⟨1, 1⟩], #[⟨1, 1⟩, ⟨5, 5⟩], #[⟨1, 1⟩, ⟨5, 1⟩, ⟨9, 1⟩]]).isEmpty)]

/-- The coverage of a stroke of a path in a 64 × 64 image. -/
def strokeCov (p : Path) (st : Stroke) : Array Span := cov (strokePolygons p st)

/-- The stroke checks. -/
def strokeChecks : Array (String × Bool) :=
  let seg := Path.polyline #[⟨10, 20.5⟩, ⟨30, 20.5⟩]
  let corner := Path.polyline #[⟨10, 10⟩, ⟨30, 10⟩, ⟨30, 30⟩]
  #[("stroke: a one-pixel hairline on a pixel centre covers one row exactly",
      let s := strokeCov seg { width := 1 }
      area s == 20 * 255 && s.all (fun sp => sp.y == 20 && sp.alpha == 255)),
    ("stroke: crisp puts coordinates on pixel centres", Raster.crisp 7.2 == 7.5 && Raster.crisp 7.9 == 7.5),
    ("stroke: width 4 butt covers 80 pixels",
      near (area (strokeCov seg { width := 4 })) (80 * 255) 64),
    ("stroke: square caps add half a width at each end",
      near (area (strokeCov seg { width := 4, cap := .square })) (96 * 255) 64),
    ("stroke: round caps add a disc",
      near (area (strokeCov seg { width := 4, cap := .round })) 23606 128),
    ("stroke: a miter join fills the outer corner square (two 20 × 4 arms meeting: 156 + 4)",
      near (area (strokeCov corner { width := 4, join := .miter })) (160 * 255) 64),
    ("stroke: a bevel join fills half the outer corner square",
      near (area (strokeCov corner { width := 4, join := .bevel })) (158 * 255) 64),
    ("stroke: a round join is between bevel and miter",
      let r := area (strokeCov corner { width := 4, join := .round })
      r > 158 * 255 + 64 && r < 160 * 255 - 64),
    ("stroke: a sharp miter beyond the limit falls back to a bevel",
      let sharp := Path.polyline #[⟨10, 10⟩, ⟨50, 12⟩, ⟨10, 14⟩]
      area (strokeCov sharp { width := 4, join := .miter, miterLimit := 2 }) ==
        area (strokeCov sharp { width := 4, join := .bevel })),
    ("stroke: dashes 5 on 5 off cover half the length",
      area (strokeCov (Path.polyline #[⟨0, 20.5⟩, ⟨40, 20.5⟩]) { width := 1, dash := #[5, 5] })
        == 20 * 255),
    ("stroke: a dash offset shifts the pattern",
      let s := strokeCov (Path.polyline #[⟨0, 20.5⟩, ⟨40, 20.5⟩])
        { width := 1, dash := #[5, 5], dashOffset := 5 }
      spansAlpha s 2 20 == 0 && spansAlpha s 7 20 == 255),
    ("stroke: a closed square outline's corners are filled",
      area (strokeCov (Path.rect 10 10 20 20) { width := 2 }) == (22 * 22 - 18 * 18) * 255),
    ("stroke: zero width and zero-length paths stroke nothing",
      (strokeCov seg { width := 0 }).isEmpty &&
        (strokeCov (Path.polyline #[⟨5, 5⟩, ⟨5, 5⟩]) { width := 3 }).isEmpty),
    ("stroke: a round-capped dot is a disc",
      near (area (cov (polylinePieces { width := 10, cap := .round } #[⟨20, 20⟩, ⟨20, 20⟩] false)))
        (79 * 255) 255)]

/-- The paint and compositing checks. -/
def paintChecks : Array (String × Bool) :=
  let red : Rgba := ⟨255, 0, 0, 255⟩
  let blue : Rgba := ⟨0, 0, 255, 255⟩
  let solidRed := (Draw.new 4 4 ⟨255, 255, 255, 255⟩).fill (Path.rect 0 0 4 4) (.solid red)
  let halfA := (Draw.new 4 4 ⟨255, 255, 255, 255⟩).fill (Path.rect 0 0 4 4)
    (.solid ⟨0, 0, 0, 128⟩)
  let g := Paint.linear ⟨1, 0⟩ ⟨101, 0⟩ #[⟨0, red⟩, ⟨1, blue⟩]
  let grp := (Draw.new 4 4 ⟨255, 255, 255, 255⟩).group 0.5 fun d =>
    (d.fill (Path.rect 0 0 4 4) (.solid red)).fill (Path.rect 0 0 4 4) (.solid red)
  let twice := ((Draw.new 4 4 ⟨255, 255, 255, 255⟩).fill (Path.rect 0 0 4 4) (.solid red) (opacity := 0.5)).fill
    (Path.rect 0 0 4 4) (.solid red) (opacity := 0.5)
  #[("paint: an opaque fill replaces the background", (solidRed.canvas.get 1 1).toRgba == red),
    ("paint: black at alpha 128 over white mixes in linear light (sRGB 187, not 127)",
      let c := (halfA.canvas.get 1 1).toRgba
      c.r == 187 && c.g == 187 && c.b == 187 && c.a == 255),
    ("paint: the sRGB tables round-trip every 8-bit value",
      (List.range 256).all fun i => encode16 (decode8 i.toUInt8) == i.toUInt8),
    ("paint: the sRGB decode table is the transfer function to the nearest 1/65535",
      (List.range 256).all fun i =>
        let v := (srgbDecode (i.toFloat / 255) * 65535 + 0.5).floor.toUInt64.toNat
        decode8 i.toUInt8 == v),
    ("paint: a gradient is its first stop at the start and its last at the end",
      (g.at 0 0).toRgba == red && (g.at 120 0).toRgba == blue),
    ("paint: a gradient's middle is the linear-light mix (sRGB 188, 0, 188)",
      let c := (g.at 50 0).toRgba
      near c.r.toNat 188 1 && c.g == 0 && near c.b.toNat 188 1),
    ("paint: a radial gradient is its first stop at the centre",
      ((Paint.radial ⟨10, 10⟩ 5 #[⟨0, red⟩, ⟨1, blue⟩]).at 9 9).toRgba.r > 200),
    ("paint: group opacity does not let the group's parts show through each other",
      (grp.canvas.get 1 1).toRgba != (twice.canvas.get 1 1).toRgba),
    ("paint: a clip path limits painting",
      let d := ((Draw.new 10 10 ⟨255, 255, 255, 255⟩).withClipPath (Path.rect 0 0 5 10)).fill
        (Path.rect 0 0 10 10) (.solid red)
      (d.canvas.get 2 2).toRgba == red && (d.canvas.get 7 2).toRgba == ⟨255, 255, 255, 255⟩),
    ("paint: an RGB image of an opaque drawing", (solidRed.toImage .rgb).getpixel 0 0 == red),
    ("paint: a transparent canvas gives transparent pixels",
      (Draw.new 2 2 ⟨0, 0, 0, 0⟩).toImage.getpixel 0 0 == ⟨0, 0, 0, 0⟩)]

/-- A figure resized (its layout is in pixels). -/
def scaled (fig : Figure) (w h : Float) : Figure := { fig with width := w, height := h }

/-- The checks that need IO: the gallery's PNGs are deterministic. -/
def ioChecks : IO (Array (String × Bool)) := do
  let mut out := #[]
  for (name, fig) in PILeanTest.Examples.gallery do
    out := out.push (s!"raster: {name} renders to the same PNG twice", fig.toPng == fig.toPng)
  return out

/-- The SVG nodes without their `text` elements, nested at most `fuel` deep. -/
def stripText (fuel : Nat) (n : Svg.Node) : Option Svg.Node :=
  match fuel, n with
  | 0, _ => none
  | _, .element "text" _ _ => none
  | fuel + 1, .element name attrs children =>
    some (.element name attrs (children.filterMap (stripText fuel)))
  | _ + 1, t => some t

/-- Writes each gallery figure's SVG and PNG without text into `dir`. -/
def writeCompare (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  for (name, fig) in PILeanTest.Examples.gallery do
    let nodes := fig.render.filterMap (stripText 64)
    let base := (System.FilePath.mk name).fileStem.getD name
    IO.FS.writeFile (dir / s!"{base}-notext.svg") (Svg.document fig.width fig.height nodes)
    let img := (Svg.rasterize fig.width.round.toUInt64.toNat fig.height.round.toUInt64.toNat
      nodes ⟨255, 255, 255, 255⟩).toImage .rgb
    match img.writePng with
    | .ok b => IO.FS.writeBinFile (dir / s!"{base}-notext.png") b
    | .error e => throw (IO.userError e.toString)
    IO.println s!"{dir}/{base}-notext.svg and .png"

/-- Times rendering and encoding the function plot at 2000 × 1200 (best of three). -/
def bench : IO Unit := do
  let fig := scaled PILeanTest.Examples.functions 2000 1200
  let mut best := (0, 0, 0)
  for i in [0:3] do
    let t0 ← IO.monoNanosNow
    let img := fig.toImage
    let t1 ← IO.monoNanosNow
    let png := img.writePng
    let t2 ← IO.monoNanosNow
    let size := match png with | .ok b => b.size | .error _ => 0
    let r := ((t1 - t0) / 1000000, (t2 - t1) / 1000000, size)
    if i == 0 || r.1 + r.2.1 < best.1 + best.2.1 then best := r
  IO.println s!"2000 × 1200 function plot: render {best.1} ms, PNG encode {best.2.1} ms, \
    {best.2.2} bytes"

/-- All the pure checks. -/
def checks : Array (String × Bool) := coverageChecks ++ strokeChecks ++ paintChecks

end PILeanTest.Raster
