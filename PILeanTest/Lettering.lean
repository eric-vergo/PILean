/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Text.Engine

/-!
# Lettering checks and specimen

Named checks of the single-stroke lettering (`PILean.Lettering`) and the text engine, and the
specimen sheet: every glyph at 12, 16 and 48 pixels and sample plot labels, as SVG and as PNG.

## Main definitions

* `PILeanTest.Lettering.checks`: the checks.
* `PILeanTest.Lettering.specimen`: the specimen's nodes.
* `PILeanTest.Lettering.writeSpecimen`: writes `lettering-specimen.svg` and `.png`.
-/

namespace PILeanTest.Lettering

open PILean PILean.Lettering PILean.Raster

/-- The text colour of the specimen. -/
def ink : Rgba := ⟨51, 51, 51, 255⟩

/-- A line of lettering at `(x, y)` (the baseline origin) as a stroked path. -/
def line (s : String) (x y size : Float) (weight : Float := 1) (tracking : Float := 0) :
    Svg.Node :=
  let (p, w) := shape s size weight tracking
  Svg.path (p.transform (Affine.translate x y)) none (some ink) w
    #[("stroke-linecap", "round"), ("stroke-linejoin", "round")]

/-- The characters of the typeface in rows of at most `n`. -/
def rows (n : Nat) : List String :=
  let rec go (fuel : Nat) (cs : List Char) : List String :=
    match fuel, cs with
    | 0, _ => []
    | _, [] => []
    | fuel + 1, cs => String.ofList (cs.take n) :: go fuel (cs.drop n)
  go (charset.length + 1) charset

/-- The sample labels of a plot. -/
def samples : List String :=
  ["−2.5   0   2.5   5.0   7.5   10.0", "Trigonometric functions", "sin x / x",
   "π(n)", "x   y   n / ln n", "Collatz stopping times",
   "θ = 45°   α ≤ β", "Waveform   minimum   maximum   0123456789"]

/-- The specimen's nodes on a white page and its height. -/
def specimen (width : Float) : Array Svg.Node × Float := Id.run do
  let mut nodes : Array Svg.Node := #[]
  let mut y := 24.0
  for size in [12.0, 16.0, 24.0, 48.0] do
    for s in samples do
      y := y + size * 1.5
      nodes := nodes.push (line s 20 y size)
    y := y + 16
  for (size, n) in [(48.0, 22), (16.0, 36), (12.0, 36)] do
    for s in rows n do
      y := y + size * 1.5
      nodes := nodes.push (line s 20 y size (tracking := size / 8))
    y := y + 16
  nodes := nodes.push (line "Title at weight 1.35" 20 (y + 40) 28 1.35)
  y := y + 70
  let page := Svg.rect 0 0 width y (some ⟨255, 255, 255, 255⟩)
  return (#[page] ++ nodes, y)

/-- Writes `lettering-specimen.svg` and `lettering-specimen.png` into `dir`. -/
def writeSpecimen (dir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dir
  let width := 1200.0
  let (nodes, height) := specimen width
  IO.FS.writeFile (dir / "lettering-specimen.svg") (Svg.document width height nodes)
  let img := (Svg.rasterize width.round.toUInt64.toNat height.round.toUInt64.toNat nodes
    ⟨255, 255, 255, 255⟩).toImage .rgb
  match img.writePng with
  | .ok b => IO.FS.writeBinFile (dir / "lettering-specimen.png") b
  | .error e => throw (IO.userError e.toString)

/-- Whether a glyph has a positive advance and its centre lines lie in the em box. -/
def glyphOk (c : Char) : Bool :=
  let g := glyph c
  g.advance > 0 &&
    (match g.strokes.bounds with
     | none => c == ' '
     | some b => b.x0 ≥ 0 && b.x1 ≤ g.advance && b.y0 ≥ -260 && b.y1 ≤ 800)

/-- The sum of the advances of a string in em units. -/
def advances (s : String) : Float := s.foldl (fun a c => a + (glyph c).advance) 0

/-- The checks of the lettering. -/
def checks : Array (String × Bool) :=
  let s := "Trigonometric functions"
  let (p1, w1) := shape s 16
  let (p2, w2) := shape s 16
  let (pe, _) := shape "" 16
  let big := shape "Aa" 1e12
  let nan := shape "Aa" (0.0 / 0.0)
  let inf := shape "Aa" (1.0 / 0.0)
  let neg := shape "Aa" (-3)
  let miss := glyph '中'
  #[("lettering: every glyph of the set is inside the em box with a positive advance",
      charset.all glyphOk),
    ("lettering: the set has 131 characters", charset.length == 131),
    ("lettering: the digits share one advance of 560",
      "0123456789".toList.all fun c => (glyph c).advance == 560),
    ("lettering: the minus sign is as wide as the plus sign",
      (glyph '−').advance == (glyph '+').advance),
    ("lettering: space advances 260", (glyph ' ').advance == 260),
    ("lettering: measure is the sum of the advances scaled",
      (measure s 16 - advances s * 16 / 1000).abs < 1e-9),
    ("lettering: measure adds the tracking between characters",
      (measure "abc" 10 2 - measure "abc" 10 - 4).abs < 1e-9),
    ("lettering: an unknown character is the missing-glyph box",
      miss.advance == 600 && miss.strokes == missingGlyph.strokes && !miss.strokes.cmds.isEmpty),
    ("lettering: shapes are deterministic", p1 == p2 && w1 == w2),
    ("lettering: the stroke width is 78 units of the size", (w1 - 78 * 16 / 1000).abs < 1e-9),
    ("lettering: the weight scales the stroke width",
      ((shape "x" 20 1.5).2 - 1.5 * (shape "x" 20).2).abs < 1e-9),
    ("lettering: the empty string has no shape and no width",
      pe.cmds.isEmpty && measure "" 16 == 0),
    ("lettering: a huge size gives an empty path", big.1.cmds.isEmpty && measure s 1e12 == 0),
    ("lettering: a non-finite or negative size gives an empty path",
      nan.1.cmds.isEmpty && inf.1.cmds.isEmpty && neg.1.cmds.isEmpty),
    ("lettering: the shape is in screen coordinates (capitals rise above the baseline)",
      match (shape "H" 100).1.bounds with
      | some b => b.y1 < 1 && b.y0 < -60 && b.y0 > -75
      | none => false),
    ("lettering: the shape starts at the baseline origin with the left bearing",
      match (shape "H" 1000).1.bounds with
      | some b => (b.x0 - 109).abs < 1
      | none => false),
    ("lettering: text engine measures like the lettering",
      (TextEngine.lettering.measure s 16 - measure s 16).abs < 1e-9),
    ("lettering: text engine shapes with centre lines",
      let sh := TextEngine.lettering.shape s 16 1
      sh.fill.cmds.isEmpty && sh.strokes == p1 && sh.strokeWidth == w1),
    ("lettering: the metrics are fractions of the size",
      ascent == 0.74 && descent == 0.2 && capHeight == 0.7 && xHeight == 0.51)]

end PILeanTest.Lettering
