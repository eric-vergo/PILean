/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Text.Engine
import PILeanTest.Examples

/-!
# Lettering checks and specimen

Named checks of the single-stroke lettering (`PILean.Lettering`) and the text engine, and the
specimen sheet: every glyph at 12, 16 and 48 pixels and sample plot labels, as SVG and as PNG.

## Main definitions

* `PILeanTest.Lettering.checks`: the checks.
* `PILeanTest.Lettering.specimen`: the specimen's nodes.
* `PILeanTest.Lettering.writeSpecimen`: writes `lettering-specimen.svg` and `.png`.
* `PILeanTest.Lettering.svgText`: the text content of the `<text>` elements of an SVG document,
  which the checks use to see that every character of the examples' labels has a glyph.
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
   "θ = 45°   α ≤ β", "Waveform   minimum   maximum   0123456789",
   "x² + y₂ = z³   eⁱᵖ   H₂O   n⁻¹   ½ ¼ ¾   ™", "Ångström   café   Ñandú   Œuvre   Ørsted",
   "∑ᵢ₌₁ⁿ xᵢ ≤ ∫ f dx   ∀ε ∃δ   ⌊x⌋ ⟨u, v⟩   → ⇒ ↦", "α β γ δ ε ζ η θ   Γ Δ Θ Λ Ξ Π Φ Ψ Ω"]

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

/-- The ink of a glyph: the bounds of its centre lines widened by half the stroke width. -/
def ink? (c : Char) : Option (Float × Float × Float × Float) :=
  match (glyph c).strokes.bounds with
  | none => none
  | some b => some (b.x0 - 39, b.x1 + 39, b.y0 - 39, b.y1 + 39)

/-- Whether a glyph has a positive advance and its ink lies within `x ∈ [-100, advance + 100]`
and `y ∈ [-260, 900]` (units of the em). -/
def glyphOk (c : Char) : Bool :=
  let g := glyph c
  g.advance > 0 &&
    (match ink? c with
     | none => c.isWhitespace || (spec? c).isSome
     | some (x0, x1, y0, y1) => x0 ≥ -100 && x1 ≤ g.advance + 100 && y0 ≥ -260 && y1 ≤ 900)

/-- The characters of `charset` that satisfy `p`, as a string. -/
def charsWhere (p : Char → Bool) : String := String.ofList (charset.filter p)

/-- Whether `c` is a superscript letter, digit or sign of the typeface. -/
def isSuper (c : Char) : Bool := (superBase c).isSome

/-- Whether `c` is a subscript letter, digit or sign of the typeface. -/
def isSub (c : Char) : Bool := (subBase c).isSome

/-- Whether the ink of a superscript lies above `y = 100` (the x-height minus a margin of `410`). -/
def superOk (c : Char) : Bool :=
  match ink? c with
  | some (_, _, y0, _) => y0 ≥ 100
  | none => false

/-- Whether the ink of a subscript lies below `y = 380`. -/
def subOk (c : Char) : Bool :=
  match ink? c with
  | some (_, _, _, y1) => y1 ≤ 380
  | none => false

/-- The checks that every character of the labels of the examples has a glyph; the name of a
check lists the characters that lack one. -/
def labelChecks : Array (String × Bool) :=
  let entry (what : String) (svg : String) : String × Bool :=
    let lacking := missing (svgText svg)
    (s!"lettering: every character in the labels of {what} has a glyph (lacking: \
      {String.ofList lacking})", lacking.isEmpty)
  (Examples.gallery.map fun (name, fig) => entry name fig.toSvg) ++
  (Examples.graphs.map fun (stem, e, st) => entry stem (e.svg st)) ++
  (Examples.animations.map fun (name, a) => entry name a.toSvg)

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
  #[(s!"lettering: every character of the set has a design and is not the missing box \
      (lacking: {charsWhere fun c => (spec? c).isNone})", charset.all fun c => (spec? c).isSome),
    (s!"lettering: every glyph of the set has a positive advance and its ink within x from -100 \
      to advance + 100 and y from -260 to 900 (outside: {charsWhere (!glyphOk ·)})",
      charset.all glyphOk),
    ("lettering: the characters of the set are distinct",
      charset.eraseDups.length == charset.length),
    ("lettering: the set has 430 characters", charset.length == 430),
    (s!"lettering: the ink of every superscript is above y = 100 \
      (outside: {charsWhere fun c => isSuper c && !superOk c})",
      charset.all fun c => !isSuper c || superOk c),
    (s!"lettering: the ink of every subscript is below y = 380 \
      (outside: {charsWhere fun c => isSub c && !subOk c})",
      charset.all fun c => !isSub c || subOk c),
    ("lettering: no character the typeface draws is reported missing",
      missing (String.ofList charset) == []),
    ("lettering: missing lists the characters without a glyph once, in order",
      missing "a中b文中c" == ['中', '文']),
    ("lettering: svgText unescapes the text of an SVG document",
      svgText "<svg><text x=\"1\">a&amp;b &lt;&#176;&#x3b1;&gt;</text><text y=\"2\"/></svg>" ==
        "a&b <°α>"),
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
      ascent == 0.74 && descent == 0.2 && capHeight == 0.7 && xHeight == 0.51)] ++ labelChecks

end PILeanTest.Lettering
