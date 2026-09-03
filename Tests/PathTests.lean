import Tests.Framework

/-!
# path tests

`PILean.Draw.Path` (polyline, dashed line, fixed-point trigonometry, arc,
circular arrow) and `Draw.textScaled`.

Every expected pixel set below is hand-derived: either enumerated directly,
or produced by a small independent Python reimplementation of the same
integer formulas (the fixed-point table and rounding rule, the midpoint
circle walk, the cross-product sector test, the DDA dash rule) written from
`PILean/Draw/Path.lean`'s docstrings rather than from its code. Nothing here
is compared against Pillow: PILean reproduces Pillow's *capabilities* and
angle convention, not its anti-aliased pixels.

Structural properties are checked as properties rather than as literals
where that is stronger — clipping is verified as *restriction* (drawing on a
small canvas equals the corresponding window of the same drawing on a large
one), reversal as *set equality*, and `textScaled` as exact block
replication of `text`.

The composite golden (`testdata/golden/path_composite.png`, plus a CRC-32 of
the raw pixel buffer) is a byte-identity lock: it is what detects a change
in rasterization across toolchains or refactors, and it is deliberately not
an independent oracle.
-/

namespace Tests.PathTests

open PILean PILean.Draw

/-- Build an image by setting exactly the pixels at `pts` to `color` on a
`w × h` `.rgb` canvas of `bg` (same convention as `Tests.DrawTests`). -/
private def expectFrom (w h : Nat) (pts : Array (Nat × Nat)) (color : Color)
    (bg : Color := Color.black) : Image :=
  pts.foldl (fun im (p : Nat × Nat) => im.putPixel (p.1 : Int) (p.2 : Int) color)
    (Image.new w h .rgb bg)

/-- Count pixels of `img` equal to `color`. -/
private def countColor (img : Image) (color : Color) : Nat := Id.run do
  let mut n := 0
  for y in [0:img.height] do
    for x in [0:img.width] do
      if img.getPixel! x y == color then
        n := n + 1
  return n

/-- Assert that `small` is pixel-for-pixel the window of `big` whose
top-left corner is `(ox, oy)`. Used to state "clipping is restriction": the
same geometry drawn on a canvas too small for it must agree with the part of
the large-canvas drawing that survives. -/
private def assertWindowAgrees (small big : Image) (ox oy : Int)
    (label : String := "window") : IO Unit := do
  for y in [0:small.height] do
    for x in [0:small.width] do
      assertEq (small.getPixel! x y) (big.getPixel! ((x : Int) + ox) ((y : Int) + oy))
        s!"{label} ({x},{y})"

/-- A fresh untouched `.rgb` canvas, for "this call changed nothing" checks. -/
private def blank (w h : Nat) : Image := Image.new w h .rgb

/-! ## Fixed-point trigonometry -/

def fixedPointTests : List TestCase := [
  test "sinTable has 91 entries spanning 0 … 65536" do
    assertEq sinTable.size 91 "size"
    assertEq sinTable[0]! 0 "sin 0°"
    assertEq sinTable[90]! 65536 "sin 90°"
    assertEq sinTable[30]! 32768 "sin 30° = 1/2 exactly at 16.16"
    assertEq sinTable[45]! 46341 "sin 45°"
    -- strictly increasing on [0°, 90°]
    for d in [0:90] do
      assertTrue (sinTable[d]! < sinTable[d + 1]!) s!"strictly increasing at {d}",
  test "fpRound rounds half away from zero" do
    assertEq (fpRound 0) 0 "0"
    assertEq (fpRound 32767) 0 "just under a half rounds down"
    assertEq (fpRound 32768) 1 "exactly a half rounds up"
    assertEq (fpRound 65536) 1 "one"
    assertEq (fpRound 98303) 1 "just under 1.5"
    assertEq (fpRound 98304) 2 "exactly 1.5 rounds away from zero"
    assertEq (fpRound (-32767)) 0 "negative just under a half"
    assertEq (fpRound (-32768)) (-1) "negative exact half rounds away from zero"
    assertEq (fpRound (-98304)) (-2) "negative 1.5",
  test "fpRound is odd: fpRound (-v) = - fpRound v" do
    for v in [0:400] do
      let vi : Int := (v : Int) * 977
      assertEq (fpRound (-vi)) (-(fpRound vi)) s!"v = {vi}",
  test "sinFP is exact at the four axis directions" do
    assertEq (sinFP 0) 0 "sin 0°"
    assertEq (sinFP 90) 65536 "sin 90°"
    assertEq (sinFP 180) 0 "sin 180°"
    assertEq (sinFP 270) (-65536) "sin 270°"
    assertEq (sinFP 360) 0 "sin 360°"
    assertEq (cosFP 0) 65536 "cos 0°"
    assertEq (cosFP 90) 0 "cos 90°"
    assertEq (cosFP 180) (-65536) "cos 180°"
    assertEq (cosFP 270) 0 "cos 270°",
  test "sinFP obeys the reflection, shift and period identities" do
    for d in [0:361] do
      let di : Int := (d : Int)
      assertEq (sinFP (180 - di)) (sinFP di) s!"sin(180° - {d}°)"
      assertEq (sinFP (di + 180)) (-(sinFP di)) s!"sin({d}° + 180°)"
      assertEq (sinFP (di + 360)) (sinFP di) s!"period at {d}°"
      assertEq (sinFP (di - 360)) (sinFP di) s!"negative period at {d}°"
      assertEq (cosFP di) (sinFP (di + 90)) s!"cos = sin shifted at {d}°",
  test "sinFP/cosFP stay inside [-65536, 65536] and satisfy the Pythagorean bound" do
    for d in [0:360] do
      let di : Int := (d : Int)
      let s := sinFP di
      let c := cosFP di
      assertTrue (-65536 ≤ s && s ≤ 65536) s!"sin range at {d}°"
      assertTrue (-65536 ≤ c && c ≤ 65536) s!"cos range at {d}°"
      -- rounding each entry to 16.16 moves s² + c² by at most a few ulps
      let n := s * s + c * c
      assertTrue (4294574080 ≤ n && n ≤ 4295360512) s!"s² + c² near 2^32 at {d}° (got {n})",
  test "circlePoint places the axis directions exactly" do
    assertEq (circlePoint ⟨50, 50⟩ 30 0) (⟨80, 50⟩ : Point) "0° is 3 o'clock"
    assertEq (circlePoint ⟨50, 50⟩ 30 90) (⟨50, 80⟩ : Point) "90° is 6 o'clock (y grows down)"
    assertEq (circlePoint ⟨50, 50⟩ 30 180) (⟨20, 50⟩ : Point) "180° is 9 o'clock"
    assertEq (circlePoint ⟨50, 50⟩ 30 270) (⟨50, 20⟩ : Point) "270° is 12 o'clock"
    assertEq (circlePoint ⟨50, 50⟩ 30 360) (⟨80, 50⟩ : Point) "360° wraps to 0°"
    assertEq (circlePoint ⟨50, 50⟩ 30 (-90)) (⟨50, 20⟩ : Point) "-90° = 270°",
  test "circlePoint at 30° matches the rounding rule by hand" do
    -- cosFP 30 = 56756, sinFP 30 = 32768; 10·56756 = 567560 → (567560+32768) >>> 16 = 9,
    -- 10·32768 = 327680 → (327680+32768) >>> 16 = 5.
    assertEq (circlePoint ⟨0, 0⟩ 10 30) (⟨9, 5⟩ : Point) "10 @ 30°"
    assertEq (circlePoint ⟨0, 0⟩ 10 (-30)) (⟨9, -5⟩ : Point) "10 @ -30° mirrors exactly"
    assertEq (circlePoint ⟨0, 0⟩ 0 137) (⟨0, 0⟩ : Point) "radius 0 is the center"
]

/-! ## Polylines -/

def polylineTests : List TestCase := [
  test "open polyline draws each consecutive segment" do
    let img := polyline (blank 8 8) #[⟨1, 1⟩, ⟨5, 1⟩, ⟨5, 5⟩] Color.red
    let pts : Array (Nat × Nat) :=
      #[(1,1),(2,1),(3,1),(4,1),(5,1),(5,2),(5,3),(5,4),(5,5)]
    assertImagesEq img (expectFrom 8 8 pts Color.red) "open polyline",
  test "closed polyline adds the last → first segment" do
    let img := polyline (blank 8 8) #[⟨1, 1⟩, ⟨5, 1⟩, ⟨5, 5⟩] Color.red (closed := true)
    let pts : Array (Nat × Nat) :=
      #[(1,1),(2,1),(2,2),(3,1),(3,3),(4,1),(4,4),(5,1),(5,2),(5,3),(5,4),(5,5)]
    assertImagesEq img (expectFrom 8 8 pts Color.red) "closed polyline",
  test "polyline equals the corresponding chain of Draw.line calls (also at width 3)" do
    let pts : Array Point := #[⟨1, 6⟩, ⟨6, 1⟩, ⟨11, 6⟩, ⟨6, 11⟩]
    for w in [1:4] do
      let viaPolyline := polyline (blank 13 13) pts Color.red (width := w) (closed := true)
      let mut viaLines := blank 13 13
      for i in [0:4] do
        viaLines := line viaLines pts[i]! pts[(i + 1) % 4]! Color.red w
      assertImagesEq viaPolyline viaLines s!"width {w}",
  test "fewer than two points draws nothing" do
    assertImagesEq (polyline (blank 8 8) #[] Color.red) (blank 8 8) "empty"
    assertImagesEq (polyline (blank 8 8) #[⟨3, 3⟩] Color.red) (blank 8 8) "single point"
    assertImagesEq (polyline (blank 8 8) #[⟨3, 3⟩] Color.red (closed := true)) (blank 8 8)
      "single point, closed",
  test "fully off-canvas polyline leaves the canvas unchanged" do
    let img := polyline (blank 8 8) #[⟨-50, -50⟩, ⟨-40, -40⟩, ⟨-30, -60⟩] Color.red
      (width := 3) (closed := true)
    assertImagesEq img (blank 8 8) "unchanged",
  test "partially off-canvas polyline keeps exactly the in-bounds pixels" do
    let img := polyline (blank 8 8) #[⟨-5, 4⟩, ⟨20, 4⟩, ⟨20, -3⟩] Color.red
    let pts : Array (Nat × Nat) := #[(0,4),(1,4),(2,4),(3,4),(4,4),(5,4),(6,4),(7,4)]
    assertImagesEq img (expectFrom 8 8 pts Color.red) "clipped row"
    assertTrue img.validate "image still valid"
]

/-! ## Dashed lines -/

def dashedLineTests : List TestCase := [
  test "horizontal dash 2 / gap 1 inks steps 0,1 then 3,4 then 6,7 then 9" do
    let img := dashedLine (blank 12 12) ⟨0, 0⟩ ⟨9, 0⟩ Color.red 2 1
    let pts : Array (Nat × Nat) := #[(0,0),(1,0),(3,0),(4,0),(6,0),(7,0),(9,0)]
    assertImagesEq img (expectFrom 12 12 pts Color.red) "dash 2 gap 1",
  test "shallow diagonal walks the major axis (N = |dx|)" do
    let img := dashedLine (blank 12 12) ⟨0, 0⟩ ⟨10, 4⟩ Color.red 3 2
    let pts : Array (Nat × Nat) := #[(0,0),(1,0),(2,1),(5,2),(6,2),(7,3),(10,4)]
    assertImagesEq img (expectFrom 12 12 pts Color.red) "dash 3 gap 2, dx > dy",
  test "steep diagonal walks the major axis (N = |dy|)" do
    let img := dashedLine (blank 12 12) ⟨0, 0⟩ ⟨4, 10⟩ Color.red 3 2
    let pts : Array (Nat × Nat) := #[(0,0),(0,1),(1,2),(2,5),(2,6),(3,7),(4,10)]
    assertImagesEq img (expectFrom 12 12 pts Color.red) "dash 3 gap 2, dy > dx",
  test "the pattern is phased from `a`, so reversing the segment changes it" do
    let fwd := dashedLine (blank 12 12) ⟨0, 0⟩ ⟨10, 4⟩ Color.red 3 2
    let rev := dashedLine (blank 12 12) ⟨10, 4⟩ ⟨0, 0⟩ Color.red 3 2
    let revPts : Array (Nat × Nat) := #[(0,0),(3,1),(4,2),(5,2),(8,3),(9,4),(10,4)]
    assertImagesEq rev (expectFrom 12 12 revPts Color.red) "reversed phase"
    assertTrue (countColor fwd Color.red == countColor rev Color.red)
      "same number of inked steps"
    assertTrue (fwd.getPixel! 1 0 != rev.getPixel! 1 0) "the two renderings differ",
  test "dash + gap = 0 draws a solid line (including dash = gap = 0)" do
    let img := dashedLine (blank 12 12) ⟨0, 0⟩ ⟨9, 0⟩ Color.red 0 0
    let pts : Array (Nat × Nat) :=
      #[(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(7,0),(8,0),(9,0)]
    assertImagesEq img (expectFrom 12 12 pts Color.red) "solid"
    let solid := dashedLine (blank 12 12) ⟨0, 0⟩ ⟨9, 0⟩ Color.red 7 0
    assertImagesEq solid (expectFrom 12 12 pts Color.red) "gap 0 is also solid",
  test "dash = 0 with a nonzero gap draws nothing" do
    assertImagesEq (dashedLine (blank 12 12) ⟨0, 0⟩ ⟨9, 0⟩ Color.red 0 3) (blank 12 12)
      "dash 0 gap 3"
    assertImagesEq (dashedLine (blank 12 12) ⟨0, 0⟩ ⟨9, 9⟩ Color.red 0 1 (width := 5))
      (blank 12 12) "dash 0 gap 1, thick",
  test "zero-length segment is one step, inked by the same rule" do
    assertEq (countColor (dashedLine (blank 8 8) ⟨3, 3⟩ ⟨3, 3⟩ Color.red 2 1) Color.red) 1
      "dash 2 gap 1 inks step 0"
    assertEq ((dashedLine (blank 8 8) ⟨3, 3⟩ ⟨3, 3⟩ Color.red 2 1).getPixel! 3 3) Color.red
      "at the point"
    assertEq (countColor (dashedLine (blank 8 8) ⟨3, 3⟩ ⟨3, 3⟩ Color.red 0 1) Color.red) 0
      "dash 0 gap 1 inks nothing"
    assertEq (countColor (dashedLine (blank 8 8) ⟨3, 3⟩ ⟨3, 3⟩ Color.red 0 0) Color.red) 1
      "dash + gap = 0 is solid, so the single step is inked",
  test "width > 1 stamps Draw.line's square on each inked step" do
    let img := dashedLine (blank 12 12) ⟨2, 5⟩ ⟨8, 5⟩ Color.red 1 2 (width := 3)
    -- steps 0, 3, 6 are inked, at x = 2, 5, 8; each stamps rows 4..6 of a 3-wide column
    let mut pts : Array (Nat × Nat) := #[]
    for cx in [2, 5, 8] do
      for dy in [0:3] do
        for dx in [0:3] do
          pts := pts.push (cx - 1 + dx, 4 + dy)
    assertImagesEq img (expectFrom 12 12 pts Color.red) "three 3×3 stamps"
    assertEq (countColor img Color.red) 27 "27 distinct pixels",
  test "fully off-canvas dashed line leaves the canvas unchanged" do
    assertImagesEq (dashedLine (blank 8 8) ⟨-50, -50⟩ ⟨-10, -50⟩ Color.red 2 1 (width := 3))
      (blank 8 8) "unchanged",
  test "partially off-canvas dashed line keeps exactly the in-bounds pixels" do
    let img := dashedLine (blank 8 8) ⟨-4, 2⟩ ⟨11, 2⟩ Color.red 2 2
    let pts : Array (Nat × Nat) := #[(0,2),(1,2),(4,2),(5,2)]
    assertImagesEq img (expectFrom 8 8 pts Color.red) "clipped dashes"
    assertTrue img.validate "image still valid"
]

/-! ## Arcs -/

def arcTests : List TestCase := [
  test "quarter arc (0° → 90°) matches the hand-derived midpoint pixels" do
    let img := arc (blank 16 16) ⟨8, 8⟩ 5 0 90 Color.red
    let pts : Array (Nat × Nat) := #[(8,13),(9,13),(10,12),(11,11),(12,10),(13,8),(13,9)]
    assertImagesEq img (expectFrom 16 16 pts Color.red) "0° → 90° (down-right quadrant)",
  test "sweep +90 and sweep -90 are different arcs sharing only the start ray" do
    let pos := arc (blank 16 16) ⟨8, 8⟩ 5 0 90 Color.red
    let neg := arc (blank 16 16) ⟨8, 8⟩ 5 0 (-90) Color.red
    let negPts : Array (Nat × Nat) := #[(8,3),(9,3),(10,4),(11,5),(12,6),(13,7),(13,8)]
    assertImagesEq neg (expectFrom 16 16 negPts Color.red) "0° → -90° (up-right quadrant)"
    assertEq (countColor pos Color.red) 7 "positive sweep pixel count"
    assertEq (countColor neg Color.red) 7 "negative sweep pixel count"
    -- they overlap in exactly the one pixel of the shared 0° ray
    let mut shared := 0
    for y in [0:16] do
      for x in [0:16] do
        if pos.getPixel! x y == Color.red && neg.getPixel! x y == Color.red then
          shared := shared + 1
    assertEq shared 1 "only the 0° ray pixel is shared"
    assertEq (pos.getPixel! 13 8) Color.red "0° ray in the positive sweep"
    assertEq (neg.getPixel! 13 8) Color.red "0° ray in the negative sweep",
  test "|sweep| ≥ 360 draws the whole circle, from any start" do
    let full := arc (blank 16 16) ⟨8, 8⟩ 5 0 360 Color.red
    let pts : Array (Nat × Nat) :=
      #[(3,7),(3,8),(3,9),(4,6),(4,10),(5,5),(5,11),(6,4),(6,12),(7,3),(7,13),(8,3),
        (8,13),(9,3),(9,13),(10,4),(10,12),(11,5),(11,11),(12,6),(12,10),(13,7),(13,8),(13,9)]
    assertImagesEq full (expectFrom 16 16 pts Color.red) "midpoint circle, radius 5"
    assertImagesEq (arc (blank 16 16) ⟨8, 8⟩ 5 17 720 Color.red) full "720° from 17°"
    assertImagesEq (arc (blank 16 16) ⟨8, 8⟩ 5 0 (-360) Color.red) full "-360°",
  test "a wide sector (> 180°) and its complement partition the circle" do
    let wide := arc (blank 16 16) ⟨8, 8⟩ 5 0 270 Color.red
    let narrow := arc (blank 16 16) ⟨8, 8⟩ 5 270 90 Color.red
    let full := arc (blank 16 16) ⟨8, 8⟩ 5 0 360 Color.red
    assertEq (countColor wide Color.red) 19 "wide sector pixel count"
    assertEq (countColor narrow Color.red) 7 "narrow sector pixel count"
    -- union is the full circle, intersection is exactly the two boundary rays
    let mut shared := 0
    for y in [0:16] do
      for x in [0:16] do
        let inWide := wide.getPixel! x y == Color.red
        let inNarrow := narrow.getPixel! x y == Color.red
        let inFull := full.getPixel! x y == Color.red
        assertEq (inWide || inNarrow) inFull s!"union at ({x},{y})"
        if inWide && inNarrow then shared := shared + 1
    assertEq shared 2 "the 0° and 270° boundary rays"
    assertEq (wide.getPixel! 13 8) Color.red "0° ray drawn by the wide sector"
    assertEq (wide.getPixel! 8 3) Color.red "270° ray drawn by the wide sector",
  test "opposite parametrizations of the same sector draw identical pixels" do
    let cw := arc (blank 41 41) ⟨20, 20⟩ 12 135 270 Color.red
    let ccw := arc (blank 41 41) ⟨20, 20⟩ 12 45 (-270) Color.red
    assertImagesEq cw ccw "(135°, +270°) = (45°, -270°)"
    assertEq (countColor cw Color.red) 49 "three quarters of a radius-12 circle",
  test "small radii: 1 and 2" do
    assertImagesEq (arc (blank 8 8) ⟨4, 4⟩ 1 0 360 Color.red)
      (expectFrom 8 8 #[(3,4),(4,3),(4,5),(5,4)] Color.red) "radius 1 is the 4-neighborhood"
    assertImagesEq (arc (blank 8 8) ⟨4, 4⟩ 2 0 360 Color.red)
      (expectFrom 8 8 #[(2,3),(2,4),(2,5),(3,2),(3,6),(4,2),(4,6),(5,2),(5,6),
                        (6,3),(6,4),(6,5)] Color.red) "radius 2",
  test "radius 0 and sweep 0 draw nothing" do
    assertImagesEq (arc (blank 8 8) ⟨4, 4⟩ 0 0 360 Color.red) (blank 8 8) "radius 0"
    assertImagesEq (arc (blank 8 8) ⟨4, 4⟩ 3 45 0 Color.red) (blank 8 8) "sweep 0"
    assertImagesEq (arc (blank 8 8) ⟨4, 4⟩ 0 45 0 Color.red (width := 4)) (blank 8 8) "both",
  test "width 2 stamps a 2×2 square on every arc pixel" do
    let img := arc (blank 16 16) ⟨8, 8⟩ 5 0 360 Color.red (width := 2)
    -- 24 circle pixels, each stamping a 2×2 block offset one pixel up-left; the
    -- blocks overlap only where the circle is 8-connected, leaving 64 pixels.
    assertEq (countColor img Color.red) 64 "thick ring pixel count"
    let thin := arc (blank 16 16) ⟨8, 8⟩ 5 0 360 Color.red
    for y in [0:16] do
      for x in [0:16] do
        if thin.getPixel! x y == Color.red then
          assertEq (img.getPixel! x y) Color.red s!"thin ⊆ thick at ({x},{y})",
  test "fully off-canvas arc leaves the canvas unchanged" do
    assertImagesEq (arc (blank 8 8) ⟨100, 100⟩ 5 0 360 Color.red (width := 3)) (blank 8 8)
      "far away"
    assertImagesEq (arc (blank 8 8) ⟨-100, 4⟩ 20 0 360 Color.red) (blank 8 8)
      "circle entirely to the left",
  test "partially off-canvas arc keeps exactly the in-bounds pixels" do
    let img := arc (blank 8 8) ⟨0, 0⟩ 5 0 360 Color.red
    let pts : Array (Nat × Nat) := #[(0,5),(1,5),(2,4),(3,3),(4,2),(5,0),(5,1)]
    assertImagesEq img (expectFrom 8 8 pts Color.red) "quarter circle in the corner"
    assertTrue img.validate "image still valid",
  test "clipping is restriction: small canvas = window of the large canvas" do
    let small := arc (blank 12 12) ⟨2, 3⟩ 9 30 300 Color.red (width := 2)
    let big := arc (blank 40 40) ⟨16, 17⟩ 9 30 300 Color.red (width := 2)
    assertWindowAgrees small big 14 14 "arc"
]

/-! ## Circular arrows -/

def circularArrowTests : List TestCase := [
  test "fixed geometry: tip and both head endpoints are exactly where the rule says" do
    -- center (50,50), r = 30, 0° → 90°: the end point is 90° = (50, 80).
    -- Travel at the end is 90° + 90° = 180° (leftward), so the head runs
    -- backwards from 0°, splayed ±30°:
    --   0°+30° = 30°:  (50 + fpRound(10·cosFP 30), 80 + fpRound(10·sinFP 30)) = (59, 85)
    --   0°-30° = -30°: (59, 75) by the odd symmetry of fpRound.
    let img := circularArrow (blank 100 100) ⟨50, 50⟩ 30 0 90 Color.red
      (headLength := 10) (headHalfAngleDeg := 30)
    assertEq (circlePoint ⟨50, 50⟩ 30 90) (⟨50, 80⟩ : Point) "tip"
    assertEq (circlePoint ⟨50, 80⟩ 10 30) (⟨59, 85⟩ : Point) "head endpoint at +30°"
    assertEq (circlePoint ⟨50, 80⟩ 10 (-30)) (⟨59, 75⟩ : Point) "head endpoint at -30°"
    assertEq (img.getPixel! 50 80) Color.red "tip pixel"
    assertEq (img.getPixel! 59 85) Color.red "first head endpoint pixel"
    assertEq (img.getPixel! 59 75) Color.red "second head endpoint pixel"
    -- and the whole rendering is exactly arc + the two head segments
    let expected := line (line (arc (blank 100 100) ⟨50, 50⟩ 30 0 90 Color.red)
      ⟨50, 80⟩ ⟨59, 85⟩ Color.red) ⟨50, 80⟩ ⟨59, 75⟩ Color.red
    assertImagesEq img expected "arc + two head segments",
  test "the turn icon: same arc pixels, head at opposite ends" do
    let cw := circularArrow (blank 41 41) ⟨20, 20⟩ 12 135 270 Color.white
      (headLength := 8) (headHalfAngleDeg := 30)
    let ccw := circularArrow (blank 41 41) ⟨20, 20⟩ 12 45 (-270) Color.white
      (headLength := 8) (headHalfAngleDeg := 30)
    let bare := arc (blank 41 41) ⟨20, 20⟩ 12 135 270 Color.white
    assertImagesEq (arc (blank 41 41) ⟨20, 20⟩ 12 45 (-270) Color.white) bare
      "the underlying arcs coincide"
    -- both renderings contain the shared arc …
    for y in [0:41] do
      for x in [0:41] do
        if bare.getPixel! x y == Color.white then
          assertEq (cw.getPixel! x y) Color.white s!"cw ⊇ arc at ({x},{y})"
          assertEq (ccw.getPixel! x y) Color.white s!"ccw ⊇ arc at ({x},{y})"
    -- … and differ: the clockwise head sits at 45°, the other at 135°
    assertEq (circlePoint ⟨20, 20⟩ 12 45) (⟨28, 28⟩ : Point) "clockwise tip"
    assertEq (circlePoint ⟨20, 20⟩ 12 135) (⟨12, 28⟩ : Point) "counterclockwise tip"
    assertEq (cw.getPixel! 36 26) Color.white "clockwise head endpoint (36,26)"
    assertEq (cw.getPixel! 30 20) Color.white "clockwise head endpoint (30,20)"
    assertEq (ccw.getPixel! 10 20) Color.white "counterclockwise head endpoint (10,20)"
    assertEq (ccw.getPixel! 4 26) Color.white "counterclockwise head endpoint (4,26)"
    assertTrue (cw.getPixel! 36 26 != ccw.getPixel! 36 26) "the two icons differ"
    assertTrue (countColor cw Color.white == countColor ccw Color.white)
      "mirror-image heads have the same pixel count",
  test "headLength = 0 draws the plain arc" do
    assertImagesEq (circularArrow (blank 41 41) ⟨20, 20⟩ 12 135 270 Color.red (headLength := 0))
      (arc (blank 41 41) ⟨20, 20⟩ 12 135 270 Color.red) "no head"
    assertImagesEq (circularArrow (blank 41 41) ⟨20, 20⟩ 12 135 270 Color.red (width := 3)
      (headLength := 0)) (arc (blank 41 41) ⟨20, 20⟩ 12 135 270 Color.red (width := 3))
      "no head, thick",
  test "radius 0 and sweep 0 draw nothing (no travel direction, so no head)" do
    assertImagesEq (circularArrow (blank 16 16) ⟨8, 8⟩ 0 0 90 Color.red) (blank 16 16)
      "radius 0"
    assertImagesEq (circularArrow (blank 16 16) ⟨8, 8⟩ 5 45 0 Color.red) (blank 16 16)
      "sweep 0",
  test "fully off-canvas circular arrow leaves the canvas unchanged" do
    assertImagesEq (circularArrow (blank 8 8) ⟨-100, -100⟩ 20 0 270 Color.red (width := 2))
      (blank 8 8) "unchanged",
  test "partially off-canvas circular arrow keeps exactly the in-bounds pixels" do
    let img := circularArrow (blank 8 8) ⟨0, 0⟩ 5 0 90 Color.red (headLength := 4)
    let pts : Array (Nat × Nat) :=
      #[(0,5),(1,4),(1,5),(1,6),(2,4),(2,6),(3,3),(3,7),(4,2),(5,0),(5,1)]
    assertImagesEq img (expectFrom 8 8 pts Color.red) "clipped arrow"
    assertTrue img.validate "image still valid",
  test "clipping is restriction: small canvas = window of the large canvas" do
    let small := circularArrow (blank 12 12) ⟨3, 4⟩ 10 200 (-250) Color.red (width := 2)
      (headLength := 5)
    let big := circularArrow (blank 40 40) ⟨17, 18⟩ 10 200 (-250) Color.red (width := 2)
      (headLength := 5)
    assertWindowAgrees small big 14 14 "circular arrow"
]

/-! ## Scaled text -/

/-- Is `scaled` the exact `scale`-fold block replication of `plain`? Both
images must be rendered at the origin, `scaled` being `scale` times as big
on each axis. -/
private def isBlockReplication (plain scaled : Image) (scale : Nat) : IO Unit := do
  assertEq scaled.width (plain.width * scale) "scaled width"
  assertEq scaled.height (plain.height * scale) "scaled height"
  for y in [0:scaled.height] do
    for x in [0:scaled.width] do
      assertEq (scaled.getPixel! x y) (plain.getPixel! (x / scale) (y / scale))
        s!"block replication at ({x},{y})"

def textScaledTests : List TestCase := [
  test "scale 1 is exactly `text`" do
    for s in ["A", "Hello, world!", "two\nlines", "", "\n\nx"] do
      let plain := text (blank 200 80) ⟨3, 2⟩ s Color.red
      let scaled := textScaled (blank 200 80) ⟨3, 2⟩ s Color.red 1
      assertImagesEq scaled plain s!"scale 1 = text for {repr s}",
  test "scale 1 is exactly `text` for an uncovered codepoint (fallback box)" do
    let s := String.singleton (Char.ofNat 0x2603)  -- ☃, outside spleen8x16
    let plain := text (blank 40 40) ⟨1, 1⟩ s Color.red
    let scaled := textScaled (blank 40 40) ⟨1, 1⟩ s Color.red 1
    assertImagesEq scaled plain "fallback box at scale 1"
    assertTrue (countColor plain Color.red > 0) "the fallback box has ink",
  test "scale 2 and 3 are exact block replications of the scale-1 render" do
    for scale in [2, 3] do
      let plain := text (Image.new 24 32 .rgb) ⟨0, 0⟩ "Ag\n%~" Color.red
      let scaled := textScaled (Image.new (24 * scale) (32 * scale) .rgb) ⟨0, 0⟩ "Ag\n%~"
        Color.red scale
      isBlockReplication plain scaled scale,
  test "the fallback box scales too (its border becomes `scale` thick)" do
    let s := String.singleton (Char.ofNat 0x2603)
    let plain := text (Image.new 8 16 .rgb) ⟨0, 0⟩ s Color.red
    let scaled := textScaled (Image.new 16 32 .rgb) ⟨0, 0⟩ s Color.red 2
    isBlockReplication plain scaled 2,
  test "scale 0 draws nothing" do
    assertImagesEq (textScaled (blank 40 40) ⟨2, 2⟩ "Hello" Color.red 0) (blank 40 40)
      "scale 0",
  test "textSizeScaled multiplies textSize componentwise" do
    for s in ["", "A", "Hello", "two\nlines", "a\nbcd\nef"] do
      let (w, h) := textSize s
      for scale in [0, 1, 2, 5] do
        assertEq (textSizeScaled s scale) (w * scale, h * scale) s!"{repr s} @ {scale}"
    assertEq (textSizeScaled "Hello" 1) (textSize "Hello") "scale 1 agrees with textSize"
    assertEq (textSizeScaled "Hello" 2) (80, 32) "5 glyphs × 8 px by one line × 16 px, doubled"
    assertEq (textSizeScaled "" 7) (0, 0) "empty string"
    assertEq (textSizeScaled "Hello" 0) (0, 0) "scale 0",
  test "the drawn text fits inside textSizeScaled's box" do
    let s := "Wq\ngj"
    let scale := 3
    let (w, h) := textSizeScaled s scale
    let img := textScaled (blank 120 120) ⟨5, 7⟩ s Color.red scale
    let box : Rect := ⟨5, 7, 5 + (w : Int), 7 + (h : Int)⟩
    for y in [0:120] do
      for x in [0:120] do
        if !box.contains ⟨x, y⟩ then
          assertEq (img.getPixel! x y) Color.black s!"nothing outside the box at ({x},{y})"
    assertTrue (countColor img Color.red > 0) "and something was drawn",
  test "fully off-canvas scaled text leaves the canvas unchanged" do
    assertImagesEq (textScaled (blank 12 12) ⟨-100, -100⟩ "Hi" Color.red 3) (blank 12 12)
      "far up-left"
    assertImagesEq (textScaled (blank 12 12) ⟨500, 500⟩ "Hi" Color.red 3) (blank 12 12)
      "far down-right",
  test "partially off-canvas scaled text clips to the window of the large render" do
    let small := textScaled (blank 12 12) ⟨-4, -4⟩ "Ag" Color.red 2
    let big := textScaled (blank 60 60) ⟨10, 10⟩ "Ag" Color.red 2
    assertWindowAgrees small big 14 14 "textScaled"
    assertTrue (countColor small Color.red > 0) "some ink survived the clip"
    assertTrue small.validate "image still valid"
]

/-! ## Zero-size canvases -/

def zeroSizeTests : List TestCase := [
  test "every path primitive is a no-op on 0×0, 0×h and w×0 images" do
    for (w, h) in [(0, 0), (0, 5), (5, 0)] do
      let img := Image.new w h .rgb
      let label := s!"{w}×{h}"
      assertEq (polyline img #[⟨-5, -5⟩, ⟨5, 5⟩, ⟨0, 9⟩] Color.red (width := 3)
        (closed := true)).data.size 0 s!"polyline {label}"
      assertEq (dashedLine img ⟨-5, -5⟩ ⟨9, 9⟩ Color.red 2 1 (width := 3)).data.size 0
        s!"dashedLine {label}"
      assertEq (dashedLine img ⟨0, 0⟩ ⟨0, 0⟩ Color.red 0 0).data.size 0
        s!"dashedLine degenerate {label}"
      assertEq (arc img ⟨0, 0⟩ 7 0 360 Color.red (width := 3)).data.size 0 s!"arc {label}"
      assertEq (circularArrow img ⟨0, 0⟩ 7 135 270 Color.red (width := 3)).data.size 0
        s!"circularArrow {label}"
      assertEq (textScaled img ⟨0, 0⟩ "Hi" Color.red 3).data.size 0 s!"textScaled {label}"
      assertTrue (Image.new w h .rgb).validate s!"canvas {label} still valid"
]

/-! ## Composite golden -/

/-- The composite scene: every primitive in `PILean.Draw.Path` plus
`textScaled`, on one 200×120 `.rgb` canvas, including geometry that runs off
the bottom-left corner so the golden also pins the clipped path. Pure
integer drawing throughout, so the buffer is byte-identical everywhere. -/
def composite : Image := Id.run do
  let mut img := Image.new 200 120 .rgb (Color.rgb 8 8 16)
  -- dashed rules
  img := dashedLine img ⟨0, 10⟩ ⟨199, 10⟩ (Color.rgb 60 90 200) 4 3
  img := dashedLine img ⟨100, 0⟩ ⟨100, 119⟩ (Color.rgb 60 90 200) 4 3
  -- a closed pentagon placed with circlePoint (0° at 3 o'clock, clockwise)
  let mut pent : Array Point := #[]
  for k in [0:5] do
    pent := pent.push (circlePoint ⟨44, 66⟩ 30 (72 * (k : Int) - 90))
  img := polyline img pent Color.red (width := 1) (closed := true)
  -- a wide arc and the two turn icons that share its center
  img := arc img ⟨146, 62⟩ 38 210 240 (Color.rgb 0 200 90) (width := 2)
  img := circularArrow img ⟨146, 62⟩ 26 135 270 Color.white (headLength := 9)
  img := circularArrow img ⟨146, 62⟩ 15 45 (-270) (Color.rgb 240 200 40) (headLength := 7)
  -- geometry that leaves the canvas at the bottom-left corner
  img := arc img ⟨6, 112⟩ 22 0 360 (Color.rgb 200 60 200) (width := 2)
  img := polyline img #[⟨-20, 90⟩, ⟨30, 118⟩, ⟨70, 130⟩] (Color.rgb 120 120 120)
  -- labels
  img := textScaled img ⟨5, 22⟩ "PATH" (Color.rgb 0 220 220) 2
  img := textScaled img ⟨108, 100⟩ "n=10" (Color.rgb 220 220 220) 1
  return img

def goldenTests : List TestCase := [
  test "composite raw pixel buffer has the recorded CRC-32" do
    let img := composite
    assertTrue img.validate "composite image is valid"
    assertEq img.width 200 "width"
    assertEq img.height 120 "height"
    assertEq img.data.size (200 * 120 * 3) "buffer size"
    assertEq (PILean.Compress.crc32 img.data) (0xed6a5025 : UInt32) "CRC-32 of the raw RGB buffer",
  test "composite PNG matches testdata/golden/path_composite.png" do
    match PILean.Png.encode composite with
    | .error e => fail s!"encode failed: {e}"
    | .ok bytes => Tests.golden "path_composite.png" bytes
]

/-- The `path` suite: `PILean.Draw.Path` and `Draw.textScaled`. -/
def suite : Tests.Suite :=
  { name := "path"
    cases := fixedPointTests ++ polylineTests ++ dashedLineTests ++ arcTests ++
             circularArrowTests ++ textScaledTests ++ zeroSizeTests ++ goldenTests }

end Tests.PathTests
