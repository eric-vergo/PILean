import Tests.Framework
import Tests.Prng

/-!
# draw tests

Drawing primitives incl. clipping at every edge. Owned by WP5 — that work package fills in `cases`.

Most expected pixel sets are hand-derived (by direct enumeration or a
small independent Python reimplementation of the same integer formulas
used in `PILean.Draw.Basic`, never by comparison against Pillow — drawing
capability parity is in scope, quirk-for-quirk pixel parity is not) and
then encoded as literal coordinate lists or ASCII grids below.
-/

namespace Tests.DrawTests

open PILean PILean.Draw

/-- Build an image by setting exactly the pixels at `pts` to `color` on a
`w × h` `.rgb` canvas of `bg` (mirrors how the tests assert: same
`putPixel`-chain style used by `Image.new`/`putPixel` already under test in
`ScaffoldTests`). -/
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

/-- Are all pixels of `img` outside `r` equal to `bg`? -/
private def onlyInsideChanged (img : Image) (r : Rect) (bg : Color) : Bool := Id.run do
  let mut ok := true
  for y in [0:img.height] do
    for x in [0:img.width] do
      if !(r.contains ⟨x, y⟩) then
        if img.getPixel! x y != bg then
          ok := false
  return ok

def pointTests : List TestCase := [
  test "point sets exactly one pixel" do
    let img := point (Image.new 4 4 .rgb) ⟨2, 1⟩ Color.red
    assertEq (img.getPixel! 2 1) Color.red "set pixel"
    assertEq (countColor img Color.red) 1 "only one pixel changed",
  test "point off-canvas clips silently" do
    let img := point (Image.new 4 4 .rgb) ⟨-1, 0⟩ Color.red
    assertEq (countColor img Color.red) 0 "no pixel changed"
]

def lineTests : List TestCase := [
  test "horizontal line" do
    let img := line (Image.new 8 8 .rgb) ⟨0, 3⟩ ⟨5, 3⟩ Color.red
    let expected := expectFrom 8 8 #[(0,3),(1,3),(2,3),(3,3),(4,3),(5,3)] Color.red
    assertImagesEq img expected "horizontal",
  test "vertical line" do
    let img := line (Image.new 8 8 .rgb) ⟨3, 0⟩ ⟨3, 5⟩ Color.red
    let expected := expectFrom 8 8 #[(3,0),(3,1),(3,2),(3,3),(3,4),(3,5)] Color.red
    assertImagesEq img expected "vertical",
  test "45° diagonal line, both directions" do
    let fwd := line (Image.new 8 8 .rgb) ⟨0, 0⟩ ⟨4, 4⟩ Color.red
    let expectedFwd := expectFrom 8 8 #[(0,0),(1,1),(2,2),(3,3),(4,4)] Color.red
    assertImagesEq fwd expectedFwd "0,0 -> 4,4"
    let anti := line (Image.new 8 8 .rgb) ⟨0, 4⟩ ⟨4, 0⟩ Color.red
    let expectedAnti := expectFrom 8 8 #[(0,4),(1,3),(2,2),(3,1),(4,0)] Color.red
    assertImagesEq anti expectedAnti "0,4 -> 4,0"
    let rev := line (Image.new 8 8 .rgb) ⟨4, 4⟩ ⟨0, 0⟩ Color.red
    assertImagesEq rev expectedFwd "4,4 -> 0,0 (reversed) matches forward set",
  test "shallow and steep octants" do
    let shallow := line (Image.new 8 8 .rgb) ⟨0, 0⟩ ⟨6, 2⟩ Color.red
    let expectedShallow := expectFrom 8 8 #[(0,0),(1,0),(2,1),(3,1),(4,1),(5,2),(6,2)] Color.red
    assertImagesEq shallow expectedShallow "shallow (dx > dy)"
    let steep := line (Image.new 8 8 .rgb) ⟨0, 0⟩ ⟨2, 6⟩ Color.red
    let expectedSteep := expectFrom 8 8 #[(0,0),(0,1),(1,2),(1,3),(1,4),(2,5),(2,6)] Color.red
    assertImagesEq steep expectedSteep "steep (dy > dx)",
  test "zero-length line is a single point" do
    let img := line (Image.new 8 8 .rgb) ⟨3, 3⟩ ⟨3, 3⟩ Color.red
    assertEq (countColor img Color.red) 1 "one pixel"
    assertEq (img.getPixel! 3 3) Color.red "at the point",
  test "width > 1 stamps a filled square centered on each plotted point" do
    -- horizontal segment (2,4)-(5,4), width 3: half = 3/2 = 1, so each
    -- plotted point stamps a 3×3 square; consecutive stamps overlap into
    -- one solid 6×3 band (rows 3..5, cols 1..6).
    let img := line (Image.new 8 8 .rgb) ⟨2, 4⟩ ⟨5, 4⟩ Color.red (width := 3)
    let band : Rect := ⟨1, 3, 7, 6⟩
    assertEq (countColor img Color.red) 18 "band pixel count"
    for y in [0:8] do
      for x in [0:8] do
        assertEq (img.getPixel! x y == Color.red) (band.contains ⟨x, y⟩)
          s!"({x},{y}) matches band",
  test "off-canvas endpoints (±10000) never panic, only in-bounds pixels change" do
    let img := line (Image.new 5 5 .rgb) ⟨-10000, -10000⟩ ⟨10000, 10000⟩ Color.red
    -- the diagonal through the origin crosses the 5×5 canvas along y = x
    for i in [0:5] do
      assertEq (img.getPixel! (i : Int) (i : Int)) Color.red s!"({i},{i}) on the diagonal"
    assertEq (countColor img Color.red) 5 "only the 5 on-canvas diagonal pixels"
]

def rectTests : List TestCase := [
  test "filled rect pixel count and region" do
    let r : Rect := ⟨2, 1, 6, 4⟩  -- 4×3
    let img := rect (Image.new 8 8 .rgb) r (fill := some Color.red)
    assertEq (countColor img Color.red) 12 "4×3 = 12 pixels"
    assertTrue (onlyInsideChanged img r Color.black) "only inside r changed"
    for y in [1:4] do
      for x in [2:6] do
        assertEq (img.getPixel! (x : Int) (y : Int)) Color.red s!"({x},{y}) filled",
  test "1-px outline is exactly the border" do
    let r : Rect := ⟨1, 1, 7, 7⟩  -- 6×6
    let img := rect (Image.new 8 8 .rgb) r (outline := some Color.red)
    let border : Array (Nat × Nat) :=
      #[(1,1),(2,1),(3,1),(4,1),(5,1),(6,1),
        (1,2),(6,2),(1,3),(6,3),(1,4),(6,4),(1,5),(6,5),
        (1,6),(2,6),(3,6),(4,6),(5,6),(6,6)]
    let expected := expectFrom 8 8 border Color.red
    assertImagesEq img expected "1px border only",
  test "thick outline (width 2) insets from the boundary" do
    let r : Rect := ⟨1, 1, 7, 7⟩
    let img := rect (Image.new 8 8 .rgb) r (outline := some Color.red) (width := 2)
    -- band = r minus the rect inset by 2 on each side ⟨3,3,5,5⟩
    let inner : Rect := ⟨3, 3, 5, 5⟩
    for y in [0:8] do
      for x in [0:8] do
        let want := r.contains ⟨x, y⟩ && !inner.contains ⟨x, y⟩
        assertEq (img.getPixel! (x : Int) (y : Int) == Color.red) want s!"({x},{y})",
  test "fill then outline: outline drawn last overwrites the border" do
    let r : Rect := ⟨1, 1, 5, 5⟩
    let img := rect (Image.new 8 8 .rgb) r (fill := some Color.blue) (outline := some Color.red)
    assertEq (img.getPixel! 1 1) Color.red "corner is outline, not fill"
    assertEq (img.getPixel! 2 2) Color.blue "interior stays fill",
  test "off-canvas rect (±10000) clips, never panics" do
    let img := rect (Image.new 4 4 .rgb) ⟨-10000, -10000, 10000, 10000⟩ (fill := some Color.red)
    assertEq (countColor img Color.red) 16 "whole 4×4 canvas filled",
  test "empty rect (right ≤ left) draws nothing" do
    let img := rect (Image.new 4 4 .rgb) ⟨2, 2, 2, 5⟩ (fill := some Color.red)
      (outline := some Color.red)
    assertEq (countColor img Color.red) 0 "no pixels"
]

def ellipseTests : List TestCase := [
  test "fill matches hand-derived grid (small ellipse)" do
    let img := ellipse (Image.new 8 8 .rgb) ⟨0, 0, 4, 4⟩ (fill := some Color.red)
    let pts : Array (Nat × Nat) :=
      #[(1,0),(2,0),
        (0,1),(1,1),(2,1),(3,1),
        (0,2),(1,2),(2,2),(3,2),
        (1,3),(2,3)]
    assertImagesEq img (expectFrom 8 8 pts Color.red) "4×4 bounds grid",
  test "fill is symmetric under horizontal and vertical reflection" do
    let bounds : Rect := ⟨1, 1, 7, 7⟩
    let img := ellipse (Image.new 8 8 .rgb) bounds (fill := some Color.red)
    for y in [0:8] do
      for x in [0:8] do
        let mx := (bounds.left + bounds.right - 1 - (x : Int)).toNat
        let my := (bounds.top + bounds.bottom - 1 - (y : Int)).toNat
        assertEq (img.getPixel! (x : Int) (y : Int)) (img.getPixel! (mx : Int) (y : Int))
          s!"h-mirror ({x},{y}) vs ({mx},{y})"
        assertEq (img.getPixel! (x : Int) (y : Int)) (img.getPixel! (x : Int) (my : Int))
          s!"v-mirror ({x},{y}) vs ({x},{my})",
  test "fill and outline stay inside bounds" do
    let bounds : Rect := ⟨2, 2, 6, 5⟩
    let img := ellipse (Image.new 8 8 .rgb) bounds (fill := some Color.red)
      (outline := some Color.blue)
    assertTrue (onlyInsideChanged img bounds Color.black) "no pixel outside bounds touched",
  test "outline band matches hand-derived grid" do
    let bounds : Rect := ⟨1, 1, 7, 7⟩
    let img := ellipse (Image.new 8 8 .rgb) bounds (outline := some Color.red)
    let pts : Array (Nat × Nat) :=
      #[(2,1),(3,1),(4,1),(5,1),
        (1,2),(2,2),(5,2),(6,2),
        (1,3),(6,3),
        (1,4),(6,4),
        (1,5),(2,5),(5,5),(6,5),
        (2,6),(3,6),(4,6),(5,6)]
    assertImagesEq img (expectFrom 8 8 pts Color.red) "outline width 1",
  test "degenerate bounds (empty, and 1×1) never loop forever and behave sensibly" do
    let emptyImg := ellipse (Image.new 8 8 .rgb) ⟨3, 3, 3, 6⟩ (fill := some Color.red)
    assertEq (countColor emptyImg Color.red) 0 "empty bounds draw nothing"
    let onePx := ellipse (Image.new 8 8 .rgb) ⟨3, 3, 4, 4⟩ (fill := some Color.red)
    assertEq (countColor onePx Color.red) 1 "1×1 bounds draw exactly one pixel"
    assertEq (onePx.getPixel! 3 3) Color.red "at the single point"
]

def polygonTests : List TestCase := [
  test "triangle fill matches hand-derived pixel set" do
    let pts : Array Point := #[⟨1,1⟩, ⟨6,1⟩, ⟨1,6⟩]
    let img := polygon (Image.new 8 8 .rgb) pts (fill := some Color.red)
    let expectedPts : Array (Nat × Nat) :=
      #[(1,1),(2,1),(3,1),(4,1),(5,1),
        (1,2),(2,2),(3,2),(4,2),
        (1,3),(2,3),(3,3),
        (1,4),(2,4),
        (1,5)]
    assertImagesEq img (expectFrom 8 8 expectedPts Color.red) "even-odd triangle fill"
    assertEq (countColor img Color.red) 15 "15 pixels",
  test "outline draws the three edges including the closing edge" do
    let pts : Array Point := #[⟨1,1⟩, ⟨6,1⟩, ⟨1,6⟩]
    let img := polygon (Image.new 8 8 .rgb) pts (outline := some Color.red)
    -- edge (1,1)-(6,1): horizontal; edge (6,1)-(1,6): diagonal-ish; closing
    -- edge (1,6)-(1,1): vertical. Every fill pixel that lies on the
    -- triangle's boundary (left column, top row, or hypotenuse) must be set.
    for x in [1:7] do
      assertEq (img.getPixel! (x : Int) 1) Color.red s!"top edge x={x}"
    for y in [1:7] do
      assertEq (img.getPixel! 1 (y : Int)) Color.red s!"left edge y={y}",
  test "polygon fill/outline never touch outside the bounding box" do
    let pts : Array Point := #[⟨1,1⟩, ⟨6,1⟩, ⟨1,6⟩]
    let img := polygon (Image.new 8 8 .rgb) pts (fill := some Color.red)
      (outline := some Color.blue)
    let bbox : Rect := ⟨1, 1, 7, 7⟩
    assertTrue (onlyInsideChanged img bbox Color.black) "nothing drawn outside the bbox",
  test "degenerate polygons: empty draws nothing, 1 point draws a point, 2 points draw a line" do
    let empty := polygon (Image.new 8 8 .rgb) #[] (fill := some Color.red)
      (outline := some Color.blue)
    assertEq (countColor empty Color.red + countColor empty Color.blue) 0 "0 points: nothing"
    let onePt := polygon (Image.new 8 8 .rgb) #[⟨3,4⟩] (fill := some Color.red)
    assertEq (countColor onePt Color.red) 1 "1 point: a single pixel"
    assertEq (onePt.getPixel! 3 4) Color.red "at that point"
    let twoPt := polygon (Image.new 8 8 .rgb) #[⟨1,1⟩, ⟨5,1⟩] (outline := some Color.blue)
    let expectedLine := expectFrom 8 8 #[(1,1),(2,1),(3,1),(4,1),(5,1)] Color.blue
    assertImagesEq twoPt expectedLine "2 points: the line between them"
    -- outline takes priority over fill for degenerate shapes
    let both := polygon (Image.new 8 8 .rgb) #[⟨2,2⟩] (fill := some Color.red)
      (outline := some Color.blue)
    assertEq (both.getPixel! 2 2) Color.blue "outline wins when both given",
  test "off-canvas polygon (±10000) clips, never panics" do
    let pts : Array Point := #[⟨-10000,-10000⟩, ⟨10000,-10000⟩, ⟨10000,10000⟩, ⟨-10000,10000⟩]
    let img := polygon (Image.new 4 4 .rgb) pts (fill := some Color.red)
    assertEq (countColor img Color.red) 16 "whole 4×4 canvas filled"
]

def floodFillTests : List TestCase := [
  test "stays inside a drawn rectangular boundary" do
    let boundary : Rect := ⟨1, 1, 7, 7⟩
    let img := rect (Image.new 8 8 .rgb) boundary (outline := some Color.blue)
    let filled := floodFill img ⟨3, 3⟩ Color.red
    let interior : Rect := ⟨2, 2, 6, 6⟩
    for y in [0:8] do
      for x in [0:8] do
        if interior.contains ⟨x, y⟩ then
          assertEq (filled.getPixel! (x : Int) (y : Int)) Color.red s!"interior ({x},{y}) filled"
        else
          assertTrue (filled.getPixel! (x : Int) (y : Int) != Color.red)
            s!"({x},{y}) outside interior untouched"
    assertEq (countColor filled Color.blue) (countColor img Color.blue) "boundary itself untouched",
  test "no-op when seed is out of bounds" do
    let img := Image.new 4 4 .rgb Color.black
    let filled := floodFill img ⟨10, 10⟩ Color.red
    assertImagesEq filled img "unchanged",
  test "no-op when seed color already equals fill color" do
    let img := Image.new 4 4 .rgb Color.black
    let filled := floodFill img ⟨1, 1⟩ Color.black
    assertImagesEq filled img "unchanged",
  test "fills an entire solid-color image" do
    let img := Image.new 5 5 .rgb Color.black
    let filled := floodFill img ⟨2, 2⟩ Color.red
    assertEq (countColor filled Color.red) 25 "whole image"
]

def zeroSizeTests : List TestCase := [
  test "every primitive is a no-op on a 0×0 image" do
    let img := Image.new 0 0 .rgb
    assertEq (point img ⟨0, 0⟩ Color.red).data.size 0 "point"
    assertEq (line img ⟨-5, -5⟩ ⟨5, 5⟩ Color.red (width := 3)).data.size 0 "line"
    assertEq (rect img ⟨-5, -5, 5, 5⟩ (fill := some Color.red)
      (outline := some Color.blue) (width := 2)).data.size 0 "rect"
    assertEq (ellipse img ⟨-5, -5, 5, 5⟩ (fill := some Color.red)
      (outline := some Color.blue) (width := 2)).data.size 0 "ellipse"
    assertEq (polygon img #[⟨-5,-5⟩, ⟨5,-5⟩, ⟨0,5⟩] (fill := some Color.red)
      (outline := some Color.blue)).data.size 0 "polygon"
    assertEq (floodFill img ⟨0, 0⟩ Color.red).data.size 0 "floodFill"
]

/-- The `draw` suite (WP5). -/
def suite : Tests.Suite :=
  { name := "draw"
    cases := pointTests ++ lineTests ++ rectTests ++ ellipseTests ++ polygonTests ++
             floodFillTests ++ zeroSizeTests }

end Tests.DrawTests
