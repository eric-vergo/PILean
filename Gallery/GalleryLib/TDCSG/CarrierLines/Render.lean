import PILean
import GalleryLib.TDCSG.CarrierLines.Exact

/-!
# Proof-driven TDCSG carrier-line plates

The exact construction lives in `Exact.lean`.  This file performs one
deterministic integer/fixed-point rounding step for raster output and draws
only from the `PhasePair` records defined there.
-/

namespace Gallery.TDCSG.CarrierLines

open PILean
open PILean.Draw

def canvasW : Nat := 3840
def canvasH : Nat := 2160

def bg : Color := Color.rgb 9 15 29
def panelBg : Color := Color.rgb 15 25 43
def grid : Color := Color.rgb 44 61 82
def diskLeft : Color := Color.rgb 73 197 182
def diskRight : Color := Color.rgb 244 138 120
def polygonColor : Color := Color.rgb 158 177 197
def lineA : Color := Color.rgb 66 211 255
def lineB : Color := Color.rgb 255 105 180
def carrierColor : Color := Color.rgb 255 210 76
def edgeColor : Color := Color.rgb 255 244 190
def white : Color := Color.rgb 238 244 252
def muted : Color := Color.rgb 155 170 190
def warning : Color := Color.rgb 255 177 66

def roundedRatio (a b c : Nat) : Nat :=
  if c == 0 then 0 else (a * b + c / 2) / c

def circle (img : Image) (center : Point) (radius : Nat) (color : Color)
    (width : Nat := 1) : Image :=
  arc img center radius 0 360 color width

def dot (img : Image) (p : Point) (radius : Nat) (color : Color) : Image :=
  ellipse img
    ⟨p.x - (radius : Int), p.y - (radius : Int),
      p.x + (radius : Int) + 1, p.y + (radius : Int) + 1⟩
    (fill := some color)

def centeredText (img : Image) (y : Int) (s : String) (color : Color)
    (scale : Nat) : Image :=
  let (tw, _) := textSizeScaled s scale
  let x : Int := ((img.width - min img.width tw) / 2 : Nat)
  textScaled img ⟨x, y⟩ s color scale

def textAt (img : Image) (x y : Int) (s : String) (color : Color)
    (scale : Nat := 2) : Image :=
  textScaled img ⟨x, y⟩ s color scale

def reflectAbout (o p : Point) : Point :=
  ⟨2 * o.x - p.x, 2 * o.y - p.y⟩

def polygonPoints (center : Point) (radius order : Nat) : Array Point := Id.run do
  let mut pts : Array Point := #[]
  let step : Int := (360 / order : Nat)
  for k in [0:order] do
    -- PILean screen angles are clockwise; negate to render the mathematical
    -- counterclockwise root used by the exact construction.
    pts := pts.push (circlePoint center radius (-((k : Int) * step)))
  return pts

def scalePixels (unit : Nat) (p : PhasePair) : Nat :=
  let cm := (cosFP p.midpointDeg).natAbs
  let ch := (cosFP p.halfStepDeg).natAbs
  roundedRatio unit cm ch

def diskRadius10 (unit : Nat) : Nat := roundedRatio unit 1543361918 1000000000

def diskRadius20 (unit : Nat) : Nat := roundedRatio unit 1100580623 1000000000

/-- Radial length of the `j=9,10` unit-20-gon edge from the origin:
`2 sin(π/20)` times the polygon radius, evaluated with PILean's deterministic
16.16 trigonometric table. -/
def focusEdgeHalfPixels (unit : Nat) : Nat :=
  roundedRatio (2 * unit) (sinFP 9).natAbs 65536

def lineAngleScreen (order edge : Nat) : Int :=
  -((((2 * edge + 1) * 180 / order : Nat) : Int) - 90)

def lineEndpoints (o : Point) (radius : Nat) (screenAngle : Int) : Point × Point :=
  (circlePoint o radius (screenAngle + 180), circlePoint o radius screenAngle)

/-- Half-length of the intersection of a line through the origin with the
two equal closed disks, computed in the deterministic pixel model from the
same disk radius and line angle used by the scene. -/
def lensHalfPixels (diskRadius unit : Nat) (screenAngle : Int) : Nat :=
  let proj := (fpRound ((unit : Int) * cosFP screenAngle)).natAbs
  let perp := (fpRound ((unit : Int) * sinFP screenAngle)).natAbs
  let radicand := diskRadius * diskRadius - perp * perp
  Nat.sqrt radicand - proj

def drawAxes (img : Image) (o : Point) (halfW halfH : Nat) : Image :=
  let img := dashedLine img ⟨o.x - (halfW : Int), o.y⟩
      ⟨o.x + (halfW : Int), o.y⟩ grid 18 16 2
  dashedLine img ⟨o.x, o.y - (halfH : Int)⟩
    ⟨o.x, o.y + (halfH : Int)⟩ grid 18 16 2

def drawDiskPair (img : Image) (o : Point) (unit diskRadius : Nat) : Image :=
  let cL : Point := ⟨o.x - (unit : Int), o.y⟩
  let cR : Point := ⟨o.x + (unit : Int), o.y⟩
  let img := circle img cL diskRadius (Color.rgb 18 47 58) 18
  let img := circle img cL diskRadius diskLeft 7
  let img := circle img cR diskRadius (Color.rgb 64 32 42) 18
  let img := circle img cR diskRadius diskRight 7
  let img := dot img cL 10 diskLeft
  let img := dot img cR 10 diskRight
  let img := dot img o 8 white
  img

def edgeAt (pts : Array Point) (j : Nat) : Point × Point :=
  (pts[j % pts.size]!, pts[(j + 1) % pts.size]!)

def drawPolygonPair (img : Image) (o : Point) (unit radius order : Nat) :
    Image × Array Point :=
  let cR : Point := ⟨o.x + (unit : Int), o.y⟩
  let right := polygonPoints cR radius order
  let left := right.map (reflectAbout o)
  let img := polyline img right polygonColor 5 true
  let img := polyline img left polygonColor 5 true
  (img, right)

def drawCommonEdge (img : Image) (o : Point) (right : Array Point)
    (order edge supportLength carrierHalf : Nat) (color : Color) : Image :=
  let angle := lineAngleScreen order edge
  let (supportA, supportB) := lineEndpoints o supportLength angle
  let (carrierA, carrierB) := lineEndpoints o carrierHalf angle
  let (p, q) := edgeAt right edge
  let lp := reflectAbout o p
  let lq := reflectAbout o q
  let img := dashedLine img supportA supportB color 24 18 4
  let img := line img p q edgeColor 16
  let img := line img lp lq edgeColor 16
  let img := line img carrierA carrierB carrierColor 12
  let img := dot img p 8 edgeColor
  let img := dot img q 8 edgeColor
  let img := dot img lp 8 edgeColor
  let img := dot img lq 8 edgeColor
  let img := dot img carrierA 13 carrierColor
  let img := dot img carrierB 13 carrierColor
  img

def drawPhasePair (img : Image) (o : Point) (unit supportLength : Nat)
    (p : PhasePair) (carrierHalf : Nat) : Image :=
  let radius := scalePixels unit p
  let (img, right) := drawPolygonPair img o unit radius p.order
  let img := drawCommonEdge img o right p.order p.edgeIndex supportLength carrierHalf lineA
  drawCommonEdge img o right p.order p.partner supportLength carrierHalf lineB

def drawLegendSwatch (img : Image) (x y : Int) (color : Color) (dashed : Bool)
    (label : String) : Image :=
  let a : Point := ⟨x, y + 10⟩
  let b : Point := ⟨x + 130, y + 10⟩
  let img := if dashed then dashedLine img a b color 18 12 5 else line img a b color 9
  textAt img (x + 155) y label white 2

def n10Plate : Image := Id.run do
  let mut img := Image.new canvasW canvasH .rgb bg
  let o : Point := ⟨1920, 1115⟩
  let unit : Nat := 650
  let diskR := diskRadius10 unit
  let polyR := scalePixels unit n10Pair
  img := drawAxes img o 1850 1040
  img := drawDiskPair img o unit diskR
  let (img0, right) := drawPolygonPair img o unit polyR 10
  img := img0
  img := drawCommonEdge img o right 10 3 1810 polyR lineA
  img := drawCommonEdge img o right 10 6 1810 polyR lineB
  -- Header and footer panels are drawn last so labels never compete with arcs.
  img := rect img ⟨0, 0, 3840, 238⟩ (fill := some (Color.rgb 10 18 33))
  img := centeredText img 42 "n = 10  |  exact common-edge carriers" white 5
  img := centeredText img 140
    "Figure 5(b) geometry: phases j = 3, 6;  s = 1/phi;  R^2 = 4 - phi" muted 3
  img := rect img ⟨0, 1940, 3840, 2160⟩ (fill := some (Color.rgb 10 18 33))
  img := drawLegendSwatch img 250 1985 lineA true "supporting line  +pi/5"
  img := drawLegendSwatch img 1420 1985 lineB true "supporting line  -pi/5"
  img := drawLegendSwatch img 2590 1985 carrierColor false "closed lens carrier"
  img := textAt img 250 2070
    "Solid gold endpoints are exact cross-disk contacts; polygon edges are pale gold." muted 2
  return img

def panelOrigin (slot : Nat) : Point :=
  if slot < 3 then ⟨650 + (slot : Int) * 1270, 735⟩
  else ⟨1285 + ((slot - 3 : Nat) : Int) * 1270, 1570⟩

def drawN20Panel (img : Image) (slot : Nat) (p : PhasePair) : Image := Id.run do
  let o := panelOrigin slot
  let unit : Nat := 190
  let diskR := diskRadius20 unit
  let carrierHalf := lensHalfPixels diskR unit (lineAngleScreen p.order p.edgeIndex)
  let box : Rect :=
    if slot < 3 then
      ⟨o.x - 590, o.y - 380, o.x + 590, o.y + 375⟩
    else
      ⟨o.x - 590, o.y - 355, o.x + 590, o.y + 375⟩
  let mut img := rect img box (fill := some panelBg) (outline := some grid) (width := 3)
  img := drawAxes img o 550 330
  img := drawDiskPair img o unit diskR
  -- A panel-local supporting segment: long enough to expose the line, short
  -- enough not to leak across neighboring panels (PILean clips to the canvas,
  -- not to arbitrary nested viewports).
  img := drawPhasePair img o unit 320 p carrierHalf
  let beta := p.lineAngleDeg
  img := textAt img (box.left + 28) (box.top + 25)
    s!"j = {p.edgeIndex}, {p.partner}    beta = +/-{beta} deg" white 2
  img := textAt img (box.left + 28) (box.top + 75)
    s!"polygon scale s = {p.scaleLabel}" muted 2
  let relation := if p.edgeIndex == 9 then
      "edges meet at 0; carrier extends slightly beyond"
    else
      "carrier occupies the central gap between edges"
  img := textAt img (box.left + 28) (box.bottom - 50) relation warning 1
  return img

def n20AtlasPlate : Image := Id.run do
  let mut img := Image.new canvasW canvasH .rgb bg
  img := centeredText img 36 "n = 20  |  five-scale common-edge atlas" white 5
  img := centeredText img 132
    "Ten phase lines form five reflected pairs; one fixed-size 20-gon cannot show all ten." muted 3
  for h : slot in [0:n20Pairs.size] do
    img := drawN20Panel img slot n20Pairs[slot]
  img := rect img ⟨0, 2035, 3840, 2160⟩ (fill := some (Color.rgb 10 18 33))
  img := centeredText img 2070
    "Disks use the retrospective contact radius r* = 1.1005806228...; this atlas claims no critical radius or IET." warning 2
  return img

def drawFocusInset (img : Image) (center : Point) (halfEdge halfCarrier : Nat) : Image := Id.run do
  let box : Rect := ⟨center.x - 500, center.y - 390, center.x + 500, center.y + 390⟩
  let mut img := rect img box (fill := some (Color.rgb 12 22 38))
    (outline := some grid) (width := 4)
  img := textAt img (box.left + 34) (box.top + 28)
    "origin detail (same exact phase data, enlarged)" white 2
  let zoom : Nat := 2
  for edge in #[9, 10] do
    let angle := lineAngleScreen 20 edge
    let (sa, sb) := lineEndpoints center (430 : Nat) angle
    let (ea, eb) := lineEndpoints center (halfEdge * zoom) angle
    let (ca, cb) := lineEndpoints center (halfCarrier * zoom) angle
    let c := if edge == 9 then lineA else lineB
    img := dashedLine img sa sb c 18 14 4
    img := line img ea eb edgeColor 15
    img := line img ca cb carrierColor 8
    img := dot img ea 10 edgeColor
    img := dot img eb 10 edgeColor
    img := dot img ca 13 carrierColor
    img := dot img cb 13 carrierColor
  img := dot img center 9 white
  img := textAt img (box.left + 34) (box.bottom - 72)
    "pale gold = polygon-edge span; gold = closed lens carrier" muted 2
  return img

def n20FocusPlate : Image := Id.run do
  let mut img := Image.new canvasW canvasH .rgb bg
  let o : Point := ⟨1390, 1110⟩
  let unit : Nat := 520
  let p := n20Pairs[4]!
  let diskR := diskRadius20 unit
  let edgeHalf := focusEdgeHalfPixels unit
  let carrierHalf := lensHalfPixels diskR unit (lineAngleScreen 20 9)
  img := drawAxes img o 1320 930
  img := drawDiskPair img o unit diskR
  img := drawPhasePair img o unit 1280 p carrierHalf
  img := rect img ⟨0, 0, 3840, 238⟩ (fill := some (Color.rgb 10 18 33))
  img := centeredText img 42 "n = 20  |  focused common-edge search carriers" white 5
  img := centeredText img 140
    "phases j = 9, 10; polygon scale s = 1; supporting lines beta = +/-81 deg" muted 3
  img := drawFocusInset img ⟨3200, 1050⟩ edgeHalf carrierHalf
  img := textAt img 2725 1510 "bounded diagnostic:" white 2
  img := textAt img 2725 1570 "j=9   Ab, Ba" lineA 3
  img := textAt img 2725 1640 "j=10  aB, bA" lineB 3
  img := textAt img 2725 1725 "carrier-meeting candidates only" warning 2
  img := textAt img 2725 1780 "not a first-return map / IET" warning 2
  img := textAt img 2725 1870 "Separate 54-deg origin-ray experiment" muted 1
  img := textAt img 2725 1900 "is intentionally not shown here." muted 1
  img := rect img ⟨0, 2025, 3840, 2160⟩ (fill := some (Color.rgb 10 18 33))
  img := centeredText img 2060
    "Disk radius is the retrospective finite-contact candidate r*, not a proved critical radius." warning 2
  return img

end Gallery.TDCSG.CarrierLines
