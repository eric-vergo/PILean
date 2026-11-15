/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean

/-!
# Unit checks

Named checks of the geometry, paths, SVG writer and tick rules.
-/

namespace PILeanTest.Units

open PILean PILean.Plot Svg

/-- Whether two floats agree within `eps`. -/
def near (x y : Float) (eps : Float := 1e-9) : Bool := (x - y).abs ≤ eps

/-- Whether two points agree within `eps`. -/
def nearPt (p q : Point) (eps : Float := 1e-9) : Bool := near p.x q.x eps && near p.y q.y eps

/-- The checks of the geometry and path code. -/
def geometry : Array (String × Bool) :=
  let m := (Affine.translate 10 20).comp (Affine.scale 2 3)
  let r := Affine.rotate (3.141592653589793 / 2)
  let circle := Path.ellipse ⟨0, 0⟩ 100 100
  let flat := circle.flatten 0.05
  let pts := flat.foldl (fun acc p => acc ++ p.points) #[]
  let arch := (Path.empty.moveTo ⟨0, 0⟩).quadTo ⟨2, 4⟩ ⟨4, 0⟩
  #[("affine: translate after scale", nearPt (m.apply ⟨1, 1⟩) ⟨12, 23⟩),
    ("affine: inverse undoes", match m.inverse? with
      | some i => nearPt (i.apply (m.apply ⟨3, -7⟩)) ⟨3, -7⟩
      | none => false),
    ("affine: singular has no inverse", (Affine.scale 0 1).inverse?.isNone),
    ("affine: rotate a quarter turn (clockwise on screen)", nearPt (r.apply ⟨1, 0⟩) ⟨0, 1⟩),
    ("affine: maxScale of a scale", near (Affine.scale 2 (-5)).maxScale 5 1e-12),
    ("path: flattened circle is one closed polyline", flat.size == 1 && flat.all (·.closed)),
    ("path: flattened circle within tolerance of the cubic circle (and of the true circle)",
      pts.all fun p => near p.norm 100 0.05),
    ("path: flatten is bounded for a huge curve",
      (((Path.empty.moveTo ⟨0, 0⟩).cubicTo ⟨1e300, 0⟩ ⟨0, 1e300⟩ ⟨1, 1⟩).flatten 0.1).all
        (·.points.size ≤ Path.maxPieces + 1)),
    ("path: tight bounds take the curve's extremum", arch.bounds == some ⟨0, 0, 4, 2⟩),
    ("path: control bounds take the control point", arch.controlBounds == some ⟨0, 0, 4, 4⟩),
    ("path: rect", (Path.rect 1 2 3 4).bounds == some ⟨1, 2, 4, 6⟩),
    ("path: transform", ((Path.rect 0 0 1 1).transform m).bounds == some ⟨10, 20, 12, 23⟩)]

/-- The checks of the SVG writer. -/
def svg : Array (String × Bool) :=
  #[("fmtNum: integers", fmtNum 42 == "42" && fmtNum (-3) == "-3"),
    ("fmtNum: rounding and trailing zeros", fmtNum 1.23456 == "1.235" && fmtNum 0.5 == "0.5"),
    ("fmtNum: no -0", fmtNum (-0.0001) == "0"),
    ("fmtNum: decimals", fmtNum 3.14159 2 == "3.14"),
    ("fmtNum: non-finite and huge", fmtNum (0 / 0) == "0" && fmtNum (1 / 0) == "0" &&
      fmtNum 1e20 == "1000000000000"),
    ("escape: text", escapeText "a<b>&c" == "a&lt;b&gt;&amp;c"),
    ("escape: attribute", escapeAttr "\"x'\n" == "&quot;x&#39;&#10;"),
    ("escape: characters XML cannot carry are dropped",
      escapeText (String.ofList ['a', Char.ofNat 1, 'b', Char.ofNat 0xFFFE]) == "ab"),
    ("render: injected markup stays text",
      render 0 (text 0 0 "</text><script>x</script>" 10 ⟨0, 0, 0, 255⟩ .start) ==
        "<text x=\"0\" y=\"0\" font-size=\"10\" fill=\"#000000\" text-anchor=\"start\">" ++
        "&lt;/text&gt;&lt;script&gt;x&lt;/script&gt;</text>"),
    ("render: invalid attribute names are left out",
      render 0 (el "g" #[("on load", "x"), ("id", "a")]) == "<g id=\"a\"/>"),
    ("render: an element with an invalid name is left out", render 0 (el "1x" #[]) == ""),
    ("paint: translucent colours get an opacity",
      paint "fill" (some ⟨255, 0, 0, 128⟩) == #[("fill", "#ff0000"), ("fill-opacity", "0.502")]),
    ("pathData", pathData (Path.rect 0 0 1.006 2) == "M0 0 L1.01 0 L1.01 2 L0 2 Z")]

/-- The checks of the tick rules. -/
def ticks : Array (String × Bool) :=
  let t1 := niceTicks 0 1
  let t2 := niceTicks 3 97
  let t3 := niceTicks (-6.283) 6.283 6 (snap := false)
  let t4 := niceTicks 5 5
  #[("ticks: [0, 1]", t1.step == 0.2 && t1.values.size == 6 && t1.lo == 0 && t1.hi == 1),
    ("ticks: [3, 97] widens to [0, 100]", t2.step == 20 && t2.lo == 0 && t2.hi == 100),
    ("ticks: [-2π, 2π] unsnapped", t3.step == 2 && t3.values == #[-6, -4, -2, 0, 2, 4, 6] &&
      t3.lo == -6.283),
    ("ticks: a degenerate interval is widened", t4.lo < 5 && t4.hi > 5),
    ("ticks: non-finite bounds", (niceTicks (0 / 0) 1).lo == 0),
    ("ticks: values are exact multiples", (niceTicks 0 0.3 3).values.all fun v =>
      near (v / 0.1) (v / 0.1).round 1e-9),
    ("labels: decimals from the step", tickLabel t1 0.4 == "0.4" && tickLabel t2 40 == "40"),
    ("labels: typographic minus, no −0", fmtFixed (-1.5) 1 == "−1.5" && fmtFixed (-0.01) 1 == "0.0")]

/-- All unit checks. -/
def checks : Array (String × Bool) := geometry ++ svg ++ ticks

end PILeanTest.Units
