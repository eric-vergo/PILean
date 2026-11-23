/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanTest.Examples

/-!
# Checks of plane figures, arcs, shape metadata, the plane palette and exact points

* Arcs (`Path.arc`): the pieces, their ends, and the radial error against the stated bound.
* The frame (`Plane.Frame`): the map and its inverse, fitting (everything inside the padding, the
  page used across its width), clipping of lines and rays.
* Labels: the box of a label stands `offset` pixels from its point in every placement.
* Metadata (`Canvas.ShapeInfo`): the SVG elements and attributes, escaping and reduction of
  hostile values, inert output, and the same pixels with and without metadata.
* The plane palette: the WCAG contrast requirements of `PILean.Style`, light and dark.
* Plane figures: deterministic, inert, light and dark twins of one structure.
* Exact points: the integer square root and `sqrtBall` (certified by squaring), the worked
  instances (`PILeanTest.PlaneExact`: Gaussian rationals, ℚ(√5), ℤ[ζ₅]) certified exactly and
  within their radii, and the exact gallery figure's markers at the frame's images of its
  points.
-/

namespace PILeanTest.PlaneChecks

open PILean PILean.Plane PILean.Exact PILeanTest.PlaneExact

/-- Whether `s` contains `t`. -/
def has (s t : String) : Bool := (s.splitOn t).length > 1

/-- Whether two floats differ by at most `tol`. -/
def near (a b : Float) (tol : Float := 1e-9) : Bool := (a - b).abs ≤ tol

/-- Whether two points differ by at most `tol` in each coordinate. -/
def nearPt (p q : Point) (tol : Float := 1e-9) : Bool := near p.x q.x tol && near p.y q.y tol

/-- The largest distance from the circle `(c, r)` of the points of the path's cubics, sampled
256 times each. -/
def radialError (c : Point) (r : Float) (p : Path) : Float := Id.run do
  let mut cur : Point := ⟨0, 0⟩
  let mut worst := 0
  for cmd in p.cmds do
    match cmd with
    | .move q => cur := q
    | .cubic a b q =>
      for i in [0:257] do
        let t := i.toFloat / 256
        worst := max worst (((Path.bezierAt [cur, a, b, q] t) - c).norm - r).abs
      cur := q
    | _ => pure ()
  return worst

/-- The checks of arcs. -/
def arcs : Array (String × Bool) :=
  let c : Point := ⟨10, -4⟩
  let sweeps : List (Float × Float) :=
    [(0, 1.5707963267948966), (0.3, 2.9), (-1, -5.5), (2, 2.1), (0, 6.283185307179586),
      (1, 1 - 4.2), (0, 0.001)]
  #[("arc: pieces of at most a quarter turn",
      Path.arcPieceCount 1.5707963267948966 == 1 && Path.arcPieceCount 1.6 == 2 &&
      Path.arcPieceCount (-3.2) == 3 && Path.arcPieceCount 6.3 == 4 &&
      Path.arcPieceCount 100 == 4 && Path.arcPieceCount 0 == 1),
    ("arc: no pieces for a sweep or radius that is not finite",
      Path.arcPieceCount ((0 : Float) / 0) == 0 && (Path.arc c 2 0 ((1 : Float) / 0)).cmds.isEmpty &&
      (Path.arc c ((0 : Float) / 0) 0 1).cmds.isEmpty),
    ("arc: the quarter-turn error bound is 2.73e-4 of the radius",
      near (Path.arcError 1 1.5707963267948966) 2.7253e-4 1e-7),
    ("arc: starts and ends on the circle at the given angles",
      sweeps.all fun (a, b) =>
        let p := Path.arc c 2 a b
        let tau := 6.283185307179586
        let b' := a + max (-tau) (min tau (b - a))
        match (p.cmds[0]? : Option PathCmd), (p.cmds.back? : Option PathCmd) with
        | some (.move s), some (.cubic _ _ e) =>
          nearPt s ⟨c.x + 2 * a.cos, c.y + 2 * a.sin⟩ && nearPt e ⟨c.x + 2 * b'.cos, c.y + 2 * b'.sin⟩
        | _, _ => false),
    ("arc: within the stated error of the circle, and near it (not far below the bound)",
      sweeps.all fun (a, b) =>
        let p := Path.arc c 3 a b
        let n := Path.arcPieceCount (b - a)
        let tau := 6.283185307179586
        let δ := (max (-tau) (min tau (b - a))) / n.toFloat
        let bound := Path.arcError 3 δ
        let e := radialError c 3 p
        e ≤ bound * 1.0001 + 1e-12 && (bound < 1e-9 || e ≥ bound * 0.5)),
    ("arc: arcTo continues a path with a line to the arc's start",
      match (((Path.empty.moveTo c).arcTo c 1 0 1).close).cmds.toList with
      | [.move _, .line q, .cubic .., .close] => nearPt q ⟨c.x + 1, c.y⟩
      | _ => false),
    ("arc: a full turn closes on itself",
      match (Path.arc c 1 0.5 (0.5 + 6.283185307179586)).cmds.toList with
      | .move s :: rest =>
        rest.length == 4 && (match rest.getLast? with
          | some (.cubic _ _ e) => nearPt s e 1e-12
          | _ => false)
      | _ => false)]

/-- The checks of the frame. -/
def frames : Array (String × Bool) :=
  let f : Frame := { scale := 40, ox := 100, oy := 80, width := 200, height := 160 }
  let pts : List Point := [⟨0, 0⟩, ⟨1.5, -2⟩, ⟨-3, 0.25⟩]
  let reaches : Array Reach := #[Reach.around ⟨-2, -1⟩ 4, Reach.around ⟨3, 2⟩ 4,
    ⟨⟨3, 0⟩, ⟨-2, -10, 60, 10⟩⟩]
  let fit := Frame.fit reaches 480 none 12
  let inside := fun (fr : Frame) (pad : Float) => reaches.all fun r =>
    let q := fr.toScreen r.at_
    q.x + r.off.x0 ≥ pad - 1e-6 && q.x + r.off.x1 ≤ fr.width - pad + 1e-6 &&
      q.y + r.off.y0 ≥ pad - 1e-6 && q.y + r.off.y1 ≤ fr.height - pad + 1e-6
  let fitH := Frame.fit reaches 480 (some 200) 12
  #[("frame: y up, one scale", nearPt (f.toScreen ⟨1, 1⟩) ⟨140, 40⟩),
    ("frame: toWorld inverts toScreen", pts.all fun p => nearPt (f.toWorld (f.toScreen p)) p),
    ("frame: the view is the world box of the page",
      let v := f.view
      near v.x0 (-2.5) && near v.x1 2.5 && near v.y0 (-2) && near v.y1 2),
    ("fit: every reach inside the padding", inside fit 12),
    ("fit: the page used across its width (a reach touches each side)",
      let xs := reaches.map fun r => ((fit.toScreen r.at_).x + r.off.x0,
        (fit.toScreen r.at_).x + r.off.x1)
      near (xs.foldl (fun m p => min m p.1) 1e9) 12 1e-6 &&
        near (xs.foldl (fun m p => max m p.2) (-1e9)) 468 1e-6),
    ("fit: the height is whole and fits", fit.height == fit.height.round && fit.height > 24),
    ("fit: with a height, inside the padding both ways", inside fitH 12 && fitH.height == 200),
    ("fit: no reaches gives a frame of positive scale",
      (Frame.fit #[] 100 none 10).scale > 0),
    ("fit: non-finite reaches are left out",
      let g := Frame.fit (reaches.push (Reach.around ⟨(0 : Float) / 0, 1⟩ 2)) 480 none 12
      g.scale == fit.scale),
    ("clip: a line across the box ends on its sides",
      clipLine ⟨-5, 5⟩ ⟨0, 5⟩ ⟨0, 0, 10, 10⟩ |>.any fun (a, b) =>
        nearPt a ⟨0, 5⟩ && nearPt b ⟨10, 5⟩),
    ("clip: a ray starts at its point",
      clipLine ⟨2, 2⟩ ⟨3, 3⟩ ⟨0, 0, 10, 10⟩ (ray := true) |>.any fun (a, b) =>
        nearPt a ⟨2, 2⟩ && nearPt b ⟨10, 10⟩),
    ("clip: a line that misses the box, a ray pointing away and a point give nothing",
      (clipLine ⟨-5, 20⟩ ⟨5, 20⟩ ⟨0, 0, 10, 10⟩).isNone &&
      (clipLine ⟨2, 2⟩ ⟨1, 1⟩ ⟨5, 5, 10, 10⟩ (ray := true)).isNone &&
      (clipLine ⟨2, 2⟩ ⟨2, 2⟩ ⟨0, 0, 10, 10⟩).isNone)]

/-- The checks of labels: the box stands `offset` pixels from the point in every placement (its
nearest point along the placement's direction), and a centred label is centred on it. -/
def labels : Array (String × Bool) :=
  let st := Style.light
  let places : List Placement := [.above, .below, .left, .right, .aboveLeft, .aboveRight,
    .belowLeft, .belowRight, .toward 1, .toward (-2.5)]
  #[("label: the box is offset pixels from its point in every placement",
      places.all fun pl =>
        let (b, _) := labelBox st "x²+1" 15 6 pl
        let d := pl.screenDir
        let corners : List Point := [⟨b.x0, b.y0⟩, ⟨b.x1, b.y0⟩, ⟨b.x0, b.y1⟩, ⟨b.x1, b.y1⟩]
        near (corners.foldl (fun m q => min m (q.x * d.x + q.y * d.y)) 1e9) 6 1e-9),
    ("label: centred on the point when centred",
      let (b, base) := labelBox st "abc" 15 6 .center
      near (b.x0 + b.x1) 0 && near (b.y0 + b.y1) 0 && near base.x 0),
    ("label: the label's box is part of the figure's reaches",
      let items := #[point ⟨0, 0⟩, point ⟨1, 0⟩, label "a long label on the right" ⟨1, 0⟩ .right]
      let fig : Plane.Figure := { items }
      let fr := fig.frame
      let (b, _) := labelBox st "a long label on the right" st.plane.labelSize
        st.plane.labelOffset .right
      (fr.toScreen ⟨1, 0⟩).x + b.x1 ≤ fr.width - fig.padding + 1e-6)]

/-- The SVG of a drawing with the built-in lettering as text. -/
def svgOf (s : Canvas.Shape) : String := Canvas.Shape.toSvg s 100 100 "sans-serif"

/-- The checks of shape metadata. -/
def metadata : Array (String × Bool) :=
  let disc := Canvas.Shape.path (Canvas.circle ⟨50, 50⟩ 30) (some (.solid ⟨200, 30, 30, 255⟩))
  let info : Canvas.ShapeInfo :=
    { title := "a disc", description := "radius 30", cssClass := "disc main", id := "d1",
      leanDecl := "Foo.bar" }
  let tagged := Canvas.Shape.tagged info disc
  let svg := svgOf tagged
  let hostile : Canvas.ShapeInfo :=
    { title := "</title><script>alert(1)</script>", description := "a & b < c",
      cssClass := "x\" onload=\"evil() javascript:", id := "a b<c>", leanDecl := "N\"><script>" }
  let hsvg := svgOf (.tagged hostile disc)
  let px := fun (s : Canvas.Shape) =>
    (Canvas.Shape.toImage s 100 100 TextEngine.lettering ⟨255, 255, 255, 255⟩).data.data
  #[("metadata: title, desc, id, class and data-lean-decl in SVG",
      has svg "<title>a disc</title>" && has svg "<desc>radius 30</desc>" &&
      has svg "id=\"d1\"" && has svg "class=\"disc main\"" && has svg "data-lean-decl=\"Foo.bar\""),
    ("metadata: the SVG is inert", Svg.isInert svg),
    ("metadata: no wrapper without metadata", svgOf (.tagged {} disc) == svgOf disc),
    ("metadata: hostile values escaped or reduced, and the SVG inert",
      Svg.isInert hsvg && !has hsvg "<script" && has hsvg "&lt;/title&gt;" &&
      has hsvg "id=\"a_b_c_\"" && !has hsvg " onload=" && !has hsvg "javascript:" &&
      has hsvg "class=\"x_ onload__evil__ javascript_\"" && has hsvg "a &amp; b &lt; c"),
    ("metadata: the image is the same with and without it", px tagged == px disc),
    ("metadata: merge keeps fields and joins classes",
      let a : Canvas.ShapeInfo := { title := "t", cssClass := "a" }
      let m := a.merge { cssClass := "b", id := "i" }
      m.title == "t" && m.cssClass == "a b" && m.id == "i"),
    ("metadata: item modifiers fill the fields",
      match (point ⟨0, 0⟩ |>.named "P" |>.describedBy "a point" |>.withClass "pt" |>.withId "p"
          |>.declRef `PILean.Plane.point) with
      | .shape _ _ i => i.title == "P" && i.description == "a point" && i.cssClass == "pt" &&
          i.id == "p" && i.leanDecl == "PILean.Plane.point"
      | _ => false),
    ("metadata: a plane item's metadata reaches the figure's SVG",
      let items := #[point ⟨0, 0⟩ |>.named "the origin" |>.declRef `PILean.Plane.point,
        point ⟨1, 1⟩]
      let fig : Plane.Figure := { items }
      has fig.toSvg "<title>the origin</title>" &&
        has fig.toSvg "data-lean-decl=\"PILean.Plane.point\"")]

/-- The contrast of `c` against `bg` with `tint` laid over it at opacity `a`, mixed in linear light
(`Rgba.over`, as PILean draws) and in sRGB (as a browser does): the smaller of the two. -/
def contrastOnTint (c tint bg : Rgba) (a : Float) : Float :=
  let alpha := (a * 255).round.toUInt8
  let lin := Rgba.over { tint with a := alpha } bg
  let mix := fun (x y : UInt8) => (a * x.toFloat + (1 - a) * y.toFloat).round.toUInt8
  let srgb : Rgba := ⟨mix tint.r bg.r, mix tint.g bg.g, mix tint.b bg.b, 255⟩
  min (contrast c lin) (contrast c srgb)

/-- Whether a plane palette meets the requirements of `PILean.Style` on a background: the ink at
least 7:1, every accent and the faint colour at least 4.5:1 on the background; on a fill tinted
with any accent, the ink at least 7:1, the accents at least 4.5:1, the faint colour at least
3:1. -/
def meetsContrast (p : PlaneStyle) (bg : Rgba) : Bool :=
  contrast p.ink bg ≥ 7 && p.accents.all (contrast · bg ≥ 4.5) && contrast p.faint bg ≥ 4.5 &&
    p.accents.all fun t =>
      contrastOnTint p.ink t bg p.fillOpacity ≥ 7 &&
      p.accents.all (contrastOnTint · t bg p.fillOpacity ≥ 4.5) &&
      contrastOnTint p.faint t bg p.fillOpacity ≥ 3

/-- The checks of the plane palette. -/
def palette : Array (String × Bool) :=
  #[("palette: light meets the contrast requirements on the light background",
      meetsContrast PlaneStyle.light Style.light.background),
    ("palette: dark meets the contrast requirements on the dark background",
      meetsContrast PlaneStyle.dark Style.dark.background),
    ("palette: three accents, Style.dark carries the dark plane colours",
      PlaneStyle.light.accents.size == 3 && PlaneStyle.dark.accents.size == 3 &&
      Style.dark.plane == PlaneStyle.dark && Style.light.plane == PlaneStyle.light),
    ("palette: the check fails for an ink too light",
      !meetsContrast { PlaneStyle.light with ink := ⟨180, 180, 180, 255⟩ } Style.light.background),
    ("palette: accents wrap round", PlaneStyle.light.accent 4 == PlaneStyle.light.accent 1),
    ("palette: tones resolve to the style's roles",
      Tone.ink.resolve PlaneStyle.dark == PlaneStyle.dark.ink &&
      (Tone.accent 2).resolve PlaneStyle.light == PlaneStyle.light.accent 2 &&
      Tone.faint.resolve PlaneStyle.light == PlaneStyle.light.faint)]

/-- The checks of plane figures. -/
def figures : Array (String × Bool) :=
  let disks := Examples.PlaneFigures.disks
  let dark := { disks with style := Style.dark }
  #[("figure: deterministic SVG and PNG",
      disks.toSvg == disks.toSvg && disks.toPng.map (·.data) == disks.toPng.map (·.data)),
    ("figure: every gallery plane figure is inert and has pixels",
      Examples.planes.all fun (_, f) => Svg.isInert f.toSvg && f.toPng.isSome),
    ("figure: the dark twin has the same frame and the dark colours",
      dark.frame == disks.frame && has dark.toSvg (Svg.rgbHex PlaneStyle.dark.ink) &&
      !has dark.toSvg (Svg.rgbHex (PlaneStyle.light.accent 0))),
    ("figure: the page width is the given width",
      disks.frame.width == 520 && disks.pixelSize.1 == 520),
    ("figure: a given view is fitted",
      let f : Plane.Figure := { items := #[], view := some ⟨0, 0, 4, 2⟩, width := 420, padding := 10 }
      near f.frame.scale 100 1e-6 && f.frame.height == 220),
    ("figure: stroke widths stay in pixels at every scale",
      let items := #[segment ⟨0, 0⟩ ⟨1, 0⟩, point ⟨0, 1⟩]
      let at_ := fun (w : Float) => ({ items, width := w } : Plane.Figure).toSvg
      has (at_ 200) "stroke-width=\"2\"" && has (at_ 900) "stroke-width=\"2\""),
    ("figure: a line reaches the edges of the page",
      let items := #[line ⟨0, 0⟩ ⟨1, 0⟩, point ⟨0, 1⟩, point ⟨2, -1⟩]
      let f : Plane.Figure := { items }
      match drawGeom f.env {} (.line ⟨0, 0⟩ ⟨1, 0⟩) with
      | #[.path p _ _ _] => match p.cmds.toList with
        | [.move a, .line b] => near a.x 0 && near b.x f.frame.width
        | _ => false
      | _ => false),
    ("figure: ToOutputs gives an SVG and a PNG",
      (PILean.Trust.ToOutputs.outputs disks).map (·.format.name) == #["svg", "png"])]

/-- The checks of exact points. -/
def exact : Array (String × Bool) :=
  let isqrtOk := fun (n : Nat) => let s := isqrt n; s * s ≤ n && n < (s + 1) * (s + 1)
  let qs : List Rat := [2, 3, 5, 1 / 3, 10, 7 / 11, 12345 / 7, 1 / 1000000, 2 ^ 70 + 1]
  let ks : List Nat := [0, 1, 8, 30, 64]
  let gold := QSqrt5.phi
  let zeta := (List.range 5).map Zeta5.pow
  let fig := zetaSteps
  #[("isqrt: floor square roots, small and large",
      (List.range 3000).all isqrtOk && [10 ^ 30, 10 ^ 30 - 1, 2 ^ 127, 2 ^ 128 + 7].all isqrtOk),
    ("sqrtBall: certified by squaring, radius at most 2^-(k+1)",
      qs.all fun q => ks.all fun k =>
        let b := sqrtBall q k
        sqrtCertified q b && b.radius * 2 ^ (k + 1) ≤ 1),
    ("rational points: their own balls, drawn at their conversions",
      PlanePoint.re ((1 / 3 : Rat), (2 : Rat)) 9 == ⟨1 / 3, 0⟩ &&
      PlanePoint.toPoint ((1 / 4 : Rat), (-3 : Rat)) == ⟨0.25, -3⟩),
    ("Gaussian rationals: exact", PlanePoint.toPoint (GaussQ.mk (1 / 2) (-1)) == ⟨0.5, -1⟩),
    ("Q(√5): the golden ratio's balls are certified and within 2^-k",
      ks.all fun k =>
        let b := RealValue.ball gold k
        gold.certifies b && b.radius * 2 ^ k ≤ 1 && b.radius ≥ 0),
    ("Q(√5): balls of large coefficients certified and within 2^-k",
      ([⟨3, -1000⟩, ⟨-7 / 3, 12345 / 17⟩, ⟨0, 1⟩] : List QSqrt5).all fun x => ks.all fun k =>
        let b := RealValue.ball x k
        x.certifies b && b.radius * 2 ^ k ≤ 1),
    ("Q(√5): drawn near its value",
      near (RealValue.toFloat gold) 1.618033988749895 1e-15),
    ("Q(√5): the sign is decided exactly",
      QSqrt5.nonneg ⟨-2, 1⟩ && !QSqrt5.nonneg ⟨-3, 1⟩ && QSqrt5.nonneg ⟨3, -1⟩ &&
      !QSqrt5.nonneg ⟨2, -1⟩),
    ("Z[ζ5]: the balls of sin 72° and sin 144° are certified",
      [true, false].all fun plus => ks.all fun k =>
        let b := Zeta5.sinBall plus k
        let c : Rat := if plus then 2 else -2
        -- (4 lo)² ≤ 10 ± 2√5 ≤ (4 hi)², each side compared in Q(√5)
        QSqrt5.le ⟨16 * b.lo * b.lo, 0⟩ ⟨10, c⟩ && QSqrt5.le ⟨10, c⟩ ⟨16 * b.hi * b.hi, 0⟩ &&
          b.lo ≥ 0),
    ("Z[ζ5]: the real parts are certified, every radius within 2^-k",
      zeta.all fun z => ks.all fun k =>
        z.realPart.certifies (PlanePoint.re z k) && (PlanePoint.re z k).radius * 2 ^ k ≤ 1 &&
          (PlanePoint.im z k).radius * 2 ^ k ≤ 1 && (PlanePoint.im z k).radius ≥ 0),
    ("Z[ζ5]: the points are the fifth roots of unity",
      (List.range 5).all fun j =>
        nearPt (PlanePoint.toPoint (Zeta5.pow j)) (rootOfUnity 5 j) 1e-15),
    ("Z[ζ5]: sums of large coefficients within 2^-k",
      let z : Zeta5 := ⟨#[100, -2000, 37, 999]⟩
      ks.all fun k => (PlanePoint.im z k).radius * 2 ^ k ≤ 1 && (PlanePoint.re z k).radius * 2 ^ k ≤ 1),
    ("exact figure: the steps in the window are 1, ζ and ζ⁴",
      (List.range 5).filter inWindow == [0, 1, 4]),
    ("exact figure: each point's marker is centred at the frame's image of its conversion",
      zeta.all fun z =>
        let q := fig.env.frame.toScreen (PlanePoint.toPoint z)
        (drawItem fig.env (Plane.Exact.point z)).all fun s =>
          match s with
          | .path p _ _ _ => match p.bounds with
            | some b => nearPt ⟨(b.x0 + b.x1) / 2, (b.y0 + b.y1) / 2⟩ q 1e-9
            | none => false
          | _ => false),
    ("exact figure: the unit circle's points are the scale away from the origin's image",
      let o := fig.frame.toScreen ⟨0, 0⟩
      zeta.all fun z =>
        near ((fig.frame.toScreen (PlanePoint.toPoint z)) - o).norm fig.frame.scale 1e-9)]

/-- The checks. -/
def checks : Array (String × Bool) :=
  arcs ++ frames ++ labels ++ metadata ++ palette ++ figures ++ exact

end PILeanTest.PlaneChecks
