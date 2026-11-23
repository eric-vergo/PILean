/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanTest.Examples
import PILean.Trust.Build

/-!
# Checks of the figure checks, and of what they guard

Each check plants the fault a figure check is there to find and requires the check to report it
(by its kind), and requires the clean figure beside it to pass:

* plane figures: incidences held to the elements they name, contrast at a colour's alpha and along
  strokes over tints, numbers that are not finite, labels centred on strokes, unknown roles,
  colours the inline dark theme would restyle wrongly;
* regions of disks within rounding of touching, outside and inside, and their arcs;
* plots: axis labels and named series, the opt-out, and the levels;
* inline pictures: each is byte for byte the SVG file it comes with, every explorer frame a file;
* explorers and plane animations: their frames' problems, the plane figure's compositing and
  lettering, steps of one length, every frame a file;
* the frame of a figure with a label wider than the page, an arrowhead on a sweep of more than a
  turn, and the builders and helpers no other check exercises;
* the mathematics of the gallery's disks, in floating point beside the exact specification;
* `pilean-build`'s exit status on a figure whose checks level is `fail`.
-/

namespace PILeanTest.FigureChecks

open PILean PILean.Plane PILean.Exact PILean.Trust

/-- Whether `s` contains `t`. -/
def has (s t : String) : Bool := (s.splitOn t).length > 1

/-- Whether two floats differ by at most `tol`. -/
def near (a b : Float) (tol : Float := 1e-9) : Bool := (a - b).abs ≤ tol

/-- The kinds of a plane figure's problems. -/
def kinds (fig : Plane.Figure) : Array Plane.ProblemKind := fig.problems.map (·.kind)

/-- A figure of 300 pixels with these items. -/
def base (items : Array Item) : Plane.Figure := { items, width := 300 }

/-! ### Incidences -/

/-- The checks of recorded incidences. -/
def incidenceChecks : Array (String × Bool) :=
  let circleNamed := circle ⟨0, 0⟩ 1 |>.named "the circle"
  let far := point ⟨-2, -2⟩
  #[("incidence: a record names an element that exists, and holds",
      (kinds (base #[circleNamed, point ⟨1, 0⟩ |>.incident .on "the circle", far])).isEmpty),
    ("incidence: a point recorded on a circle but drawn off it is reported",
      (kinds (base #[circleNamed, point ⟨1.2, 0⟩ |>.incident .on "the circle", far])).contains
        .wrongIncidence),
    ("incidence: a point recorded inside a circle but drawn outside it is reported",
      (kinds (base #[circleNamed, point ⟨1.3, 0⟩ |>.incident .inside "the circle", far])).contains
        .wrongIncidence),
    ("incidence: a point recorded inside a segment is reported",
      (kinds (base #[segment ⟨0, 0⟩ ⟨2, 0⟩ |>.named "the segment",
        point ⟨1, 0.5⟩ |>.incident .inside "the segment", far])).contains .wrongIncidence),
    ("incidence: a record naming no element is reported, and silences nothing",
      -- the reviewer's case: the circle is unnamed, the record names something else
      let ks := kinds (base #[circle ⟨0, 0⟩ 1, point ⟨1.0001, 0⟩ |>.incident .inside
        "something else", far])
      ks.contains .unknownIncidenceTarget && ks.contains .undecidedIncidence),
    ("incidence: a record against one element does not excuse another one as near",
      let ks := kinds (base #[circleNamed, circle ⟨2, 0⟩ 1 |>.named "the other circle",
        point ⟨1, 0⟩ |>.incident .on "the circle", far])
      ks.contains .undecidedIncidence && !ks.contains .wrongIncidence),
    ("incidence: two records, one for each element, hold",
      (kinds (base #[circleNamed, circle ⟨2, 0⟩ 1 |>.named "the other circle",
        point ⟨1, 0⟩ |>.incident .on "the circle" |>.incident .on "the other circle",
        far])).isEmpty)]

/-! ### Contrast, numbers, labels, roles and dark themes -/

/-- The checks of contrast, non-finite numbers, centred labels, roles and the dark theme. -/
def drawingChecks : Array (String × Bool) :=
  let pts := #[point ⟨0, 0⟩, point ⟨1, 1⟩]
  let ghost := base (pts.push (label "invisible" ⟨0.5, 0.2⟩ .center |>.color ⟨0, 0, 0, 0⟩))
  let faded := base (pts.push (label "faded" ⟨0.5, 0.2⟩ .center |>.color ⟨0, 0, 0, 40⟩))
  let solid := base (pts.push (label "solid" ⟨0.5, 0.2⟩ .center))
  let onTint := fun (c : Rgba) => base #[disk ⟨0, 0⟩ 2 |>.color ⟨0, 0, 0, 255⟩ |>.fillOpacity 1,
    segment ⟨-1, 0⟩ ⟨1, 0⟩ |>.color c]
  let lineOn := base #[segment ⟨0, 0⟩ ⟨4, 0⟩ |>.named "across",
    segment ⟨2, -1⟩ ⟨2, 1⟩ |>.named "up", point ⟨0, 0⟩, point ⟨4, 1⟩,
    label "a long label on purpose" ⟨2, 0⟩ .center]
  let overUp := lineOn.problems.filter fun p => p.kind == .labelOverItem
  let nan : Float := 0 / 0
  let inf : Float := 1 / 0
  let nanFig := base #[point ⟨0, 0⟩, point ⟨1, 1⟩, point ⟨nan, 0⟩, point ⟨inf, 1⟩]
  let nanLens := base #[lens ⟨nan, 0⟩ 1 ⟨1, 0⟩ 1, point ⟨0, 0⟩, point ⟨2, 1⟩]
  let fixedLikeAccent := base #[segment ⟨0, 0⟩ ⟨1, 1⟩ |>.color (PlaneStyle.light.accent 0),
    point ⟨2, 0⟩]
  let shared : Style := { Style.light with plane := { PlaneStyle.light with
    roles := #[⟨"a", ⟨29, 78, 216, 255⟩, ⟨143, 176, 252, 255⟩⟩,
      ⟨"b", ⟨29, 78, 216, 255⟩, ⟨94, 224, 200, 255⟩⟩] } }
  let twoRoles : Plane.Figure := { base #[segment ⟨0, 0⟩ ⟨1, 0⟩ |>.role "a",
    segment ⟨0, 1⟩ ⟨1, 1⟩ |>.role "b"] with style := shared }
  #[("contrast: a transparent label is reported", (kinds ghost).contains .lowContrast),
    ("contrast: a label at a low alpha is reported, the same label opaque is not",
      (kinds faded).contains .lowContrast && !(kinds solid).contains .lowContrast),
    ("contrast: a stroke is checked against the tint under it, not the page",
      let strokeLow := fun (f : Plane.Figure) =>
        f.problems.any fun p => p.kind == .lowContrast && p.items == #[1]
      strokeLow (onTint ⟨20, 20, 20, 255⟩) && !strokeLow (onTint ⟨235, 235, 235, 255⟩)),
    ("labels: a label centred on a line is reported against both lines through its point",
      overUp.size == 2),
    ("numbers: points that are not finite are reported, and the SVG stays inert",
      (nanFig.problems.filter (·.kind == .nonFinite)).size == 2 && Svg.isInert nanFig.toSvg &&
        !has nanFig.toSvg "NaN"),
    ("numbers: a region of a disk whose centre is not finite is reported and draws nothing",
      (kinds nanLens).contains .nonFinite &&
      (regionArcs .intersection ⟨nan, 0⟩ 1 ⟨1, 0⟩ 1).isEmpty && !has nanLens.toSvg "NaN"),
    ("roles: a role the style does not name is reported",
      (kinds (base #[segment ⟨0, 0⟩ ⟨1, 0⟩ |>.role "missing"])).contains .unknownRole),
    ("dark theme: a fixed colour equal to a style colour is reported",
      (kinds fixedLikeAccent).contains .darkThemeClash),
    ("dark theme: two roles sharing a light colour with different dark ones are reported",
      (kinds twoRoles).contains .darkThemeClash),
    ("dark theme: the gallery's plane figures have no clash",
      Examples.planes.all fun (_, f) => !(kinds f).contains .darkThemeClash)]

/-! ### Regions of disks within rounding of touching -/

/-- Whether an angle of the arcs is not a number. -/
def hasNaN (arcs : Array (Array WorldArc)) : Bool :=
  arcs.any fun a => a.any fun (_, r, t0, t1) => t0.isNaN || t1.isNaN || r.isNaN

/-- The sum of the sweeps of the arcs of one boundary. -/
def sweep (arcs : Array WorldArc) : Float :=
  arcs.foldl (fun s (_, _, t0, t1) => s + (t1 - t0)) 0

/-- Whether the flattened page path of a region passes within `tol` pixels of the page point. -/
def pathReaches (f : Frame) (op : RegionOp) (c₁ : Point) (r₁ : Float) (c₂ : Point) (r₂ : Float)
    (q : Point) (tol : Float) : Bool :=
  ((regionPath f op c₁ r₁ c₂ r₂).flatten 0.1).any fun pl =>
    pl.points.any fun p => (p - q).norm ≤ tol

/-- The checks of regions of disks within rounding of touching (the reviewer's configuration,
and a sweep over many), and of the shapes of unions and differences. -/
def regionChecks : Array (String × Bool) :=
  let r1 : Float := 0.1137
  let r2 : Float := 1.491
  let c1 : Point := ⟨0.3, 0.7⟩
  let at_ := fun (d : Float) => (⟨0.3 + 0.6 * d, 0.7 + 0.8 * d⟩ : Point)
  let outside := at_ ((r1 + r2) * (1 - 2.2e-16))
  let inside := at_ ((r2 - r1) * (1 + 2.2e-16))
  let frame : Frame := { scale := 100, ox := 100, oy := 300, width := 400, height := 400 }
  let dir : Point := ⟨0.6, 0.8⟩
  let swept := Id.run do
    let mut bad := 0
    for i in [1:200] do
      for j in [1:50] do
        let a := 0.1 * i.toFloat + 0.0137
        let b := 0.37 * j.toFloat + 0.011
        for d in [a + b, a + b - 1e-15, (a - b).abs, (a - b).abs + 1e-15, (a + b) * (1 - 2.2e-16),
            (a - b).abs * (1 + 2.2e-16)] do
          for op in [RegionOp.intersection, .union, .difference] do
            if hasNaN (regionArcs op c1 a (at_ d) b) then bad := bad + 1
    return bad
  #[("regions: no angle of any region is NaN near tangency, over 300000 configurations",
      swept == 0),
    ("regions: two disks within rounding of touching outside: the union draws both circles",
      let u := regionArcs .union c1 r1 outside r2
      !hasNaN u && u.size == 1 && near (sweep u[0]!) (4 * pi) 1e-6 &&
      pathReaches frame .union c1 r1 outside r2 (frame.toScreen (c1 - r1 * dir)) 0.5 &&
      pathReaches frame .union c1 r1 outside r2 (frame.toScreen (outside + r2 * dir)) 0.5),
    ("regions: within rounding of touching outside, the difference keeps the first disk",
      let d := regionArcs .difference c1 r1 outside r2
      !hasNaN d && pathReaches frame .difference c1 r1 outside r2
        (frame.toScreen (c1 - r1 * dir)) 0.5),
    ("regions: within rounding of touching inside, the lens is the small disk whole",
      let l := regionArcs .intersection c1 r1 inside r2
      !hasNaN l && l.size == 1 && near (sweep l[0]!).abs (2 * pi) 1e-6 &&
      pathReaches frame .intersection c1 r1 inside r2 (frame.toScreen (c1 - r1 * dir)) 0.5),
    ("regions: the near-tangent figures draw every disk and report nothing not finite",
      [RegionOp.intersection, .union, .difference].all fun op =>
        [outside, inside].all fun c2 =>
          let f := base #[.shape (.disks op c1 r1 c2 r2), point ⟨-1, -1⟩, point ⟨3, 3⟩]
          !(kinds f).contains .nonFinite && !has f.toSvg "NaN"),
    ("regions: the union of crossing disks is one boundary of two arcs, each short of a turn",
      let u := regionArcs .union ⟨0, 0⟩ 1 ⟨1, 0⟩ 1
      u.size == 1 && u[0]!.size == 2 &&
      -- the crossings are at ±60° from each centre: each arc sweeps 360° - 120°
      u[0]!.all fun (_, _, t0, t1) => near (t1 - t0) (2 * pi - 2 * pi / 3) 1e-9),
    ("regions: the difference of crossing disks is the first arc forwards and the second back",
      let d := regionArcs .difference ⟨0, 0⟩ 1 ⟨1, 0⟩ 1
      d.size == 1 && d[0]!.size == 2 &&
      near (d[0]![0]!.2.2.2 - d[0]![0]!.2.2.1) (2 * pi - 2 * pi / 3) 1e-9 &&
      near (d[0]![1]!.2.2.2 - d[0]![1]!.2.2.1) (-(2 * pi / 3)) 1e-9)]

/-! ### Plots -/

/-- A one-panel plot with these axes, series and notes. -/
def plot (x y : String) (series : Array Plot.Series) (notes : Array Plot.Annotation := #[])
    (legend : Bool := true) (bare : Bool := false) : Plot.Figure :=
  { legend, panels := #[{ x := { label := x }, y := { label := y }, series, notes, bare }] }

/-- The kinds of a plot's problems. -/
def plotKinds (fig : Plot.Figure) : Array Plot.ProblemKind := fig.problems.map (·.kind)

/-- The checks of the labelling of plots. -/
def plotChecks : Array (String × Bool) :=
  let one := #[Plot.Series.line "a" #[⟨0, 0⟩, ⟨1, 1⟩]]
  let two := one.push (.line "b" #[⟨0, 1⟩, ⟨1, 0⟩])
  let unnamed := #[Plot.Series.line "" #[⟨0, 0⟩, ⟨1, 1⟩], .line "" #[⟨0, 1⟩, ⟨1, 0⟩]]
  let failing : Plot.Figure := { plot "" "y" one with checks := .fail }
  let warned := plot "" "y" one
  #[("plots: an axis without a label is reported",
      (plotKinds (plot "" "y" one)).contains .noXLabel &&
      (plotKinds (plot "x" "" one)).contains .noYLabel),
    ("plots: two series with no legend and no direct labels are reported",
      (plotKinds (plot "x" "y" two (legend := false))).contains .unnamedSeries &&
      (plotKinds (plot "x" "y" unnamed)).contains .unnamedSeries),
    ("plots: a legend, or a direct label for each series, names them",
      (plotKinds (plot "x" "y" two)).isEmpty &&
      (plotKinds (plot "x" "y" two #[.text ⟨0, 0⟩ "a", .text ⟨1, 1⟩ "b"] (legend := false))).isEmpty),
    ("plots: the groups of a bar series count as series",
      (plotKinds (plot "x" "y" #[.bars #["p", "q"] #[("", #[1, 2]), ("", #[2, 1])]])).contains
        .unnamedSeries),
    ("plots: a panel bare on purpose is not checked",
      (plotKinds (plot "" "" unnamed (bare := true))).isEmpty),
    ("plots: warn reports on the SVG, fail stops every output, ignore reports nothing",
      let w := ToOutputs.outputs warned
      let f := ToOutputs.outputs failing
      (w[0]!.problems ()).size == 1 && (w[1]!.problems ()).isEmpty &&
      f.all (fun o => match o.bytes () with | .error _ => true | .ok _ => false) &&
      ({ warned with checks := .ignore } : Plot.Figure).checkMessages.isEmpty),
    ("plots: the gallery's plots and the plots its animations are drawn from are labelled",
      Examples.gallery.all (fun (_, f) => f.problems.isEmpty) &&
      [0, 0.7, 1.9].all fun t => (Examples.Animations.waveFigure t).problems.isEmpty &&
        (Examples.Animations.barsFigure t).problems.isEmpty)]

/-! ### Explorers and plane animations -/

/-- Two labels on top of each other. -/
def overlapping : Plane.Figure :=
  base #[point ⟨0, 0⟩, point ⟨3, 1⟩, label "first label" ⟨1, 1⟩, label "second label" ⟨1.1, 1⟩]

/-- A clean figure. -/
def clean : Plane.Figure := base #[point ⟨0, 0⟩, point ⟨3, 1⟩]

/-- A tinted disk with two points, for the colour of animation frames. -/
def tinted : Plane.Figure :=
  { width := 200, items := #[disk ⟨0, 0⟩ 1 |>.accent 0 |>.noOutline,
      point ⟨1.6, 1.6⟩ |>.halo false, point ⟨-1.6, -1.6⟩ |>.halo false,
      label "A" ⟨1.6, 1.6⟩ .aboveRight] }

/-- Whether two colours differ by at most `tol` levels in each channel. -/
def nearColour (a b : Rgba) (tol : Nat := 1) : Bool :=
  let d := fun (x y : UInt8) => if x ≥ y then (x - y).toNat else (y - x).toNat
  d a.r b.r ≤ tol && d a.g b.g ≤ tol && d a.b b.b ≤ tol

/-- The SVG of an explorer frame's drawing, to tell frames apart. -/
def drawingText (s : Canvas.Shape) : String :=
  String.join ((s.render (.native "sans-serif")).toList.map (Svg.render 0))

/-- The checks of explorers and plane animations. -/
def explorerChecks : Array (String × Bool) :=
  let x := Plane.slider "r" #[("1", clean), ("2", overlapping)]
  let xFail := Plane.slider "r" #[("1", clean), ("2", { overlapping with checks := .fail })]
  let outs := ToOutputs.outputs x
  let failOuts := ToOutputs.outputs xFail
  let anim := Plane.animation #[clean, overlapping]
  let animFail := Plane.animation #[clean, { overlapping with checks := .fail }]
  let tintAnim := Plane.animation #[tinted, tinted]
  let tf := (commonView #[tinted, tinted])[0]!
  let q := tf.frame.toScreen ⟨0, 0⟩
  let figPixel := tf.toImage.getpixel q.x.toUInt64.toNat q.y.toUInt64.toNat
  let animPixel := ((tintAnim.frame 0).toImage tintAnim.width tintAnim.height tintAnim.text
    tintAnim.background tintAnim.space).getpixel q.x.toUInt64.toNat q.y.toUInt64.toNat
  -- three steps of 0.4 s, each a different rectangle
  let stepFrame := fun (j : Nat) =>
    let bar : Canvas.Shape :=
      .path (Canvas.rect 0 0 (10 * (j + 1)).toFloat 5) (some (.solid ⟨0, 0, 0, 255⟩)) none
    ({ drawing := bar, width := 40, height := 10 } : ExplorerFrame)
  let stepper := Explorer.stepper #[("a", stepFrame 0), ("b", stepFrame 1), ("c", stepFrame 2)]
  let played := stepper.toAnimation 0 0.4
  let shown := (List.range played.frameCount).map fun i =>
    (List.range 3).find? fun j => drawingText (played.frame (played.time i)) ==
      drawingText (stepFrame j).drawing
  let counts := (List.range 3).map fun j => (shown.filter (· == some j)).length
  #[("explorer: a frame's problems are reported on the poster's SVG, by frame",
      let ps := outs[0]!.problems ()
      ps.size > 0 && ps.all (has · "frame 1, r = 2")),
    ("explorer: a frame whose level is fail stops every output",
      failOuts.all fun o => match o.bytes () with | .error _ => true | .ok _ => false),
    ("explorer: the gallery's explorer has no problem in any frame",
      Examples.PlaneFigures.windowRadius.problems.isEmpty),
    ("explorer: every frame is an SVG output of its own, its file the inline picture",
      let frames := outs.filter (·.name.startsWith "-frame-")
      frames.size == x.frames.size &&
      frames.zipIdx.all fun (o, k) => o.name == s!"-frame-{k}" && match o.bytes (), o.inline () with
        | .ok b, some i => b == i.document.toUTF8 && o.spec == b
        | _, _ => false),
    ("animation: the steps' problems are reported, and fail stops it",
      ((ToOutputs.outputs anim)[0]!.problems ()).size > 0 &&
      (ToOutputs.outputs animFail).all fun o => match o.bytes () with
        | .error _ => true | .ok _ => false),
    ("animation: a plane animation's frames composite in sRGB, as the figure's image does",
      tintAnim.srgb && nearColour figPixel animPixel 1),
    ("animation: a plane animation's SVG draws text as shapes, as the figure's does",
      tintAnim.textAsShapes && !has tintAnim.posterSvg "<text" && !has tintAnim.toSvg "<text"),
    ("animation: steps of 0.4 s each take the same number of frames",
      Explorer.stepTiming 0.4 == (5, 2) && counts == [2, 2, 2] &&
      [0.3, 0.7, 1, 1.37, 2.5].all fun (s : Float) =>
        let (fps, k) := Explorer.stepTiming s
        ((k.toFloat / fps.toFloat) - s).abs / s ≤ 0.05)]

/-! ### Inline pictures -/

/-- Whether every output of `os` that gives an inline picture gives the document of its own bytes
(before any source record), and whether at least one does. -/
def inlineIsFile (os : Array Output) : Bool :=
  let inl := os.filter fun o => (o.inline ()).isSome
  !inl.isEmpty && inl.all fun o => match o.bytes (), o.inline () with
    | .ok b, some i => b == i.document.toUTF8 && o.spec == b
    | _, _ => false

/-- The checks that an inline picture is its file: for every plot, plane figure (narrow renditions
included) and explorer of the gallery. -/
def inlineChecks : Array (String × Bool) :=
  #[("inline: every plot's inline picture is its SVG file",
      Examples.gallery.all fun (_, f) => inlineIsFile (ToOutputs.outputs f)),
    ("inline: every plane figure's inline picture is its SVG file, narrow renditions included",
      Examples.planes.all fun (_, f) => inlineIsFile (ToOutputs.outputs f) &&
        (f.narrowWidth.isNone || ((ToOutputs.outputs f).filter fun o =>
          o.name == "-narrow" && (o.inline ()).isSome).size == 1)),
    ("inline: every frame of the gallery's explorer is a file, its inline picture byte for byte",
      let x := Examples.PlaneFigures.windowRadius
      let os := ToOutputs.outputs x
      inlineIsFile os && (os.filter (·.name.startsWith "-frame-")).size == x.frames.size &&
      match (os[0]!.frames ()) with
      | some fs => fs.frames.zipIdx.all fun (i, k) => match os[k + 2]? with
        | some o => match o.bytes () with
          | .ok b => b == i.document.toUTF8
          | .error _ => false
        | none => false
      | none => false)]

/-! ### Frames, arcs, builders and helpers -/

/-- The checks of fitting with a label wider than the page, arrowheads on long sweeps, and the
builders and helpers the other checks do not reach. -/
def miscChecks : Array (String × Bool) :=
  let wide : Plane.Figure := { width := 480, items := #[segment ⟨0, 0⟩ ⟨1, 0⟩, point ⟨0, 0⟩,
    label (String.ofList (List.replicate 200 'W')) ⟨0, 0⟩ .right] }
  let env : Env := { frame := { scale := 1, width := 400, height := 400 }, style := Style.light }
  let longArc := env.arcShapes {} ⟨200, 200⟩ 100 0 (3 * pi) true
  let tip : Point := ⟨200 + 100 * (3 * pi).cos, 200 - 100 * (3 * pi).sin⟩
  let strokeEnd := match longArc[0]? with
    | some (.path p _ _ _) => (p.flatten 0.1).back?.bind (·.points.back?)
    | _ => none
  let ex := Plane.Exact.graph Examples.PlaneFigures.ringGraph Examples.PlaneFigures.ringPositions
  let exPoints := ex.leaves.filterMap fun lf => match lf.geom with
    | .point p => some p
    | _ => none
  let views := commonView #[clean, base #[point ⟨5, 5⟩]]
  let pairs := Style.light.darkColourPairs
  #[("frame: a label wider than the page leaves the geometry fitted, and is reported",
      wide.frame.scale > 100 && (kinds wide).contains .outside),
    ("arc: a sweep of more than a turn keeps its arrowhead on its end",
      match strokeEnd with
      | some q => (q - tip).norm ≤ Style.light.plane.arrowLength * 1.05
      | none => false),
    ("builders: an exact graph's nodes are at the conversions of their points",
      exPoints.size == 7 && (exPoints.zip Examples.PlaneFigures.ringPositions).all fun (p, e) =>
        p == PlanePoint.toPoint e),
    ("builders: the exact union and difference are regions of their disks",
      match Plane.Exact.diskUnion ((0 : Rat), (0 : Rat)) ((1 : Rat), (0 : Rat)) (1 : Rat) (1 : Rat),
          Plane.Exact.diskDifference ((0 : Rat), (0 : Rat)) ((1 : Rat), (0 : Rat)) (1 : Rat)
            (1 : Rat) with
      | .shape (.disks .union ..) .., .shape (.disks .difference ..) .. => true
      | _, _ => false),
    ("builders: an exact tick stands at its point, across its segment",
      match Plane.Exact.tickAt ((1 : Rat), (0 : Rat)) ((0 : Rat), (0 : Rat)) ((2 : Rat), (0 : Rat))
      with
      | .shape (.tick p d _) .. => p == ⟨1, 0⟩ && d == ⟨2, 0⟩
      | _ => false),
    ("builders: fillTone tints a disk in another tone than its outline",
      match disk ⟨0, 0⟩ 1 |>.accent 0 |>.fillTone (.accent 2) with
      | .shape g l _ => match drawGeom env l g with
        | #[.path _ (some (.solid c)) (some ln) _] =>
          c.rgbHex == (PlaneStyle.light.accent 2).rgbHex &&
            ln.ink.rgbHex == (PlaneStyle.light.accent 0).rgbHex
        | _ => false
      | _ => false),
    ("helpers: figures given one view share it and its height",
      views.size == 2 && views[0]!.view == views[1]!.view && views[0]!.view.isSome &&
        views[0]!.height == views[1]!.height),
    ("helpers: the dark pairs of the light style, the first pairing of a colour kept",
      pairs.contains (Style.light.background.rgbHex, Style.dark.background.rgbHex) &&
      pairs.contains ((PlaneStyle.light.accent 0).rgbHex, (PlaneStyle.dark.accent 0).rgbHex) &&
      Style.dark.darkColourPairs.isEmpty &&
      (pairs.map (·.1)).all fun h => (pairs.filter (·.1 == h)).size == 1),
    ("gallery: every vertex of the graph in a window is clear of the window's boundary",
      let f := Examples.PlaneFigures.graphInWindow
      let e := f.env
      let lv := f.leaves
      let ring := strokeSegments e lv[0]!
      lv.all fun lf => match markerOf e lf with
        | some (c, r) => distToSegments c ring ≥ r + 6
        | none => true),
    ("gallery: the narrow reference figure's centre labels keep clear of the lens",
      match PILeanTest.PlaneExact.reference.narrow with
      | some n =>
        let g := n.autoPlaced
        let e := g.env
        let lv := g.leaves
        let lensSegs := strokeSegments e lv[2]!
        lv.all fun lf => match lf.geom, labelOf e lf with
          | .label s .., some (b, _) =>
            !(s == "−1" || s == "+1") || lensSegs.all fun (a, c) =>
              [a, c, a.mid c].all fun q => distToBox q b ≥ 3
          | _, _ => true
      | none => false)]

/-! ### The mathematics of the gallery's disks -/

/-- `e^{2πi j/5}` in floating point, from the cosine and sine. -/
def zeta (j : Nat) : Point := ⟨(2 * pi * j.toFloat / 5).cos, (2 * pi * j.toFloat / 5).sin⟩

/-- The checks of the disks figure's mathematics in floating point, independently of ℤ[ζ₅]: `E =
ζ - ζ²` is on the circle about `-1` of radius `√(3 + φ)` and inside the one about `1`, and the
circles cross at `±(ζ - ζ⁴)`; and the exact points are drawn where these are. -/
def mathChecks : Array (String × Bool) :=
  let φ := (1 + Float.sqrt 5) / 2
  let R := Float.sqrt (3 + φ)
  let e := zeta 1 - zeta 2
  let c := zeta 1 - zeta 4
  let dist := fun (p q : Point) => (p - q).norm
  #[("disks: E is on the left circle and inside the right disk",
      near (dist e ⟨-1, 0⟩) R 1e-12 && dist e ⟨1, 0⟩ < R - 1),
    ("disks: -E is on the right circle and inside the left disk",
      near (dist ((-1 : Float) * e) ⟨1, 0⟩) R 1e-12 && dist ((-1 : Float) * e) ⟨-1, 0⟩ < R - 1),
    ("disks: the circles cross at ±(ζ - ζ⁴), on the imaginary axis, and not at ±E",
      near (dist c ⟨-1, 0⟩) R 1e-12 && near (dist c ⟨1, 0⟩) R 1e-12 && near c.x 0 1e-12 &&
      near (dist ((-1 : Float) * c) ⟨1, 0⟩) R 1e-12 && !near (dist e ⟨1, 0⟩) R 1e-3),
    ("disks: the exact points are drawn at these places",
      (PlanePoint.toPoint Examples.PlaneFigures.chordEnd - e).norm < 1e-12 &&
      (PlanePoint.toPoint Examples.PlaneFigures.crossing - c).norm < 1e-12 &&
      near (RealValue.toFloat Examples.PlaneFigures.critical) R 1e-12)]

/-! ### `pilean-build` on a figure that fails its checks -/

/-- A plane figure whose labels overlap and whose checks level is `fail`. -/
@[figure] def failingPlane : Plane.Figure := { overlapping with checks := .fail }

/-- A plot without axis labels whose checks level is `fail`. -/
@[figure] def failingPlot : Plot.Figure :=
  { width := 160, height := 100, checks := .fail,
    panels := #[{ series := #[.function "x²" (fun x => x * x) (-1) 1] }] }

/-- A plane figure with problems at the level `warn`. -/
@[figure] def warnedPlane : Plane.Figure := overlapping

/-- The tagged figures of this module. -/
def tagged : Array FigureEntry := (figures% : Array FigureEntry).filter
  (·.module == "PILeanTest.FigureChecks")

/-- The checks of `pilean-build`'s command line on a figure that fails its checks: exit status 1
for a build and a check, 0 for the figure that only warns. -/
def ioChecks : IO (Array (String × Bool)) := do
  let root : System.FilePath := ".lake" / "pilean-test-figure-checks"
  if ← root.pathExists then IO.FS.removeDirAll root
  let pick := fun (d : String) => tagged.filter (·.decl.endsWith d)
  let planeCode ← buildMain (pick "failingPlane") ["--out", (root / "a").toString]
  let plotCode ← buildMain (pick "failingPlot") ["--out", (root / "b").toString]
  let checkCode ← buildMain (pick "failingPlane") ["--out", (root / "a").toString, "--check"]
  let warnCode ← buildMain (pick "warnedPlane") ["--out", (root / "c").toString]
  IO.FS.removeDirAll root
  return #[("pilean-build: a plane figure whose checks fail makes the build exit 1",
      (pick "failingPlane").size == 1 && planeCode == 1),
    ("pilean-build: a plot whose checks fail makes the build exit 1",
      (pick "failingPlot").size == 1 && plotCode == 1),
    ("pilean-build: and the check of its directory exits 1", checkCode == 1),
    ("pilean-build: a figure that only warns builds", (pick "warnedPlane").size == 1 &&
      warnCode == 0)]

/-- The checks. -/
def checks : Array (String × Bool) :=
  incidenceChecks ++ drawingChecks ++ regionChecks ++ plotChecks ++ explorerChecks ++
    inlineChecks ++ miscChecks ++ mathChecks

end PILeanTest.FigureChecks
