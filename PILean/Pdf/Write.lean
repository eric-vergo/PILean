/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Raster.SvgRender
import PILean.Pdf.Object
import PILean.Png.Deflate
import PILean.Image.Basic
import PILean.Trust.Sha256

/-!
# PDF output

A writer of one-page PDF 1.7 documents, in pure Lean, for pictures that go into papers. The page is
written from the same SVG nodes as the SVG file and the PNG (`PILean.Svg.Node`, with text as shapes
from a `TextEngine`), so the three show one drawing; the PDF is a vector picture that needs no
fonts.

What is written, as the rasteriser reads the nodes (`PILean.Raster.Svg.rasterize`): `g` (its
presentation attributes inherited, its `opacity` as a transparency group, its `clip-path` as a
clipping path), `rect` (with `rx`), `line`, `circle`, `ellipse`, `polyline`, `polygon`, `path`
(quadratic pieces raised to cubics, exactly), `clipPath` and gradients in `defs`; fills with the
non-zero and even-odd rules, strokes with their width, caps, joins, miter limit and dashes,
`fill-opacity` and `stroke-opacity` (an `ExtGState`), linear and radial gradients (axial and
radial shadings with a stitching function through the sampled stops `Raster.gradientNode` writes,
extended at both ends as SVG pads them). Colours are `DeviceRGB` with the file's 8-bit sRGB values.

Not written: `text` elements (text reaches a PDF as shapes, so a PDF embeds no font and its text
cannot be selected), `title`, `desc` and `metadata` (the source record is written separately,
`PILean.Trust.withSourcePdf`), and what the rasteriser does not draw either. A gradient whose
stops have different opacities is drawn at their mean opacity (PDF would need a soft mask for
more). A raster `Image` is written as a page of its own (`Pdf.ofImage`): its samples as an image
`XObject`, compressed with PILean's DEFLATE, its alpha as a soft mask.

**Size.** A picture of `w × h` pixels is a page of `0.75 w × 0.75 h` points: one CSS pixel is
`1/96` inch and one point `1/72` inch (`ptPerPx`). The content keeps the pixel coordinates under one
transformation (`0.75 0 0 -0.75 0 H cm`, which also turns the `y` axis up).

**Deterministic bytes.** Objects in a fixed order (catalog, page tree, page, resources, content,
then the forms and images in drawing order), numbers through `fmtNum`, no dates, and a document
ID made of the first 16 bytes of the SHA-256 of everything before the cross-reference table. The
file ends with a classic cross-reference table and trailer; there are no object streams.

## Main definitions

* `Pdf.ptPerPx`, `Pdf.Obj`, `Pdf.Obj.write`, `Pdf.document`.
* `Pdf.ofSvgNodes`: one page from SVG nodes; `Pdf.ofImage`: one page from a raster image.

## References

* ISO 32000-1:2008, *Document management — Portable document format — Part 1: PDF 1.7*:
  7.3 (objects), 7.5 (file structure), 8.4–8.5 (graphics state, path construction and painting),
  8.7.4.5 (shadings), 7.10 (functions), 8.9 (images), 11 (transparency).
* CSS Values and Units Module Level 3, 6.2 (the reference pixel, `1px = 1/96in`).
-/

namespace PILean.Pdf

open PILean.Svg

/-- Points per CSS pixel: a pixel is `1/96` inch and a point `1/72` inch. -/
def ptPerPx : Float := 0.75

/-- A number as an object. -/
def num (x : Float) : Obj := .real x

/-- A stream object's body: its dictionary with `/Length` (and `/Filter /FlateDecode` when
`compress`, the data then compressed by PILean's zlib writer), the keyword `stream`, the data and
`endstream`. -/
def streamBody (dict : Array (String × Obj)) (data : ByteArray) (compress : Bool := true) :
    ByteArray :=
  let data := if compress then Png.zlibCompress data else data
  let filter := if compress then #[("Filter", Obj.name "FlateDecode")] else #[]
  (Obj.dict (dict ++ filter ++ #[("Length", .int data.size)])).write.toUTF8 ++ "\nstream\n".toUTF8 ++
    data ++ "\nendstream".toUTF8

/-- The file of the indirect objects `bodies` (object `k + 1` is `bodies[k]`) with object `root`
as the catalog: the header (with a comment of four bytes above 127, so that the file is taken for
binary), the objects, the cross-reference table, and the trailer with `/Size`, `/Root` and `/ID`
(two equal strings: the first 16 bytes of the SHA-256 of everything before the table). -/
def document (bodies : Array ByteArray) (root : Nat) : ByteArray := Id.run do
  let mut out := "%PDF-1.7\n".toUTF8 ++ ⟨#[37, 0xE2, 0xE3, 0xCF, 0xD3, 10]⟩
  let mut offsets : Array Nat := #[]
  for (b, k) in bodies.zipIdx do
    offsets := offsets.push out.size
    out := out ++ s!"{k + 1} 0 obj\n".toUTF8 ++ b ++ "\nendobj\n".toUTF8
  let id := hexString ((Sha256.hash out).extract 0 16)
  let xref := out.size
  let mut table := s!"xref\n0 {bodies.size + 1}\n0000000000 65535 f \n"
  for o in offsets do table := table ++ pad10 o ++ " 00000 n \n"
  let trailer := s!"trailer\n<< /Size {bodies.size + 1} /Root {root} 0 R /ID [{id} {id}] >>\n\
    startxref\n{xref}\n%%EOF\n"
  return out ++ (table ++ trailer).toUTF8

/-! ### Pages from SVG nodes -/

/-- The graphics state the content has set, so that an operator is written only when it changes
something. -/
structure GState where
  /-- The fill colour operator last written (`r g b rg`). -/
  fill : String := ""
  /-- The stroke colour operator last written (`r g b RG`). -/
  stroke : String := ""
  /-- The `ExtGState` last set, by name. -/
  alpha : String := ""
  /-- The line width, caps, joins, miter limit and dashes last written, as one text. -/
  line : String := ""
  deriving Inhabited

/-- What the content of a page refers to, collected while it is written. -/
structure State where
  /-- The `ExtGState` dictionaries (`/ca`, `/CA`), named `G0`, `G1`, … in order. -/
  alphas : Array String := #[]
  /-- The shading dictionaries, named `S0`, `S1`, …. -/
  shadings : Array String := #[]
  /-- The objects of the forms and images (`X0`, `X1`, …), numbered from `firstObject`. -/
  xobjects : Array ByteArray := #[]
  /-- The graphics state. -/
  gs : GState := {}
  deriving Inhabited

/-- The number of the first form or image object: 1 catalog, 2 page tree, 3 page, 4 resources,
5 content. -/
def firstObject : Nat := 6

/-- The object number of the resources, which every form shares with the page. -/
def resourcesObject : Nat := 4

/-- The name of an `ExtGState` with fill and stroke opacities `ca` and `CA`, added if new. -/
def alphaName (ca sa : Float) : StateM State String := do
  let d := s!"<< /ca {fmtNum ca 3} /CA {fmtNum sa 3} >>"
  let st ← get
  match st.alphas.idxOf? d with
  | some k => return s!"G{k}"
  | none =>
    set { st with alphas := st.alphas.push d }
    return s!"G{st.alphas.size}"

/-- The operator that sets the opacities, or nothing when they are already set. -/
def setAlpha (ca sa : Float) : StateM State String := do
  let ca := max 0 (min 1 ca)
  let sa := max 0 (min 1 sa)
  let st ← get
  if st.gs.alpha.isEmpty && ca == 1 && sa == 1 then return ""
  let n ← alphaName ca sa
  let st ← get
  if st.gs.alpha == n then return ""
  set { st with gs := { st.gs with alpha := n } }
  return s!"/{n} gs\n"

/-- A colour's three components (`0` to `1`, three decimals) and an operator. -/
def colourOp (c : Rgba) (op : String) : String :=
  let f := fun (v : UInt8) => fmtNum (v.toNat.toFloat / 255) 4
  s!"{f c.r} {f c.g} {f c.b} {op}"

/-- The operator that sets the fill colour, or nothing when it is set. -/
def setFill (c : Rgba) : StateM State String := do
  let op := colourOp c "rg"
  let st ← get
  if st.gs.fill == op then return ""
  set { st with gs := { st.gs with fill := op } }
  return op ++ "\n"

/-- The operator that sets the stroke colour, or nothing when it is set. -/
def setStroke (c : Rgba) : StateM State String := do
  let op := colourOp c "RG"
  let st ← get
  if st.gs.stroke == op then return ""
  set { st with gs := { st.gs with stroke := op } }
  return op ++ "\n"

/-- The operators of a stroke's width, caps, joins, miter limit and dashes (a pattern with a
negative entry, or whose entries sum to nothing, is solid, as SVG reads it). -/
def lineOps (s : Raster.Stroke) : String :=
  let cap := match s.cap with | .butt => 0 | .round => 1 | .square => 2
  let join := match s.join with | .miter => 0 | .round => 1 | .bevel => 2
  let solid := s.dash.isEmpty || s.dash.any (· < 0) || s.dash.foldl (· + ·) 0 ≤ 0
  let dash := if solid then "[] 0 d"
    else "[" ++ " ".intercalate (s.dash.toList.map (fmtNum · 3)) ++ "] " ++ fmtNum s.dashOffset 3 ++
      " d"
  s!"{fmtNum s.width 3} w {cap} J {join} j {fmtNum (max 1 s.miterLimit) 3} M {dash}"

/-- The operators of a stroke's parameters, or nothing when they are set. -/
def setLine (s : Raster.Stroke) : StateM State String := do
  let ops := lineOps s
  let st ← get
  if st.gs.line == ops then return ""
  set { st with gs := { st.gs with line := ops } }
  return ops ++ "\n"

/-- A point as two numbers. -/
def pt (p : Point) : String := fmtNum p.x 3 ++ " " ++ fmtNum p.y 3

/-- The path construction operators of a path: `m`, `l`, `c` (a quadratic piece raised to the
cubic with control points `p₀ + 2/3 (c - p₀)` and `p + 2/3 (c - p)`, the same curve) and `h`. -/
def pathOps (p : Path) : String := Id.run do
  let mut out := ""
  let mut cur : Point := ⟨0, 0⟩
  let mut start : Point := ⟨0, 0⟩
  for c in p.cmds do
    match c with
    | .move q => out := out ++ pt q ++ " m\n"; cur := q; start := q
    | .line q => out := out ++ pt q ++ " l\n"; cur := q
    | .quad k q =>
      let c1 : Point := ⟨cur.x + 2 / 3 * (k.x - cur.x), cur.y + 2 / 3 * (k.y - cur.y)⟩
      let c2 : Point := ⟨q.x + 2 / 3 * (k.x - q.x), q.y + 2 / 3 * (k.y - q.y)⟩
      out := out ++ pt c1 ++ " " ++ pt c2 ++ " " ++ pt q ++ " c\n"; cur := q
    | .cubic a b q => out := out ++ pt a ++ " " ++ pt b ++ " " ++ pt q ++ " c\n"; cur := q
    | .close => out := out ++ "h\n"; cur := start
  return out

/-- The colour and offset pieces of a gradient's stops for a stitching function: offsets clamped
to `[0, 1]` and made non-decreasing, a constant piece added before the first and after the last
stop, and pieces of no length dropped (the later colour wins, as in SVG). -/
def stopPieces (stops : Array Raster.Stop) : Array (Float × Rgba) := Id.run do
  let mut out : Array (Float × Rgba) := #[]
  let mut last : Float := 0
  for s in stops do
    let o := max last (max 0 (min 1 (if s.offset.isNaN then 0 else s.offset)))
    last := o
    out := out.push (o, s.color)
  match (out[0]? : Option (Float × Rgba)), (out.back? : Option (Float × Rgba)) with
  | some (o0, c0), some (o1, c1) =>
    let ps := (if o0 > 0 then #[((0 : Float), c0)] else #[]) ++ out ++
      (if o1 < 1 then #[((1 : Float), c1)] else #[])
    -- drop a stop at the offset of the next one
    return ps.zipIdx.filterMap fun ((o, c), k) =>
      match ps[k + 1]? with
      | some (o', _) => if o' == o then none else some (o, c)
      | none => some (o, c)
  | _, _ => return #[]

/-- The function of a shading through the pieces (`stopPieces`): a type 2 function between two
colours, or a type 3 function stitching one per pair of neighbours; `none` without stops. -/
def stopsFunction (stops : Array Raster.Stop) : Option Obj :=
  let ps := stopPieces stops
  let comps := fun (c : Rgba) => Obj.arr #[.real (c.r.toNat.toFloat / 255) 4,
    .real (c.g.toNat.toFloat / 255) 4, .real (c.b.toNat.toFloat / 255) 4]
  let lin := fun (a b : Rgba) => Obj.dict #[("FunctionType", .int 2), ("Domain", .arr #[.int 0, .int 1]),
    ("C0", comps a), ("C1", comps b), ("N", .int 1)]
  match ps.size with
  | 0 => none
  | 1 => ps[0]?.map fun (_, c) => lin c c
  | 2 => some (lin (ps[0]?.getD (0, default)).2 (ps[1]?.getD (0, default)).2)
  | n =>
    let pieces := (List.range (n - 1)).toArray.map fun k =>
      lin (ps[k]?.getD (0, default)).2 (ps[k + 1]?.getD (0, default)).2
    let bounds := ((List.range (n - 2)).toArray.map fun k => Obj.real (ps[k + 1]?.getD (0, default)).1 4)
    let encode := (List.range (n - 1)).toArray.flatMap fun _ => #[Obj.int 0, Obj.int 1]
    some (.dict #[("FunctionType", .int 3), ("Domain", .arr #[.int 0, .int 1]),
      ("Functions", .arr pieces), ("Bounds", .arr bounds), ("Encode", .arr encode)])

/-- The mean opacity of a gradient's stops (`0` to `1`). -/
def stopsAlpha (stops : Array Raster.Stop) : Float :=
  if stops.isEmpty then 1
  else (stops.foldl (fun a s => a + s.color.a.toNat.toFloat) 0) / (255 * stops.size.toFloat)

/-- The name of a shading for a gradient paint, added to the resources; `none` for a solid paint
or a gradient without stops. -/
def shadingName (p : Raster.Paint) : StateM State (Option String) := do
  let (ty, coords, stops) := match p with
    | .linear a b stops => (2, #[num a.x, num a.y, num b.x, num b.y], stops)
    | .radial c r stops => (3, #[num c.x, num c.y, .int 0, num c.x, num c.y, num (max 0 r)], stops)
    | .solid _ => (0, #[], #[])
  if ty == 0 then return none
  let some f := stopsFunction stops | return none
  let d := (Obj.dict #[("ShadingType", .int ty), ("ColorSpace", .name "DeviceRGB"),
    ("Coords", .arr coords), ("Function", f), ("Extend", .arr #[.bool true, .bool true])]).write
  let st ← get
  set { st with shadings := st.shadings.push d }
  return some s!"S{st.shadings.size}"

/-- The content of one shape: its fill (a colour, or a gradient painted inside the path as a
clip) and its stroke, with the opacities and the stroke's parameters. -/
def shapeOps (p : Path) (s : Raster.Style) : StateM State String := do
  if p.cmds.isEmpty then return ""
  let path := pathOps p
  let even := s.rule == .evenOdd
  let stroke := match s.stroke with
    | some c => if s.st.width > 0 then some c else none
    | none => none
  let mut out := ""
  -- a gradient fill: the shading painted with the path as the clip
  if let some g := s.fillPaint then
    if let some sh ← shadingName g then
      let a := match g with
        | .linear _ _ stops | .radial _ _ stops => stopsAlpha stops
        | .solid c => c.a.toNat.toFloat / 255
      let saved := (← get).gs
      let al ← setAlpha (s.fillOpacity * a) 1
      out := out ++ "q\n" ++ al ++ path ++ (if even then "W* n\n" else "W n\n") ++ s!"/{sh} sh\nQ\n"
      modify fun st => { st with gs := saved }
  let fill := if s.fillPaint.isSome then none else s.fill
  match fill, stroke with
  | none, none => return out
  | some f, none =>
    let al ← setAlpha (s.fillOpacity * f.a.toNat.toFloat / 255) 1
    let fc ← setFill f
    return out ++ al ++ fc ++ path ++ (if even then "f*\n" else "f\n")
  | none, some c =>
    let al ← setAlpha 1 (s.strokeOpacity * c.a.toNat.toFloat / 255)
    let sc ← setStroke c
    let lo ← setLine s.st
    return out ++ al ++ sc ++ lo ++ path ++ "S\n"
  | some f, some c =>
    let al ← setAlpha (s.fillOpacity * f.a.toNat.toFloat / 255)
      (s.strokeOpacity * c.a.toNat.toFloat / 255)
    let fc ← setFill f
    let sc ← setStroke c
    let lo ← setLine s.st
    return out ++ al ++ fc ++ sc ++ lo ++ path ++ (if even then "B*\n" else "B\n")

/-- The page's width and height in pixels, which a transparency group's bounding box is. -/
structure Frame where
  /-- The width in pixels. -/
  width : Float
  /-- The height in pixels. -/
  height : Float

/-- The content of nodes nested at most `fuel` deep (deeper ones are skipped), in the pixel
coordinates of the page; `clips` and `grads` are the clip paths and gradients by id. A group with
an `opacity` below 1 becomes a transparency group (a form drawn at that opacity); a group with a
`clip-path` is drawn inside `q … Q` with the clip. -/
def nodesOps (fr : Frame) (clips : Array (String × Path)) (grads : Array (String × Raster.Paint)) :
    Nat → Raster.Style → Array Node → StateM State String
  | 0, _, _ => pure ""
  | fuel + 1, s, nodes => do
    let mut out := ""
    for n in nodes do
      match n with
      | .text _ => pure ()
      | .element name attrs children =>
        let s := s.apply attrs
        let s := match Raster.attr? attrs "fill" with
          | some v =>
            if v.startsWith "url(#" then
              let id := ((v.dropPrefix "url(#").dropSuffix ")").toString
              { s with fill := some ⟨0, 0, 0, 255⟩,
                       fillPaint := (grads.find? (·.1 == id)).map (·.2) }
            else { s with fillPaint := none }
          | none => s
        match name with
        | "defs" | "clipPath" | "text" | "linearGradient" | "radialGradient" | "title" | "desc"
        | "metadata" => pure ()
        | "g" =>
          let clip := (Raster.attr? attrs "clip-path").bind fun v =>
            let id := ((v.dropPrefix "url(#").dropSuffix ")").toString
            (clips.find? (·.1 == id)).map (·.2)
          let opacity := ((Raster.attr? attrs "opacity").bind Raster.parseNumber?).getD 1
          let opacity := if opacity.isNaN then 1 else max 0 opacity
          -- one shape painted once (a fill or a stroke, not both, not a gradient) at a group
          -- opacity is that shape at the opacity times its own: no form is needed
          let single : Option (Path × Raster.Style) := match children with
            | #[.element cn ca _] =>
              let cs := s.apply ca
              let fills : Bool := cs.fill.isSome && !((Raster.attr? ca "fill").getD "").startsWith "url("
              let strokes : Bool := cs.stroke.isSome && decide (cs.st.width > (0 : Float))
              let painted : Bool := fills != strokes
              if clip.isNone && painted && cs.fillPaint.isNone && opacity < 1 then
                (Raster.shapeOf cn ca).map fun p =>
                  (p, { cs with fillOpacity := cs.fillOpacity * opacity,
                                strokeOpacity := cs.strokeOpacity * opacity })
              else none
            | _ => none
          if let some (p, cs) := single then
            out := out ++ (← shapeOps p cs)
          else if clip.isNone && opacity ≥ 1 then
            out := out ++ (← nodesOps fr clips grads fuel s children)
          else
            let saved := (← get).gs
            out := out ++ "q\n"
            if let some p := clip then
              out := out ++ pathOps p ++ "W n\n"
            if opacity < 1 then
              -- the children as a form of their own, painted at the group's opacity
              modify fun st => { st with gs := {} }
              let body ← nodesOps fr clips grads fuel s children
              let al ← (do
                modify fun st => { st with gs := saved }
                let n ← alphaName opacity opacity
                pure s!"/{n} gs\n")
              let form := streamBody #[("Type", .name "XObject"), ("Subtype", .name "Form"),
                ("BBox", .arr #[.int 0, .int 0, num fr.width, num fr.height]),
                ("Group", .dict #[("S", .name "Transparency"), ("CS", .name "DeviceRGB")]),
                ("Resources", .ref resourcesObject)] body.toUTF8
              let st ← get
              set { st with xobjects := st.xobjects.push form }
              out := out ++ al ++ s!"/X{st.xobjects.size} Do\n"
            else
              out := out ++ (← nodesOps fr clips grads fuel s children)
            out := out ++ "Q\n"
            modify fun st => { st with gs := saved }
        | _ =>
          match Raster.shapeOf name attrs with
          | none => pure ()
          | some p => out := out ++ (← shapeOps p s)
    return out

/-- The page of a picture: the catalog, the page tree with one page of `ptPerPx` times the size
in points, its resources (`ExtGState`, shadings, forms and images as collected), its content
(`content`, in the pixel coordinates of the page under the page's transformation) and the
`xobjects`, as a whole file (`document`). -/
def page (fr : Frame) (content : String) (st : State) : ByteArray :=
  let w := fr.width * ptPerPx
  let h := fr.height * ptPerPx
  let named := fun (pre : String) (xs : Array String) =>
    String.join (xs.toList.zipIdx.map fun (d, k) => s!" /{pre}{k} {d}")
  let xo := String.join ((List.range st.xobjects.size).map fun k =>
    s!" /X{k} {firstObject + k} 0 R")
  let resources := "<<" ++
    (if st.alphas.isEmpty then "" else " /ExtGState <<" ++ named "G" st.alphas ++ " >>") ++
    (if st.shadings.isEmpty then "" else " /Shading <<" ++ named "S" st.shadings ++ " >>") ++
    (if st.xobjects.isEmpty then "" else " /XObject <<" ++ xo ++ " >>") ++ " >>"
  let body := s!"q\n{fmtNum ptPerPx 3} 0 0 {fmtNum (-ptPerPx) 3} 0 {fmtNum h 3} cm\n" ++ content ++
    "Q\n"
  let catalog := (Obj.dict #[("Type", .name "Catalog"), ("Pages", .ref 2)]).write.toUTF8
  let pages := (Obj.dict #[("Type", .name "Pages"), ("Kids", .arr #[.ref 3]), ("Count", .int 1)]).write.toUTF8
  let pageObj := (Obj.dict #[("Type", .name "Page"), ("Parent", .ref 2),
    ("MediaBox", .arr #[.int 0, .int 0, num w, num h]), ("Resources", .ref resourcesObject),
    ("Contents", .ref 5),
    ("Group", .dict #[("S", .name "Transparency"), ("CS", .name "DeviceRGB")])]).write.toUTF8
  document (#[catalog, pages, pageObj, resources.toUTF8, streamBody #[] body.toUTF8] ++ st.xobjects) 1

/-- A one-page PDF of SVG nodes (the children of an `svg` root of `w × h` pixels), drawn as the
module docstring says, on a background `bg` (none when it is transparent). -/
def ofSvgNodes (w h : Float) (nodes : Array Node) (bg : Rgba := ⟨0, 0, 0, 0⟩) : ByteArray :=
  let fr : Frame := { width := w, height := h }
  let clips := nodes.foldl (fun acc n => acc ++ Raster.clipPaths 64 n) #[]
  let grads := nodes.foldl (fun acc n => acc ++ Raster.gradients 64 n) #[]
  let back := if bg.a == 0 then #[]
    else #[el "rect" (#[("x", "0"), ("y", "0"), ("width", fmtNum w), ("height", fmtNum h)] ++
      paint "fill" (some bg))]
  let (content, st) := (nodesOps fr clips grads 64 {} (back ++ nodes)).run {}
  page fr content st

/-- A one-page PDF of a raster image, one pixel to `ptPerPx` points: its samples as an image
`XObject` (`DeviceGray` or `DeviceRGB`, 8 bits, compressed with PILean's DEFLATE), its alpha as a
soft mask; `none` for an image without pixels or whose samples do not match its size. -/
def ofImage (im : Image) : Option ByteArray := do
  if im.width == 0 || im.height == 0 then none
  let ch := im.mode.channels
  if im.data.size != im.width * im.height * ch then none
  let n := im.width * im.height
  let (colour, alpha) : ByteArray × Option ByteArray := match im.mode with
    | .rgba => Id.run do
      let mut c := ByteArray.emptyWithCapacity (3 * n)
      let mut a := ByteArray.emptyWithCapacity n
      for i in [0:n] do
        c := ((c.push (Png.byteAt im.data (4 * i))).push (Png.byteAt im.data (4 * i + 1))).push
          (Png.byteAt im.data (4 * i + 2))
        a := a.push (Png.byteAt im.data (4 * i + 3))
      return (c, some a)
    | _ => (im.data, none)
  let space := if im.mode == .l then "DeviceGray" else "DeviceRGB"
  let base := fun (cs : String) => #[("Type", Obj.name "XObject"), ("Subtype", .name "Image"),
    ("Width", .int im.width), ("Height", .int im.height), ("ColorSpace", .name cs),
    ("BitsPerComponent", .int 8)]
  -- the soft mask is the object after the image
  let maskRef := match alpha with
    | some _ => #[("SMask", Obj.ref (firstObject + 1))]
    | none => #[]
  let img := streamBody (base space ++ maskRef) colour
  let mask := alpha.map (streamBody (base "DeviceGray"))
  let fr : Frame := { width := im.width.toFloat, height := im.height.toFloat }
  let content := s!"q\n{im.width} 0 0 -{im.height} 0 {im.height} cm\n/X0 Do\nQ\n"
  return page fr content { xobjects := #[img] ++ (match mask with | some m => #[m] | none => #[]) }

end PILean.Pdf
