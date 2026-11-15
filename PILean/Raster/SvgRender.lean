/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Svg
import PILean.Raster.Draw

/-!
# SVG documents rasterised

PILean's SVG model (`PILean.Svg.Node`) drawn by the rasteriser, so that one description of a
picture gives both its SVG and its PNG: the same shapes, paints, strokes and clips.

What is drawn, as SVG 1.1 specifies it: `g` (its presentation attributes inherited, its
`opacity` as a group opacity, its `clip-path` through a clip mask), `rect` (with `rx`), `line`,
`circle`, `ellipse`, `polyline`, `polygon`, `path` (the commands `M L H V Q C Z` and their
relative forms), `clipPath` in `defs`; the attributes `fill`, `stroke` (`#rgb`, `#rrggbb` or
`none`), `fill-opacity`, `stroke-opacity`, `stroke-width`, `stroke-linecap`,
`stroke-linejoin`, `stroke-miterlimit`, `stroke-dasharray`, `stroke-dashoffset`, `fill-rule`.

Not drawn: `text` (a text layer is not part of PILean yet), images, gradients given as SVG
elements (gradients are drawn through `Paint`), `transform`, `use`, filters, markers, CSS. An
element the renderer does not know is skipped, as is malformed data (a path's data is read up
to its first error, as SVG does).

## Main definitions

* `parseNumber?`, `parsePathData`: SVG numbers and path data.
* `Svg.rasterize`: nodes drawn on a drawing of a given size.
-/

namespace PILean.Raster

open PILean.Svg

/-- An SVG number (`-12.5`, `.5`, `3`; an exponent is accepted), or `none`. -/
def parseNumber? (s : String) : Option Float := Id.run do
  let cs := s.trimAscii.toString.toList
  let (neg, cs) := match cs with
    | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)
  let whole := cs.takeWhile Char.isDigit
  let rest := cs.drop whole.length
  let (frac, rest) := match rest with
    | '.' :: r => (r.takeWhile Char.isDigit, r.drop (r.takeWhile Char.isDigit).length)
    | r => ([], r)
  if whole.isEmpty && frac.isEmpty then return none
  let (ex, rest) := match rest with
    | e :: r =>
      if e == 'e' || e == 'E' then
        let (eneg, r) := match r with
          | '-' :: q => (true, q) | '+' :: q => (false, q) | q => (false, q)
        let ds := r.takeWhile Char.isDigit
        let v : Nat := ds.foldl (fun (a : Nat) (d : Char) => a * 10 + (d.toNat - 48)) 0
        if ds.isEmpty then (none, rest)
        else (some (if eneg then -(v : Int) else (v : Int)), r.drop ds.length)
      else (some 0, rest)
    | [] => (some 0, [])
  let some ex := ex | return none
  if !rest.isEmpty then return none
  let digits := whole ++ frac
  let m : Nat := (digits.take 17).foldl (fun (a : Nat) (d : Char) => a * 10 + (d.toNat - 48)) 0
  let e : Int := ex - frac.length + (if digits.length > 17 then (digits.length - 17 : Nat) else 0)
  let e := max (-400) (min 400 e)
  let v := if e ≥ 0 then m.toFloat * (10 : Float) ^ e.toNat.toFloat
    else m.toFloat / (10 : Float) ^ e.natAbs.toFloat
  return some (if neg then -v else v)

/-- The tokens of path data: command letters and numbers. -/
def pathTokens (d : String) : Array (Sum Char Float) := Id.run do
  let cs := d.toList.toArray
  let mut out := #[]
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    let c := cs[i]?.getD ' '
    if c.isAlpha && c != 'e' && c != 'E' then out := out.push (.inl c); i := i + 1
    else if c.isDigit || c == '-' || c == '+' || c == '.' then
      -- a number: sign, digits, one point, an exponent
      let mut j := i + 1
      let mut dot := c == '.'
      for _ in [i:cs.size] do
        let d := cs[j]?.getD ' '
        if d.isDigit then j := j + 1
        else if d == '.' && !dot then dot := true; j := j + 1
        else if (d == 'e' || d == 'E') && j + 1 < cs.size then
          let n := cs[j + 1]?.getD ' '
          if n.isDigit || n == '-' || n == '+' then j := j + 2 else break
        else break
      match parseNumber? (String.ofList (cs.extract i j).toList) with
      | some v => out := out.push (.inr v)
      | none => return out
      i := j
    else i := i + 1
  return out

/-- SVG path data as a path (`M L H V Q C Z`, absolute and relative), read up to the first
error. -/
def parsePathData (d : String) : Path := Id.run do
  let toks := pathTokens d
  let mut p := Path.empty
  let mut cmd := 'M'
  let mut cur : Point := ⟨0, 0⟩
  let mut start : Point := ⟨0, 0⟩
  let mut i := 0
  let num := fun (k : Nat) => match toks[k]? with | some (.inr v) => some v | _ => none
  for _ in [0:toks.size + 1] do
    if i ≥ toks.size then break
    if let some (.inl c) := toks[i]? then
      cmd := c; i := i + 1
      if c == 'Z' || c == 'z' then p := p.close; cur := start
      continue
    let rel := cmd.isLower
    let base := if rel then cur else ⟨0, 0⟩
    let pt := fun (k : Nat) => match num k, num (k + 1) with
      | some x, some y => some (⟨base.x + x, base.y + y⟩ : Point)
      | _, _ => none
    match cmd.toUpper with
    | 'M' =>
      let some q := pt i | return p
      p := p.moveTo q; cur := q; start := q; i := i + 2
      cmd := if rel then 'l' else 'L'
    | 'L' =>
      let some q := pt i | return p
      p := p.lineTo q; cur := q; i := i + 2
    | 'H' =>
      let some x := num i | return p
      cur := ⟨(if rel then cur.x else 0) + x, cur.y⟩; p := p.lineTo cur; i := i + 1
    | 'V' =>
      let some y := num i | return p
      cur := ⟨cur.x, (if rel then cur.y else 0) + y⟩; p := p.lineTo cur; i := i + 1
    | 'Q' =>
      let (some c, some q) := (pt i, pt (i + 2)) | return p
      p := p.quadTo c q; cur := q; i := i + 4
    | 'C' =>
      let (some c1, some c2, some q) := (pt i, pt (i + 2), pt (i + 4)) | return p
      p := p.cubicTo c1 c2 q; cur := q; i := i + 6
    | _ => return p
  return p

/-- The inherited presentation state. -/
structure Style where
  /-- The fill colour, `none` for no fill. -/
  fill : Option Rgba := some ⟨0, 0, 0, 255⟩
  /-- The stroke colour. -/
  stroke : Option Rgba := none
  /-- `fill-opacity`. -/
  fillOpacity : Float := 1
  /-- `stroke-opacity`. -/
  strokeOpacity : Float := 1
  /-- The stroke's style. -/
  st : Stroke := {}
  /-- `fill-rule`. -/
  rule : FillRule := .nonZero
  deriving Inhabited

/-- An attribute's value. -/
def attr? (attrs : Array (String × String)) (k : String) : Option String :=
  (attrs.find? (·.1 == k)).map (·.2)

/-- A colour value: `none`, `#rgb` or `#rrggbb`. -/
def colorValue? (v : String) : Option (Option Rgba) :=
  if v == "none" then some none else (Rgba.ofHex? v).map some

/-- The style with an element's presentation attributes applied. -/
def Style.apply (s : Style) (attrs : Array (String × String)) : Style := Id.run do
  let mut s := s
  let num := fun (k : String) => (attr? attrs k).bind parseNumber?
  if let some v := (attr? attrs "fill").bind colorValue? then s := { s with fill := v }
  if let some v := (attr? attrs "stroke").bind colorValue? then s := { s with stroke := v }
  if let some v := num "fill-opacity" then s := { s with fillOpacity := v }
  if let some v := num "stroke-opacity" then s := { s with strokeOpacity := v }
  if let some v := num "stroke-width" then s := { s with st := { s.st with width := v } }
  if let some v := num "stroke-miterlimit" then
    s := { s with st := { s.st with miterLimit := v } }
  if let some v := num "stroke-dashoffset" then
    s := { s with st := { s.st with dashOffset := v } }
  match attr? attrs "stroke-linecap" with
  | some "round" => s := { s with st := { s.st with cap := .round } }
  | some "square" => s := { s with st := { s.st with cap := .square } }
  | some "butt" => s := { s with st := { s.st with cap := .butt } }
  | _ => pure ()
  match attr? attrs "stroke-linejoin" with
  | some "round" => s := { s with st := { s.st with join := .round } }
  | some "bevel" => s := { s with st := { s.st with join := .bevel } }
  | some "miter" => s := { s with st := { s.st with join := .miter } }
  | _ => pure ()
  match attr? attrs "fill-rule" with
  | some "evenodd" => s := { s with rule := .evenOdd }
  | some "nonzero" => s := { s with rule := .nonZero }
  | _ => pure ()
  if let some v := attr? attrs "stroke-dasharray" then
    let parts := (v.split (fun c => c == ',' || c == ' ')).toList.map (·.toString)
      |>.filter (!·.isEmpty)
    let ds := parts.filterMap parseNumber?
    s := { s with st := { s.st with dash := if v == "none" then #[] else ds.toArray } }
  return s

/-- An element's shape as a path, if it is a shape. -/
def shapeOf (name : String) (attrs : Array (String × String)) : Option Path :=
  let n := fun (k : String) => ((attr? attrs k).bind parseNumber?).getD 0
  let pts := fun (k : String) =>
    let vs := ((attr? attrs k).getD "").split (fun c => c == ',' || c == ' ')
      |>.toList.filterMap (fun t => parseNumber? t.toString)
    (List.range (vs.length / 2)).toArray.map fun i =>
      (⟨vs[2 * i]?.getD 0, vs[2 * i + 1]?.getD 0⟩ : Point)
  match name with
  | "rect" =>
    let (x, y, w, h) := (n "x", n "y", n "width", n "height")
    if w ≤ 0 || h ≤ 0 then none
    else
      let rx := n "rx"
      let ry := ((attr? attrs "ry").bind parseNumber?).getD rx
      if rx > 0 || ry > 0 then some (Draw.roundedRectPath x y (x + w) (y + h) (max rx ry))
      else some (Path.rect x y w h)
  | "line" => some (Path.polyline #[⟨n "x1", n "y1"⟩, ⟨n "x2", n "y2"⟩])
  | "circle" => some (Path.ellipse ⟨n "cx", n "cy"⟩ (n "r") (n "r"))
  | "ellipse" => some (Path.ellipse ⟨n "cx", n "cy"⟩ (n "rx") (n "ry"))
  | "polyline" => some (Path.polyline (pts "points"))
  | "polygon" => some (Path.polyline (pts "points")).close
  | "path" => some (parsePathData ((attr? attrs "d").getD ""))
  | _ => none

/-- The clip paths defined in a node, by id: the union of their shapes; nodes nested more than
`fuel` deep are not searched. -/
def clipPaths (fuel : Nat) (n : Node) : Array (String × Path) :=
  match fuel, n with
  | 0, _ => #[]
  | _ + 1, .element "clipPath" attrs children =>
    match attr? attrs "id" with
    | some id => #[(id, children.foldl (fun p c => match c with
        | .element name as _ => (shapeOf name as).map p.append |>.getD p
        | _ => p) Path.empty)]
    | none => #[]
  | fuel + 1, .element _ _ children => children.foldl (fun acc c => acc ++ clipPaths fuel c) #[]
  | _ + 1, .text _ => #[]

/-- Draws nodes nested at most `fuel` deep (deeper ones are skipped). -/
def drawNodes (clips : Array (String × Path)) (fuel : Nat) (d : Draw) (s : Style)
    (nodes : Array Node) : Draw :=
  match fuel with
  | 0 => d
  | fuel + 1 => nodes.foldl (init := d) fun d n =>
    match n with
    | .text _ => d
    | .element name attrs children =>
      let s := s.apply attrs
      match name with
      | "defs" | "clipPath" | "text" => d
      | "g" =>
        let clip := (attr? attrs "clip-path").bind fun v =>
          let id := ((v.dropPrefix "url(#").dropSuffix ")").toString
          (clips.find? (·.1 == id)).map (·.2)
        let opacity := ((attr? attrs "opacity").bind parseNumber?).getD 1
        let saved := d.mask
        let d := match clip with | some p => d.withClipPath p | none => d
        let d := if opacity < 1 then
            d.group opacity fun g => drawNodes clips fuel g s children
          else drawNodes clips fuel d s children
        { d with mask := saved }
      | _ =>
        match shapeOf name attrs with
        | none => d
        | some p =>
          let d := match s.fill with
            | some c => d.fill p (.solid c) s.rule s.fillOpacity
            | none => d
          match s.stroke with
          | some c => if s.st.width > 0 then d.stroke p s.st (.solid c) s.strokeOpacity else d
          | none => d

/-- SVG nodes (the children of an `svg` root) drawn on a drawing of `w × h` pixels with a
transparent background, as the SVG renderer draws them (see the module docstring). -/
def Svg.rasterize (w h : Nat) (nodes : Array Node)
    (bg : Rgba := ⟨0, 0, 0, 0⟩) : Draw :=
  let clips := nodes.foldl (fun acc n => acc ++ clipPaths 64 n) #[]
  drawNodes clips 64 (Draw.new w h bg) {} nodes

end PILean.Raster
