/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Path
import PILean.Color

/-!
# SVG output

A small typed model of SVG documents and its writer. The output is deterministic: attributes come
in the order the constructors give them, numbers are written with a fixed number of decimals and
no exponent, elements are indented two spaces a level. All text and attribute values are
treated as untrusted and escaped; characters XML 1.0 cannot carry are dropped; element and
attribute names are checked, and a node with an invalid name is left out.

## Main definitions

* `fmtNum`: a `Float` as SVG number text.
* `escapeText`, `escapeAttr`: XML escaping.
* `Svg.Node`, `Svg.render`, `Svg.document`: the model and the writer.
* `Svg.pathData`: a `Path` as path data.
* `Svg.rect`, `Svg.line`, `Svg.path`, `Svg.text`, `Svg.group`, `Svg.paint`: element builders.

## References

* Scalable Vector Graphics (SVG) 1.1 (Second Edition), W3C Recommendation 16 August 2011.
* Extensible Markup Language (XML) 1.0 (Fifth Edition), section 2.2 "Characters".
-/

namespace PILean

/-- `x` rounded to `decimals` decimals as text: no exponent, no trailing zeros, no `-0`;
magnitudes beyond 10¹² are clamped to ±10¹², and a non-finite value is written `0`. -/
def fmtNum (x : Float) (decimals : Nat := 3) : String :=
  if x.isNaN || x.isInf then "0"
  else
    let lim : Float := 1e12
    let y := if x > lim then lim else if x < -lim then -lim else x
    let scale := (10 : Float) ^ decimals.toFloat
    let n : Nat := (y.abs * scale).round.toUInt64.toNat
    let p := 10 ^ decimals
    let whole := n / p
    let frac := n % p
    let fd := Nat.toDigits 10 frac
    let padded := List.replicate (decimals - fd.length) '0' ++ fd
    let trimmed := (padded.reverse.dropWhile (· == '0')).reverse
    let body := toString whole ++ (if trimmed.isEmpty then "" else "." ++ String.ofList trimmed)
    if n == 0 then "0" else (if y < 0 then "-" else "") ++ body

/-- Whether XML 1.0 can carry the character (tab, line feed, carriage return, and the ranges
from U+0020 except U+FFFE and U+FFFF). -/
def xmlChar (c : Char) : Bool :=
  c == '\t' || c == '\n' || c == '\r' || (c.val ≥ 0x20 && c.val != 0xFFFE && c.val != 0xFFFF)

/-- Text content escaped for XML: `&`, `<`, `>` as entities; other characters XML cannot carry
dropped. -/
def escapeText (s : String) : String :=
  s.foldl (init := "") fun out c =>
    if c == '&' then out ++ "&amp;" else if c == '<' then out ++ "&lt;"
    else if c == '>' then out ++ "&gt;" else if xmlChar c then out.push c else out

/-- An attribute value escaped for a double-quoted XML attribute: as `escapeText`, and `"`,
`'`, tab, line feed and carriage return as character references (so that they survive
attribute-value normalisation). -/
def escapeAttr (s : String) : String :=
  s.foldl (init := "") fun out c =>
    if c == '&' then out ++ "&amp;" else if c == '<' then out ++ "&lt;"
    else if c == '>' then out ++ "&gt;" else if c == '"' then out ++ "&quot;"
    else if c == '\'' then out ++ "&#39;" else if c == '\t' then out ++ "&#9;"
    else if c == '\n' then out ++ "&#10;" else if c == '\r' then out ++ "&#13;"
    else if xmlChar c then out.push c else out

/-- Whether `s` is a name this writer emits: an ASCII letter or `_` first, then ASCII letters,
digits, `-`, `_`, `.` or `:` (a subset of XML's names). -/
def validName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c.isAlpha || c == '_') &&
      cs.all fun d => d.isAlphanum || d == '-' || d == '_' || d == '.' || d == ':'

namespace Svg

/-- A node of an SVG document. -/
inductive Node where
  /-- An element: its name, attributes in output order, and children. -/
  | element (name : String) (attrs : Array (String × String)) (children : Array Node)
  /-- Character data. -/
  | text (content : String)
  deriving Inhabited, Repr

/-- The node as XML at indentation `indent`: an element whose children are all elements is laid
out one child a line; one with character data stays on one line. Attributes with invalid names
are left out, and so is an element with an invalid name. -/
def render (indent : Nat := 0) : Node → String
  | .text s => escapeText s
  | .element name attrs children =>
    if !validName name then ""
    else
      let pad := String.ofList (List.replicate indent ' ')
      let as := attrs.foldl (init := "") fun acc (k, v) =>
        if validName k then acc ++ " " ++ k ++ "=\"" ++ escapeAttr v ++ "\"" else acc
      if children.isEmpty then pad ++ "<" ++ name ++ as ++ "/>"
      else if children.all (fun c => match c with | .element .. => true | .text _ => false) then
        let inner := children.map (render (indent + 2))
        pad ++ "<" ++ name ++ as ++ ">\n" ++
          String.join (inner.toList.filter (!·.isEmpty) |>.map (· ++ "\n")) ++
          pad ++ "</" ++ name ++ ">"
      else
        let inner := children.map (render 0)
        pad ++ "<" ++ name ++ as ++ ">" ++ String.join inner.toList ++ "</" ++ name ++ ">"

/-- An element. -/
def el (name : String) (attrs : Array (String × String)) (children : Array Node := #[]) :
    Node :=
  .element name attrs children

/-- A whole SVG document of `width × height` user units, with an XML declaration, the SVG
namespace and a view box from the origin, ending in a line feed. -/
def document (width height : Float) (children : Array Node) : String :=
  let root := el "svg" #[("xmlns", "http://www.w3.org/2000/svg"), ("width", fmtNum width),
    ("height", fmtNum height), ("viewBox", s!"0 0 {fmtNum width} {fmtNum height}")] children
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++ render 0 root ++ "\n"

/-- A path as SVG path data with absolute commands, coordinates to `decimals` decimals:
`M x y`, `L x y`, `Q cx cy x y`, `C c1x c1y c2x c2y x y`, `Z`, separated by spaces. -/
def pathData (p : Path) (decimals : Nat := 2) : String :=
  let f := fun (x : Float) => fmtNum x decimals
  let pt := fun (q : Point) => f q.x ++ " " ++ f q.y
  " ".intercalate (p.cmds.toList.map fun
    | .move q => "M" ++ pt q
    | .line q => "L" ++ pt q
    | .quad c q => "Q" ++ pt c ++ " " ++ pt q
    | .cubic a b q => "C" ++ pt a ++ " " ++ pt b ++ " " ++ pt q
    | .close => "Z")

/-- A colour as `#rrggbb` (`Rgba.rgbHex`). -/
def rgbHex (c : Rgba) : String := c.rgbHex

/-- The attributes painting with a colour: `key` (`fill` or `stroke`) as `#rrggbb`, and
`key-opacity` when the colour is not opaque. `none` paints nothing. -/
def paint (key : String) : Option Rgba → Array (String × String)
  | none => #[(key, "none")]
  | some c =>
    if c.a == 255 then #[(key, rgbHex c)]
    else #[(key, rgbHex c), (key ++ "-opacity", fmtNum (c.a.toNat.toFloat / 255) 3)]

/-- A rectangle with top-left corner `(x, y)`. -/
def rect (x y w h : Float) (fill : Option Rgba) (extra : Array (String × String) := #[]) :
    Node :=
  el "rect" (#[("x", fmtNum x), ("y", fmtNum y), ("width", fmtNum w), ("height", fmtNum h)] ++
    paint "fill" fill ++ extra)

/-- A line segment stroked with a colour and width. -/
def line (a b : Point) (stroke : Rgba) (width : Float)
    (extra : Array (String × String) := #[]) : Node :=
  el "line" (#[("x1", fmtNum a.x), ("y1", fmtNum a.y), ("x2", fmtNum b.x), ("y2", fmtNum b.y)] ++
    paint "stroke" (some stroke) ++ #[("stroke-width", fmtNum width)] ++ extra)

/-- A path element with its fill and stroke. -/
def path (p : Path) (fill stroke : Option Rgba) (width : Float := 1)
    (extra : Array (String × String) := #[]) : Node :=
  el "path" (#[("d", pathData p)] ++ paint "fill" fill ++ paint "stroke" stroke ++
    (if stroke.isSome then #[("stroke-width", fmtNum width)] else #[]) ++ extra)

/-- How text is anchored at its position. -/
inductive Anchor where
  /-- The start of the text at the point. -/
  | start
  /-- The middle of the text at the point. -/
  | middle
  /-- The end of the text at the point. -/
  | finish
  deriving BEq, Inhabited, Repr

/-- The anchor's `text-anchor` value. -/
def Anchor.name : Anchor → String
  | .start => "start" | .middle => "middle" | .finish => "end"

/-- A line of text with its baseline at `(x, y)`. -/
def text (x y : Float) (content : String) (size : Float) (fill : Rgba) (anchor : Anchor)
    (extra : Array (String × String) := #[]) : Node :=
  el "text" (#[("x", fmtNum x), ("y", fmtNum y), ("font-size", fmtNum size)] ++
    paint "fill" (some fill) ++ #[("text-anchor", anchor.name)] ++ extra) #[.text content]

/-- A group of nodes with shared attributes. -/
def group (attrs : Array (String × String)) (children : Array Node) : Node :=
  el "g" attrs children

end Svg

end PILean
