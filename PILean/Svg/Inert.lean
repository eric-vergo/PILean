/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# Inert SVG

`Svg.isInert` answers whether an SVG document can be shown in a web page without running
script, loading anything from outside the document, or carrying event handlers. It is a small
bounded scanner over the bytes of the text, not an XML parser, and it is strict: it accepts the
SVG that PILean writes (figures, graphs, animations, and documents carrying a source record) and
refuses everything else that could be active.

The rules, in short:

* the input is at most 64 MiB, and the work is linear in its size;
* the only markup is one leading `<?xml ...?>` declaration, comments, and elements from a fixed
  list (`Svg.inertElements`); a document type, entity, CDATA section or other processing
  instruction is refused;
* attributes have plain names and quoted values; event handlers, `style` attributes, `xml:base`
  and links to anything but a fragment (`#id`) are refused, as are `url(` references to anything
  but a fragment, and `javascript:` and `data:` in any value;
* the values are decoded (the five XML entities and numeric character references) before they
  are checked, and any other entity is refused;
* `<style>` text may not import, load, escape or compute anything;
* elements are properly nested (at most 256 deep) and there is exactly one root, `svg`.

## Main definitions

* `Svg.inertProblem?`: the first reason a document is not inert, if there is one.
* `Svg.isInert`: whether there is none.
-/

namespace PILean.Svg

/-- The largest document, in bytes, that `isInert` examines. -/
def maxInertSize : Nat := 64 * 1024 * 1024

/-- The largest nesting depth of elements that `isInert` accepts. -/
def maxInertDepth : Nat := 256

/-- The element names `isInert` accepts (case-sensitive). -/
def inertElements : List String :=
  ["svg", "g", "path", "rect", "circle", "ellipse", "line", "polyline", "polygon", "text",
    "tspan", "title", "desc", "metadata", "pilean:source", "defs", "clipPath",
    "linearGradient", "radialGradient", "stop", "animate", "animateTransform", "set", "style"]

namespace Inert

/-- A scan either succeeds or fails with the reason. -/
abbrev Scan := Except String

/-- The byte at `i`, or `0` past the end. -/
def byteAt (d : ByteArray) (i : Nat) : UInt8 := if h : i < d.size then d[i] else 0

/-- The bytes of an ASCII string. -/
def bytes (s : String) : ByteArray := s.toUTF8

/-- The string whose characters are the bytes of `b` (used for ASCII names only). -/
def ascii (b : ByteArray) : String := b.foldl (fun s x => s.push (Char.ofNat x.toNat)) ""

/-- White space of XML. -/
def isWs (b : UInt8) : Bool := b == 32 || b == 9 || b == 10 || b == 13

/-- A byte allowed in an element or attribute name. -/
def isNameByte (b : UInt8) : Bool :=
  (48 ≤ b && b ≤ 57) || (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122) ||
    b == 45 || b == 95 || b == 58 || b == 46

/-- The byte with ASCII capitals made small. -/
def lower (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- The first position at or after `i` whose byte fails `p` (the size if there is none). -/
def scanWhile (d : ByteArray) (p : UInt8 → Bool) (i : Nat) : Nat := Id.run do
  for j in [i:d.size] do
    if !p (byteAt d j) then return j
  return max i d.size

/-- Whether `d` has the bytes `pat` at position `i`. -/
def startsAt (d pat : ByteArray) (i : Nat) : Bool := Id.run do
  if i + pat.size > d.size then return false
  for k in [0:pat.size] do
    if byteAt d (i + k) != byteAt pat k then return false
  return true

/-- The first position at or after `i` where `d` has the bytes `pat`. -/
def findPat (d pat : ByteArray) (i : Nat) : Option Nat := Id.run do
  for j in [i:d.size] do
    if startsAt d pat j then return some j
  return none

/-- Whether `d` contains the text `pat`. -/
def has (d : ByteArray) (pat : String) : Bool := (findPat d (bytes pat) 0).isSome

/-- Whether the byte `b` occurs in `d`. -/
def hasByte (d : ByteArray) (b : UInt8) : Bool := d.foldl (fun r x => r || x == b) false

/-- The bytes of `d` with ASCII capitals made small. -/
def lowered (d : ByteArray) : ByteArray := d.foldl (fun r x => r.push (lower x)) ByteArray.empty

/-- Every `url(` of `d` (already in lower case) is followed by `#`, after optional spaces and an
optional quote: references go to fragments of the document only. -/
def urlsAreLocal (d : ByteArray) : Bool := Id.run do
  let pat := bytes "url("
  for j in [0:d.size] do
    if startsAt d pat j then
      let k := scanWhile d (· ≤ 32) (j + 4)
      let k := if byteAt d k == 34 || byteAt d k == 39 then k + 1 else k
      if byteAt d k != 35 then return false
  return true

/-- The value of a numeric character reference or an entity name (the text between `&` and
`;`): an ASCII byte, or `128` for any other character, which no check looks for. -/
def entityByte (name : String) : Scan UInt8 := do
  let num (digits : String) (base : Nat) : Scan UInt8 := do
    let mut v := 0
    for c in digits.toList do
      let some x := if c.isDigit then some (c.toNat - 48)
        else if base == 16 && 'a' ≤ c.toLower && c.toLower ≤ 'f' then
          some (c.toLower.toNat - 87)
        else none
        | throw "malformed character reference"
      v := v * base + x
    if digits.isEmpty || v == 0 || v > 0x10FFFF then throw "invalid character reference"
    return if v < 128 then v.toUInt8 else 128
  match name with
  | "amp" => return 38
  | "lt" => return 60
  | "gt" => return 62
  | "quot" => return 34
  | "apos" => return 39
  | _ =>
    if name.startsWith "#x" then num (name.drop 2).toString 16
    else if name.startsWith "#" then num (name.drop 1).toString 10
    else throw s!"entity &{name.take 20};"

/-- The value of an attribute with the five entities and the numeric references decoded; a raw
`<` and any other entity are refused. A reference to a character outside ASCII becomes the byte
`128`. -/
def decodeValue (raw : ByteArray) : Scan ByteArray := do
  let mut out := ByteArray.empty
  let mut j := 0
  for _ in [0:raw.size + 1] do
    if j ≥ raw.size then return out
    let c := byteAt raw j
    if c == 60 then throw "a raw < in an attribute value"
    else if c == 38 then
      let stop := min raw.size (j + 12)
      let some e := (List.range (stop - j - 1)).find? (fun k => byteAt raw (j + 1 + k) == 59)
        | throw "an & without ; in an attribute value"
      out := out.push (← entityByte (ascii (raw.extract (j + 1) (j + 1 + e))))
      j := j + e + 2
    else
      out := out.push c
      j := j + 1
  throw "internal error"

/-- Checks one attribute: `name` as written, `value` decoded. -/
def checkAttribute (name : String) (value : ByteArray) : Scan Unit := do
  let n := name.toLower
  let shown := name.take 40
  if n.startsWith "on" then throw s!"the event handler {shown}"
  if n == "style" then throw "a style attribute"
  if n == "xml:base" then throw "xml:base"
  if (n == "href" || n.endsWith ":href") && byteAt value 0 != 35 then
    throw s!"a link to something other than a fragment ({shown})"
  let lv := lowered value
  let compact := lv.foldl (fun r x => if x > 32 then r.push x else r) ByteArray.empty
  if has compact "javascript:" then throw s!"javascript: in {shown}"
  if has compact "data:" then throw s!"data: in {shown}"
  if hasByte lv 92 then throw s!"a backslash in {shown}"
  if !urlsAreLocal lv then throw s!"a url( to something other than a fragment in {shown}"
  for w in ["image(", "image-set(", "cross-fade(", "src("] do
    if has compact w then throw s!"{w} in {shown}"

/-- Checks the text of a `style` element. -/
def checkStyleText (css : ByteArray) : Scan Unit := do
  let l := lowered css
  if hasByte l 92 then throw "a backslash in a style element"
  if hasByte l 38 then throw "a character reference in a style element"
  for w in ["@import", "@font-face", "expression", "javascript:", "image(", "image-set(",
      "cross-fade(", "src(", "binding", "behavior"] do
    if has l w then throw s!"{w} in a style element"
  if !urlsAreLocal l then throw "a url( to something other than a fragment in a style element"

/-- Whether an `attributeName` value names an attribute that is a link or an event handler. -/
def activeAttributeName (value : ByteArray) : Bool :=
  let n := ascii (lowered (value.foldl (fun r x => if x > 32 then r.push x else r)
    ByteArray.empty))
  n == "href" || n.endsWith ":href" || n.startsWith "on"

/-- Scans the attributes of a start tag whose name (already read and allowed) ends at `i`.
Returns the position after the tag and whether it is self-closing. -/
def scanAttributes (d : ByteArray) (name : String) (i : Nat) : Scan (Nat × Bool) := do
  let animates := name == "animate" || name == "set" || name == "animateTransform"
  let mut j := i
  for _ in [0:d.size + 1] do
    let k := scanWhile d isWs j
    if k ≥ d.size then throw "an unterminated tag"
    if byteAt d k == 62 then return (k + 1, false)
    if byteAt d k == 47 then
      if byteAt d (k + 1) == 62 then return (k + 2, true)
      throw "a / inside a tag"
    if k == j then throw "a missing space between attributes"
    let ne := scanWhile d isNameByte k
    if ne == k then throw "a malformed attribute name"
    let aname := ascii (d.extract k ne)
    let eq := scanWhile d isWs ne
    if byteAt d eq != 61 then throw s!"the attribute {aname.take 40} has no value"
    let q := scanWhile d isWs (eq + 1)
    if byteAt d q != 34 && byteAt d q != 39 then
      throw s!"the value of {aname.take 40} is not quoted"
    let ve := scanWhile d (· != byteAt d q) (q + 1)
    if ve ≥ d.size then throw "an unterminated attribute value"
    let value ← decodeValue (d.extract (q + 1) ve)
    checkAttribute aname value
    if animates && aname.toLower == "attributename" && activeAttributeName value then
      throw s!"an animation of the link or event handler {(ascii value).take 40}"
    j := ve + 1
  throw "internal error"

/-- The state of the scan: the position, the names of the open elements and the stage of the
root element (`0` not yet seen, `1` open, `2` closed). -/
structure State where
  /-- The position of the next byte. -/
  pos : Nat := 0
  /-- The open elements, outermost first. -/
  stack : Array String := #[]
  /-- `0` before the root element, `1` inside it, `2` after it. -/
  root : Nat := 0

/-- One step of the scan: a run of text, a comment, a declaration, an end tag or a start tag
(with the body of a `style` element). -/
def step (d : ByteArray) (s : State) : Scan State := do
  let i := s.pos
  if byteAt d i != 60 then
    if s.stack.isEmpty then
      let j := scanWhile d isWs i
      if j < d.size && byteAt d j != 60 then throw "text outside the root element"
      return { s with pos := j }
    return { s with pos := scanWhile d (· != 60) i }
  let c := byteAt d (i + 1)
  if c == 63 then
    if i == 0 && startsAt d (bytes "<?xml") 0 && isWs (byteAt d 5) then
      let some e := findPat d (bytes "?>") 2 | throw "an unterminated XML declaration"
      let inner := d.extract 2 e
      if hasByte inner 62 || hasByte inner 60 then throw "a < or > inside the XML declaration"
      return { s with pos := e + 2 }
    throw "a processing instruction"
  else if c == 33 then
    if startsAt d (bytes "<!--") i then
      let some e := findPat d (bytes "-->") (i + 4) | throw "an unterminated comment"
      let inner := d.extract (i + 4) e
      if has inner "--" || byteAt inner 0 == 62 || startsAt inner (bytes "->") 0 ||
          (inner.size > 0 && byteAt inner (inner.size - 1) == 45) then
        throw "a comment with -- inside, or one that starts with > or -> or ends with -"
      return { s with pos := e + 3 }
    throw "a declaration (document type, entity or CDATA section)"
  else if c == 47 then
    let ne := scanWhile d isNameByte (i + 2)
    let k := scanWhile d isWs ne
    if byteAt d k != 62 then throw "a malformed end tag"
    let name := ascii (d.extract (i + 2) ne)
    match s.stack.back? with
    | none => throw "an end tag without a start tag"
    | some top =>
      if top != name then throw s!"the end tag </{name.take 40}> does not match <{top}>"
      let stack := s.stack.pop
      return { pos := k + 1, stack, root := if stack.isEmpty then 2 else s.root }
  else
    let ne := scanWhile d isNameByte (i + 1)
    let name := ascii (d.extract (i + 1) ne)
    if !inertElements.contains name then throw s!"the element <{name.take 40}>"
    if s.stack.isEmpty && (name != "svg" || s.root != 0) then
      throw "a root element other than a single <svg>"
    let (j, selfClosed) ← scanAttributes d name ne
    if selfClosed then
      return { s with pos := j, root := if s.stack.isEmpty then 2 else s.root }
    if name == "style" then
      let e := scanWhile d (· != 60) j
      if e ≥ d.size then throw "an unterminated style element"
      checkStyleText (d.extract j e)
      if !startsAt d (bytes "</style>") e then throw "markup inside a style element"
      return { s with pos := e + 8 }
    if s.stack.size ≥ maxInertDepth then throw "elements nested too deeply"
    return { pos := j, stack := s.stack.push name, root := if s.stack.isEmpty then 1 else s.root }

/-- Scans a whole document. -/
def scanDocument (d : ByteArray) : Scan Unit := do
  let mut s : State := {}
  for _ in [0:d.size + 1] do
    if s.pos ≥ d.size then
      if !s.stack.isEmpty then throw "an element is not closed"
      if s.root != 2 then throw "no root element"
      return
    s ← step d s
  throw "internal error"

end Inert

/-- The first reason the SVG text is not inert, or `none` if it is (see `isInert`). -/
def inertProblem? (svg : String) : Option String :=
  if svg.utf8ByteSize > maxInertSize then some "the document is larger than 64 MiB"
  else
    match Inert.scanDocument svg.toUTF8 with
    | .ok _ => none
    | .error m => some m

/-- Whether an SVG document can be shown in a web page without running script, loading anything
from outside the document, or carrying event handlers. It accepts the SVG that PILean writes and
refuses everything else that could be active: only the elements of `inertElements`, plain
attributes, no event handlers, no link or `url(` to anything but a fragment of the document, no
`javascript:` or `data:` value, a safe `<style>` text, proper nesting up to `maxInertDepth` and one
`svg` root. Documents above `maxInertSize` bytes are refused without being read. This is a
bounded scan over the text, not an XML parser. -/
def isInert (svg : String) : Bool := (inertProblem? svg).isNone

end PILean.Svg
