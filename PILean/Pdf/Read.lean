/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Png.Tables

/-!
# Reading PDF files

A bounded reader of the parts of a PDF file that PILean needs: the objects (7.3 of ISO 32000-1),
the cross-reference tables with their trailers, followed back through `/Prev`, and the document
information dictionary. Everything read is untrusted: every loop is bounded by the input or by a
cap (`Limits`), nesting is bounded, a string or a dictionary over its cap is an error, and nothing
is interpreted beyond what is parsed. There are no cross-reference streams and no object streams
here: a file that has them is refused, which is how PILean writes its files (classic tables).

## Main definitions

* `Pdf.Value`, `Pdf.Limits`, `Pdf.parseValue`: the objects.
* `Pdf.Xref`, `Pdf.readXref`: the cross-reference table of a file, newest entry first.
* `Pdf.objectAt`, `Pdf.resolve`: an indirect object.
* `Pdf.textString?`: a PDF text string as a Lean string (UTF-16BE with its byte order mark, or
  ASCII).
* `Pdf.infoDict?`: the trailer's `/Info` dictionary.

## References

* ISO 32000-1:2008, 7.2 (lexical conventions), 7.3 (objects), 7.5.4–7.5.6 (cross-reference
  table, trailer, incremental updates), 7.9.2 (text strings), 14.3.3 (document information).
-/

namespace PILean.Pdf

/-- A PDF object as read. -/
inductive Value where
  /-- `null`. -/
  | null
  /-- `true` or `false`. -/
  | bool (b : Bool)
  /-- An integer. -/
  | int (n : Int)
  /-- A real number, as its text. -/
  | real (text : String)
  /-- A name, its `#xx` escapes decoded. -/
  | name (s : String)
  /-- A literal or hexadecimal string, as bytes. -/
  | str (b : ByteArray)
  /-- An array. -/
  | arr (xs : Array Value)
  /-- A dictionary, its keys in the order read (no key twice). -/
  | dict (kvs : Array (String × Value))
  /-- A reference `n g R`. -/
  | ref (n g : Nat)
  /-- A keyword (an operator of a content stream, `obj`, `stream`, …). -/
  | kw (s : String)
  deriving Inhabited

/-- The caps of the reader. -/
structure Limits where
  /-- The largest file, in bytes. -/
  maxInput : Nat := 64 * 1024 * 1024
  /-- The deepest nesting of arrays and dictionaries. -/
  maxDepth : Nat := 32
  /-- The longest string, in bytes. -/
  maxString : Nat := 65536
  /-- The most entries of one array. -/
  maxEntries : Nat := 65536
  /-- The most entries of one dictionary (its keys are compared with each other). -/
  maxDictEntries : Nat := 4096
  /-- The most objects in the cross-reference tables. -/
  maxObjects : Nat := 1000000
  /-- The most cross-reference sections followed through `/Prev`. -/
  maxSections : Nat := 32
  deriving Inhabited

/-- The value of a dictionary's key, if it has it. -/
def Value.get? (v : Value) (k : String) : Option Value :=
  match v with
  | .dict kvs => (kvs.find? (·.1 == k)).map (·.2)
  | _ => none

/-- The integer, if the value is one. -/
def Value.int? : Value → Option Int
  | .int n => some n
  | _ => none

/-- The natural number, if the value is a non-negative integer. -/
def Value.nat? : Value → Option Nat
  | .int n => if n ≥ 0 then some n.toNat else none
  | _ => none

/-- The name, if the value is one. -/
def Value.name? : Value → Option String
  | .name s => some s
  | _ => none

/-- Whether the value is a number (an integer or a real). -/
def Value.isNum : Value → Bool
  | .int _ | .real _ => true
  | _ => false

/-- Whether the byte is PDF white space (7.2.2). -/
def isWhite (b : UInt8) : Bool := b == 0 || b == 9 || b == 10 || b == 12 || b == 13 || b == 32

/-- Whether the byte is a PDF delimiter. -/
def isDelim (b : UInt8) : Bool :=
  b == 40 || b == 41 || b == 60 || b == 62 || b == 91 || b == 93 || b == 123 || b == 125 ||
    b == 47 || b == 37

/-- Whether the byte is a regular character (neither white space nor a delimiter). -/
def isRegular (b : UInt8) : Bool := !isWhite b && !isDelim b

/-- The position of the first byte at or after `i` that is not white space or inside a comment. -/
def skipWhite (d : ByteArray) (i : Nat) : Nat := Id.run do
  let mut p := i
  for _ in [0:d.size + 1] do
    if p ≥ d.size then return p
    let b := Png.byteAt d p
    if isWhite b then p := p + 1
    else if b == 37 then
      -- a comment, to the end of the line
      p := p + 1
      for _ in [0:d.size] do
        if p ≥ d.size then break
        let c := Png.byteAt d p
        if c == 10 || c == 13 then break
        p := p + 1
    else return p
  return p

/-- The value of a hexadecimal digit. -/
def hexValue (b : UInt8) : Option Nat :=
  if 48 ≤ b && b ≤ 57 then some (b.toNat - 48)
  else if 65 ≤ b && b ≤ 70 then some (b.toNat - 55)
  else if 97 ≤ b && b ≤ 102 then some (b.toNat - 87)
  else none

/-- The regular characters from `i`, and the position after them. -/
def regularRun (d : ByteArray) (i : Nat) : ByteArray × Nat := Id.run do
  let mut p := i
  for _ in [0:d.size] do
    if p ≥ d.size || !isRegular (Png.byteAt d p) then break
    p := p + 1
  return (d.extract i p, p)

/-- A name's text after the slash at `i`, its `#xx` escapes decoded, and the position after it. -/
def readName (lim : Limits) (d : ByteArray) (i : Nat) : Except String (String × Nat) := do
  let (raw, e) := regularRun d i
  if raw.size > 127 * 3 then throw "a name is too long"
  let mut out := ByteArray.empty
  let mut k := 0
  for _ in [0:raw.size + 1] do
    if k ≥ raw.size then break
    let b := Png.byteAt raw k
    if b == 35 then
      match hexValue (Png.byteAt raw (k + 1)), hexValue (Png.byteAt raw (k + 2)) with
      | some h, some l => out := out.push (h * 16 + l).toUInt8; k := k + 3
      | _, _ => throw "a malformed # escape in a name"
    else out := out.push b; k := k + 1
  if out.size > lim.maxString then throw "a name is too long"
  match String.fromUTF8? out with
  | some s => return (s, e)
  | none => return (String.ofList (out.toList.map fun b => Char.ofNat b.toNat), e)

/-- A literal string whose `(` is at `i`: its bytes (escapes decoded, nested parentheses kept) and
the position after the closing `)`. -/
def readLiteral (lim : Limits) (d : ByteArray) (i : Nat) : Except String (ByteArray × Nat) := do
  let mut out := ByteArray.empty
  let mut depth := 1
  let mut p := i + 1
  for _ in [0:d.size + 1] do
    if p ≥ d.size then throw "an unterminated string"
    if out.size > lim.maxString then throw "a string is too long"
    let b := Png.byteAt d p
    if b == 92 then
      let c := Png.byteAt d (p + 1)
      if p + 1 ≥ d.size then throw "an unterminated string"
      if c == 110 then out := out.push 10; p := p + 2
      else if c == 114 then out := out.push 13; p := p + 2
      else if c == 116 then out := out.push 9; p := p + 2
      else if c == 98 then out := out.push 8; p := p + 2
      else if c == 102 then out := out.push 12; p := p + 2
      else if c == 13 then p := p + (if Png.byteAt d (p + 2) == 10 then 3 else 2)
      else if c == 10 then p := p + 2
      else if 48 ≤ c && c ≤ 55 then
        -- up to three octal digits
        let mut v := 0
        let mut k := 0
        for _ in [0:3] do
          let o := Png.byteAt d (p + 1 + k)
          if 48 ≤ o && o ≤ 55 && p + 1 + k < d.size then v := v * 8 + (o.toNat - 48); k := k + 1
          else break
        out := out.push (v % 256).toUInt8
        p := p + 1 + k
      else out := out.push c; p := p + 2
    else if b == 40 then depth := depth + 1; out := out.push b; p := p + 1
    else if b == 41 then
      depth := depth - 1
      if depth == 0 then return (out, p + 1)
      out := out.push b; p := p + 1
    else out := out.push b; p := p + 1
  throw "an unterminated string"

/-- A hexadecimal string whose `<` is at `i`: its bytes (an odd last digit followed by 0) and the
position after the `>`. -/
def readHex (lim : Limits) (d : ByteArray) (i : Nat) : Except String (ByteArray × Nat) := do
  let mut out := ByteArray.empty
  let mut half : Option Nat := none
  let mut p := i + 1
  for _ in [0:d.size + 1] do
    if p ≥ d.size then throw "an unterminated hexadecimal string"
    let b := Png.byteAt d p
    if b == 62 then
      if let some h := half then out := out.push (h * 16).toUInt8
      return (out, p + 1)
    if isWhite b then p := p + 1
    else
      let some v := hexValue b | throw "a hexadecimal string with a character that is not a digit"
      match half with
      | some h => out := out.push (h * 16 + v).toUInt8; half := none
      | none => half := some v
      if out.size > lim.maxString then throw "a string is too long"
      p := p + 1
  throw "an unterminated hexadecimal string"

/-- A number or a keyword from the regular characters `raw`. -/
def numberOrKeyword (raw : ByteArray) : Except String Value := do
  let some s := String.fromUTF8? raw | throw "a token that is not text"
  let body := if s.startsWith "+" || s.startsWith "-" then (s.drop 1).toString else s
  if !body.isEmpty && body.all Char.isDigit then
    if body.length > 18 then throw "an integer is too long"
    let n : Int := body.foldl (fun n c => 10 * n + (c.toNat - 48 : Nat)) 0
    return .int (if s.startsWith "-" then -n else n)
  let digits := body.toList.filter (· != '.')
  if !body.isEmpty && (body.toList.filter (· == '.')).length == 1 && digits.all Char.isDigit &&
      !digits.isEmpty then
    if s.length > 40 then throw "a number is too long"
    return .real s
  match s with
  | "true" => return .bool true
  | "false" => return .bool false
  | "null" => return .null
  | _ =>
    if s.length > 64 then throw "a keyword is too long"
    return .kw s

/-- One value starting at the first non-white byte from `i` (`fuel` bounds the nesting), and the
position after it; `n g R` is read as a reference. Fails at the end of the input, on a `)`, `>`,
`]`, `}` or `>>` out of place, on a dictionary key that is not a name or that occurs twice, and
on any cap of `lim`. -/
def parseValue (lim : Limits) (d : ByteArray) : Nat → Nat → Except String (Value × Nat)
  | 0, _ => throw "the nesting is too deep"
  | fuel + 1, i => do
    let p := skipWhite d i
    if p ≥ d.size then throw "the input ends where a value is expected"
    let b := Png.byteAt d p
    if b == 47 then
      let (s, e) ← readName lim d (p + 1)
      return (.name s, e)
    if b == 40 then
      let (s, e) ← readLiteral lim d p
      return (.str s, e)
    if b == 60 then
      if Png.byteAt d (p + 1) == 60 then
        -- a dictionary
        let mut kvs : Array (String × Value) := #[]
        let mut q := p + 2
        for _ in [0:d.size + 1] do
          let r := skipWhite d q
          if r ≥ d.size then throw "an unterminated dictionary"
          if Png.byteAt d r == 62 && Png.byteAt d (r + 1) == 62 then return (.dict kvs, r + 2)
          if Png.byteAt d r != 47 then throw "a dictionary key that is not a name"
          let (k, e) ← readName lim d (r + 1)
          if kvs.any (·.1 == k) then throw s!"the key {k} occurs twice in a dictionary"
          let (v, e) ← parseValue lim d fuel e
          if kvs.size ≥ lim.maxDictEntries then throw "a dictionary has too many entries"
          kvs := kvs.push (k, v)
          q := e
        throw "an unterminated dictionary"
      let (s, e) ← readHex lim d p
      return (.str s, e)
    if b == 91 then
      let mut xs : Array Value := #[]
      let mut q := p + 1
      for _ in [0:d.size + 1] do
        let r := skipWhite d q
        if r ≥ d.size then throw "an unterminated array"
        if Png.byteAt d r == 93 then return (.arr xs, r + 1)
        let (v, e) ← parseValue lim d fuel r
        if xs.size ≥ lim.maxEntries then throw "an array has too many entries"
        -- `n g R` inside an array
        match v, xs.back?, xs.pop.back? with
        | .kw "R", some (.int g), some (.int n) =>
          if n ≥ 0 && g ≥ 0 then xs := xs.pop.pop.push (.ref n.toNat g.toNat)
          else throw "a malformed reference"
        | _, _, _ => xs := xs.push v
        q := e
      throw "an unterminated array"
    if isDelim b then throw "a delimiter out of place"
    let (raw, e) := regularRun d p
    let v ← numberOrKeyword raw
    -- a reference `n g R` outside an array
    match v with
    | .int n =>
      let q := skipWhite d e
      let (r2, e2) := regularRun d q
      match numberOrKeyword r2 with
      | .ok (.int g) =>
        let q3 := skipWhite d e2
        let (r3, e3) := regularRun d q3
        if r2.size > 0 && r3 == "R".toUTF8 && n ≥ 0 && g ≥ 0 then return (.ref n.toNat g.toNat, e3)
        return (v, e)
      | _ => return (v, e)
    | _ => return (v, e)

/-- Whether `d` has the bytes of `s` at `i`. -/
def hasText (d : ByteArray) (i : Nat) (s : String) : Bool :=
  let p := s.toUTF8
  i + p.size ≤ d.size && d.extract i (i + p.size) == p

/-- The last position at or after `from` where `s` occurs in `d`. -/
def lastIndexOf (d : ByteArray) (s : String) (start : Nat) : Option Nat := Id.run do
  let p := s.toUTF8
  if d.size < p.size then return none
  let mut k := d.size - p.size + 1
  for _ in [0:d.size + 1] do
    if k == 0 || k ≤ start then return none
    k := k - 1
    if hasText d k s then return some k
  return none

/-- The cross-reference table of a file: for each object number, its offset and generation (the
newest section's entry for it), and the newest trailer. -/
structure Xref where
  /-- In-use entries, `(number, offset, generation)`, sorted by number. -/
  entries : Array (Nat × Nat × Nat)
  /-- The trailer dictionary of the newest section. -/
  trailer : Value
  /-- The offsets of the sections, newest first. -/
  sections : Array Nat
  deriving Inhabited

/-- The offset `startxref` gives: the number after the last `startxref` in the last 1024 bytes,
which must be followed by `%%EOF`. -/
def startXref (d : ByteArray) : Except String Nat := do
  let tail := if d.size > 1024 then d.size - 1024 else 0
  let some k := lastIndexOf d "startxref" tail | throw "no startxref near the end of the file"
  let p := skipWhite d (k + 9)
  let (raw, e) := regularRun d p
  let .ok (.int n) := numberOrKeyword raw | throw "startxref is not followed by an offset"
  if n < 0 then throw "startxref is negative"
  -- white space only: `%%EOF` would be skipped as a comment
  let mut q := e
  for _ in [0:64] do
    if q < d.size && isWhite (Png.byteAt d q) then q := q + 1
  if !hasText d q "%%EOF" then throw "startxref is not followed by %%EOF"
  return n.toNat

/-- One cross-reference section at `off`: its entries (in use and free, `(number, offset,
generation, inUse)`), its trailer dictionary and the position after it. -/
def readSection (lim : Limits) (d : ByteArray) (off : Nat) :
    Except String (Array (Nat × Nat × Nat × Bool) × Value) := do
  if !hasText d off "xref" then throw "the cross-reference offset does not point to xref"
  let mut p := off + 4
  let mut out : Array (Nat × Nat × Nat × Bool) := #[]
  for _ in [0:d.size + 1] do
    p := skipWhite d p
    if hasText d p "trailer" then
      let (t, _) ← parseValue lim d lim.maxDepth (p + 7)
      let .dict _ := t | throw "the trailer is not a dictionary"
      return (out, t)
    let (r1, e1) := regularRun d p
    let (r2, e2) := regularRun d (skipWhite d e1)
    let (.ok (.int first), .ok (.int count)) := (numberOrKeyword r1, numberOrKeyword r2)
      | throw "a malformed cross-reference subsection header"
    if first < 0 || count < 0 then throw "a malformed cross-reference subsection header"
    if out.size + count.toNat > lim.maxObjects then throw "too many cross-reference entries"
    p := e2
    -- each entry is 20 bytes: 10 digits, a space, 5 digits, a space, `n` or `f`, two bytes
    let mut q := p
    -- the end of line after the header
    q := skipWhite d q
    for k in [0:count.toNat] do
      if q + 20 > d.size then throw "a truncated cross-reference table"
      let o := d.extract q (q + 10)
      let g := d.extract (q + 11) (q + 16)
      let t := Png.byteAt d (q + 17)
      if Png.byteAt d (q + 10) != 32 || Png.byteAt d (q + 16) != 32 ||
          !(o.toList.all fun b => 48 ≤ b && b ≤ 57) || !(g.toList.all fun b => 48 ≤ b && b ≤ 57) ||
          (t != 110 && t != 102) then throw "a malformed cross-reference entry"
      let ev := fun (x : ByteArray) => x.foldl (fun n b => 10 * n + (b.toNat - 48)) 0
      out := out.push (first.toNat + k, ev o, ev g, t == 110)
      q := q + 20
    p := q
  throw "a cross-reference table without a trailer"

/-- The cross-reference table of the file: the section `startxref` points to and the older ones
its trailer's `/Prev` leads to (at most `lim.maxSections`, none twice), the newest entry of an
object number winning. Fails on a file with a cross-reference stream (no `xref` keyword at the
offset), a malformed table, or a loop of `/Prev`. -/
def readXref (lim : Limits) (d : ByteArray) : Except String Xref := do
  if d.size > lim.maxInput then throw "the file is too large"
  if !hasText d 0 "%PDF-" then throw "not a PDF file"
  let mut off ← startXref d
  let mut seen : Array Nat := #[]
  -- every entry with the age of its section (0 for the newest)
  let mut all : Array (Nat × Nat × Nat × Nat × Bool) := #[]
  let mut newest : Option Value := none
  for _ in [0:lim.maxSections + 1] do
    if seen.contains off then throw "the cross-reference sections form a loop"
    if seen.size ≥ lim.maxSections then throw "too many cross-reference sections"
    let age := seen.size
    seen := seen.push off
    let (es, t) ← readSection lim d off
    if all.size + es.size > lim.maxObjects then throw "too many cross-reference entries"
    if newest.isNone then newest := some t
    all := all ++ es.map fun (n, o, g, u) => (n, age, o, g, u)
    match t.get? "Prev" with
    | some v =>
      let some p := v.nat? | throw "/Prev is not an offset"
      off := p
    | none => break
  let some t := newest | throw "no trailer"
  -- the newest entry of each number: sorted by number, then by age
  let sorted := all.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
  let newestOf := sorted.zipIdx.filterMap fun (e, k) =>
    match sorted[k - 1]? with
    | some p => if k > 0 && p.1 == e.1 then none else some e
    | none => some e
  let used := newestOf.filterMap fun (n, _, o, g, inUse) => if inUse then some (n, o, g) else none
  return { entries := used, trailer := t, sections := seen }

/-- The offset and generation of object `n`, if it is in use. -/
def Xref.find? (x : Xref) (n : Nat) : Option (Nat × Nat) :=
  (x.entries.binSearch (n, 0, 0) (fun a b => a.1 < b.1)).map fun (_, o, g) => (o, g)

/-- The indirect object at `off`, which must start with `n g obj`: its value and the position
after it (before `stream` or `endobj`). -/
def objectAt (lim : Limits) (d : ByteArray) (n g off : Nat) : Except String (Value × Nat) := do
  let p := skipWhite d off
  if p != off then throw s!"the offset of object {n} does not point at its header"
  let (r1, e1) := regularRun d p
  let (r2, e2) := regularRun d (skipWhite d e1)
  let (r3, e3) := regularRun d (skipWhite d e2)
  match numberOrKeyword r1, numberOrKeyword r2 with
  | .ok (.int n'), .ok (.int g') =>
    if n' != n || g' != g || r3 != "obj".toUTF8 then
      throw s!"the offset of object {n} points at another object"
  | _, _ => throw s!"the offset of object {n} does not point at an object"
  parseValue lim d lim.maxDepth e3

/-- The value a reference stands for (one step), or the value itself when it is not a reference;
fails when the object is not in the table. -/
def resolve (lim : Limits) (d : ByteArray) (x : Xref) : Value → Except String Value
  | .ref n g => do
    let some (o, g') := x.find? n | throw s!"object {n} is not in the cross-reference table"
    if g' != g then throw s!"object {n} has another generation"
    return (← objectAt lim d n g o).1
  | v => pure v

/-- A text string as a Lean string: UTF-16BE after the byte order mark `FE FF` (surrogate pairs
joined), or ASCII bytes; `none` otherwise (a lone surrogate, an odd length, a byte above 127
without the mark). -/
def textString? (b : ByteArray) : Option String := Id.run do
  if b.size ≥ 2 && Png.byteAt b 0 == 0xFE && Png.byteAt b 1 == 0xFF then
    if b.size % 2 != 0 then return none
    let mut out := ""
    let mut i := 2
    for _ in [0:b.size] do
      if i ≥ b.size then break
      let u := (Png.byteAt b i).toNat * 256 + (Png.byteAt b (i + 1)).toNat
      if 0xD800 ≤ u && u < 0xDC00 then
        let l := (Png.byteAt b (i + 2)).toNat * 256 + (Png.byteAt b (i + 3)).toNat
        if i + 4 > b.size || l < 0xDC00 || l ≥ 0xE000 then return none
        out := out.push (Char.ofNat (0x10000 + (u - 0xD800) * 1024 + (l - 0xDC00)))
        i := i + 4
      else if 0xDC00 ≤ u && u < 0xE000 then return none
      else
        out := out.push (Char.ofNat u)
        i := i + 2
    return some out
  if b.toList.all (· < 128) then
    return some (String.ofList (b.toList.map fun c => Char.ofNat c.toNat))
  return none

/-- A Lean string as a PDF text string: the byte order mark `FE FF` and UTF-16BE. -/
def utf16Text (s : String) : ByteArray :=
  s.toList.foldl (init := ⟨#[0xFE, 0xFF]⟩) fun out c =>
    let push16 := fun (o : ByteArray) (u : Nat) => (o.push (u / 256).toUInt8).push (u % 256).toUInt8
    let v := c.val.toNat
    if v < 0x10000 then push16 out v
    else
      let w := v - 0x10000
      push16 (push16 out (0xD800 + w / 1024)) (0xDC00 + w % 1024)

/-- The document information dictionary the newest trailer names (`/Info`), if it names one. -/
def infoDict? (lim : Limits) (d : ByteArray) (x : Xref) : Except String (Option Value) := do
  match x.trailer.get? "Info" with
  | none => return none
  | some v =>
    let i ← resolve lim d x v
    let .dict _ := i | throw "/Info is not a dictionary"
    return some i

end PILean.Pdf
