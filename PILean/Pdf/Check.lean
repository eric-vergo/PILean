/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Pdf.Read
import PILean.Png.Inflate
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# A structural check of PDF files

`Pdf.check` reads a PDF file through and says what is wrong with its structure, as far as PILean
writes PDF: the header; `startxref` and the cross-reference tables (every section followed back
through `/Prev`); every object in use, at exactly its listed offset with its number and
generation, its value well formed, a stream's `/Length` (direct or a reference) ending exactly at
`endstream`, then `endobj`; every reference naming an object in use; `/Size` above every object
number, and `/Size` at most one above the reader's object cap; the catalog and the page tree
(`/Kids`, `/Parent` back to the node, `/Count` the number of pages below, at most 32 levels, no
node reached twice anywhere in the tree, so the tree is a tree and its size is linear in the
file); each page's `/MediaBox` (four numbers, inherited or not) and its content streams; every
content stream, of a page or of a form it draws, decoded (no filter, or `FlateDecode` through
PILean's inflate), each stream object decoded once however often it is used, and every use of a
decoded stream (a page's content, a form, an image) counted against one cap for the whole
document, `maxDecoded` bytes; each read as operators with operands: every operator known to PDF 1.7, the operators PILean writes with the
number of operands they take, `q` and `Q` balanced, and every resource a `gs`, `sh` or `Do` names
present in the resources; image objects of the right size once decoded; shadings of type 2 or 3
with their coordinates and a function.

The check is bounded as the reader is (`Pdf.Limits`), and a file it accepts is one the reader can
read. It is a check of structure, not of what a viewer draws: the rasterise-and-compare check of
`tools/pdf-compare.py` and an independent checker such as `qpdf --check` are the others.

## Main definitions

* `Pdf.Summary`, `Pdf.check`.
-/

namespace PILean.Pdf

/-- What a file that passes the check holds. -/
structure Summary where
  /-- The number of objects in use. -/
  objects : Nat
  /-- The number of pages. -/
  pages : Nat
  /-- The number of content streams read (pages and forms). -/
  contents : Nat
  /-- The number of operators read in them. -/
  operators : Nat
  /-- The decoded bytes read, each use of a stream counted (at most `maxDecoded`). -/
  decoded : Nat := 0
  deriving Repr, Inhabited

/-- The most decoded bytes the check reads in one document: the content streams of its pages and
forms and the data of its images, each counted every time it is used. A file PILean writes uses
each stream once and stays under it (a domain colouring of `DomainColouring.maxPixels` pixels
decodes to 12 MiB of RGB samples). -/
def maxDecoded : Nat := 32 * 1024 * 1024

/-- The operators of PDF 1.7 content streams (ISO 32000-1, Annex A). -/
def knownOperators : Array String :=
  #["b", "B", "b*", "B*", "BDC", "BI", "BMC", "BT", "BX", "c", "cm", "CS", "cs", "d", "d0", "d1",
    "Do", "DP", "EI", "EMC", "ET", "EX", "f", "F", "f*", "G", "g", "gs", "h", "i", "ID", "j", "J",
    "K", "k", "l", "m", "M", "MP", "n", "q", "Q", "re", "RG", "rg", "ri", "s", "S", "SC", "sc",
    "SCN", "scn", "sh", "T*", "Tc", "Td", "TD", "Tf", "Tj", "TJ", "TL", "Tm", "Tr", "Ts", "Tw",
    "Tz", "v", "w", "W", "W*", "y", "'", "\""]

/-- The number of operands an operator takes, for the operators whose count is fixed. -/
def operandCount (op : String) : Option Nat :=
  match op with
  | "b" | "B" | "b*" | "B*" | "f" | "F" | "f*" | "h" | "n" | "q" | "Q" | "s" | "S" | "W" | "W*"
  | "BT" | "ET" | "EMC" | "BX" | "EX" | "T*" => some 0
  | "cm" | "Tm" => some 6
  | "c" => some 6
  | "v" | "y" | "re" => some 4
  | "l" | "m" | "Td" | "TD" | "d" | "Tf" => some 2
  | "rg" | "RG" => some 3
  | "k" | "K" => some 4
  | "g" | "G" | "w" | "J" | "j" | "M" | "i" | "gs" | "sh" | "Do" | "cs" | "CS" | "ri" | "Tc"
  | "Tw" | "Tz" | "TL" | "Tr" | "Ts" | "Tj" | "TJ" | "'" | "MP" | "BMC" => some 1
  | "\"" => some 3
  | "DP" | "BDC" | "d0" => some 2
  | "d1" => some 6
  | _ => none

/-- The state of the check: the objects already read, the pages, the content streams read and the
operators read. -/
structure CheckState where
  /-- The objects read, by number. -/
  values : Array (Nat × Value) := #[]
  /-- Pages counted. -/
  pages : Nat := 0
  /-- Content streams read. -/
  contents : Nat := 0
  /-- Operators read. -/
  operators : Nat := 0
  /-- Forms and images that have been checked, by object number. -/
  forms : Std.HashSet Nat := {}
  /-- The nodes of the page tree reached, by object number. -/
  nodes : Std.HashSet Nat := {}
  /-- The stream objects decoded, by object number, with their decoded bytes. -/
  streams : Std.HashMap Nat ByteArray := {}
  /-- The decoded bytes read so far, each use counted. -/
  decoded : Nat := 0

/-- The references an object holds, nested at most `fuel` deep. -/
def refsOf : Nat → Value → Array Nat
  | 0, _ => #[]
  | fuel + 1, v => match v with
    | .ref n _ => #[n]
    | .arr xs => xs.foldl (fun acc x => acc ++ refsOf fuel x) #[]
    | .dict kvs => kvs.foldl (fun acc (_, x) => acc ++ refsOf fuel x) #[]
    | _ => #[]

/-- One object in use at its offset: its value and, for a stream, its raw data (between the end
of line after `stream` and the end of line before `endstream`, `/Length` bytes long). -/
def readObject (lim : Limits) (d : ByteArray) (x : Xref) (n g off : Nat) :
    Except String (Value × Option ByteArray) := do
  if off ≥ d.size then throw s!"object {n}: its offset is past the end of the file"
  let (v, e) ← objectAt lim d n g off
  let p := skipWhite d e
  if hasText d p "endobj" then return (v, none)
  if !hasText d p "stream" then throw s!"object {n}: no endobj after its value"
  let .dict _ := v | throw s!"object {n}: a stream without a dictionary"
  -- the data starts after `stream` and CR LF or LF
  let q := p + 6
  let q := if Png.byteAt d q == 13 && Png.byteAt d (q + 1) == 10 then q + 2
    else if Png.byteAt d q == 10 then q + 1
    else 0
  if q == 0 then throw s!"object {n}: stream is not followed by an end of line"
  let some lenV := v.get? "Length" | throw s!"object {n}: a stream without /Length"
  let lenV ← match lenV with
    | .ref m h =>
      if m == n then throw s!"object {n}: /Length refers to the stream itself"
      resolve lim d x (.ref m h)
    | w => pure w
  let some len := lenV.nat? | throw s!"object {n}: /Length is not a length"
  if q + len > d.size then throw s!"object {n}: the stream runs past the end of the file"
  -- an end of line after the data, not counted in `/Length`, then `endstream`
  let r := q + len
  let r := if Png.byteAt d r == 13 && Png.byteAt d (r + 1) == 10 then r + 2
    else if Png.byteAt d r == 10 || Png.byteAt d r == 13 then r + 1 else 0
  if r == 0 || !hasText d r "endstream" then
    throw s!"object {n}: /Length {len} does not end at an end of line before endstream"
  if !hasText d (skipWhite d (r + 9)) "endobj" then throw s!"object {n}: no endobj after endstream"
  return (v, some (d.extract q (q + len)))

/-- A stream's data decoded: none or `FlateDecode` as its `/Filter` (and no `/DecodeParms`), at
most `cap` bytes. -/
def decodeStream (n : Nat) (v : Value) (raw : ByteArray) (cap : Nat := maxDecoded) :
    Except String ByteArray := do
  if (v.get? "DecodeParms").isSome then throw s!"object {n}: decode parameters are not supported"
  match v.get? "Filter" with
  | none => return raw
  | some (.name "FlateDecode") | some (.arr #[.name "FlateDecode"]) =>
    match Png.zlibDecompress raw cap with
    | .ok b => return b
    | .error e => throw s!"object {n}: its Flate data is damaged or decodes to more than the \
        document's {maxDecoded} bytes ({e.toString})"
  | some _ => throw s!"object {n}: a filter other than FlateDecode"

/-- Counts `k` decoded bytes read against the document's cap, `maxDecoded`. -/
def useDecoded (n k : Nat) : StateT CheckState (Except String) Unit := do
  let st ← get
  if st.decoded + k > maxDecoded then
    throw s!"object {n}: the document decodes to more than {maxDecoded} bytes"
  set { st with decoded := st.decoded + k }

/-- The stream object `n` (already read: its dictionary `v` and raw data `raw`) decoded, once:
a stream decoded before is taken from the state, and a new one is inflated to at most what is
left of the document's cap. Each use is counted against the cap (`useDecoded`). -/
def streamData (n : Nat) (v : Value) (raw : ByteArray) :
    StateT CheckState (Except String) ByteArray := do
  let st ← get
  let data ← match st.streams[n]? with
    | some b => pure b
    | none => do
      let b ← decodeStream n v raw (maxDecoded - st.decoded)
      modify fun st => { st with streams := st.streams.insert n b }
      pure b
  useDecoded n data.size
  return data

/-- The names a resource dictionary gives in its category `cat` (`ExtGState`, `Shading`,
`XObject`), with their values (resolved one step). -/
def resourceNames (lim : Limits) (d : ByteArray) (x : Xref) (res : Value) (cat : String) :
    Except String (Array (String × Value)) := do
  match res.get? cat with
  | none => return #[]
  | some c =>
    match ← resolve lim d x c with
    | .dict kvs => return kvs
    | _ => throw s!"the resources' /{cat} is not a dictionary"

/-- The operators and their operands of decoded content, in order; fails on a token that is not
an operand or a known operator, on an inline image, and on a string, name or array of operands
past the caps. -/
def contentOps (lim : Limits) (c : ByteArray) : Except String (Array (String × Array Value)) := do
  let mut out : Array (String × Array Value) := #[]
  let mut operands : Array Value := #[]
  let mut p := 0
  for _ in [0:c.size + 1] do
    p := skipWhite c p
    if p ≥ c.size then break
    let (v, e) ← parseValue lim c lim.maxDepth p
    match v with
    | .kw op =>
      if !knownOperators.contains op then throw s!"an unknown operator {op}"
      if op == "BI" || op == "ID" || op == "EI" then throw "an inline image"
      out := out.push (op, operands)
      operands := #[]
    | .ref _ _ => throw "a reference inside a content stream"
    | _ =>
      if operands.size ≥ 64 then throw "too many operands"
      operands := operands.push v
    p := e
  if !operands.isEmpty then throw "operands after the last operator"
  return out

/-- Checks a shading dictionary: type 2 with four coordinates or type 3 with six, a colour space
and a function (a dictionary of type 2 or 3, or a reference). -/
def checkShading (v : Value) : Except String Unit := do
  let ty := (v.get? "ShadingType").bind Value.nat?
  let coords := match v.get? "Coords" with | some (.arr cs) => cs | _ => #[]
  match ty with
  | some 2 => if coords.size != 4 || !coords.all Value.isNum then throw "an axial shading's /Coords"
  | some 3 => if coords.size != 6 || !coords.all Value.isNum then throw "a radial shading's /Coords"
  | _ => throw "a shading of a type PILean does not write"
  if (v.get? "ColorSpace").isNone then throw "a shading without /ColorSpace"
  match v.get? "Function" with
  | some (.dict _) | some (.ref _ _) | some (.arr _) => pure ()
  | _ => throw "a shading without /Function"

mutual

/-- Checks the content `c` of a page or form with resources `res`: the operators (`contentOps`),
their operand counts and kinds for the fixed ones, `q`/`Q` balanced, and every name of `gs`,
`sh` and `Do` in the resources; a form drawn by `Do` is checked in turn (`fuel` bounds the depth,
`forms` the forms already checked). Structural recursion on `fuel`. -/
def checkContent (lim : Limits) (d : ByteArray) (x : Xref) (res : Value) (c : ByteArray) :
    Nat → StateT CheckState (Except String) Unit
  | 0 => throw "forms are nested too deeply"
  | fuel + 1 => do
    let ops : Array (String × Array Value) ← contentOps lim c
    let gss ← resourceNames lim d x res "ExtGState"
    let shs ← resourceNames lim d x res "Shading"
    let xos ← resourceNames lim d x res "XObject"
    let mut depth : Nat := 0
    for opArgs in ops do
      let op : String := opArgs.1
      let args : Array Value := opArgs.2
      if let some k := operandCount op then
        if args.size != k then throw s!"{op} takes {k} operands, not {args.size}"
      if ["c", "cm", "v", "y", "re", "l", "m", "rg", "RG", "k", "K", "g", "G", "w", "M", "Td",
          "TD", "Tm", "i"].contains op && !args.all Value.isNum then
        throw s!"{op} takes numbers"
      if op == "J" || op == "j" then
        match (args[0]? : Option Value) with
        | some (.int k) => if k < 0 || k > 2 then throw s!"{op} out of range"
        | _ => throw s!"{op} takes an integer"
      if op == "d" then
        match (args[0]? : Option Value), (args[1]? : Option Value) with
        | some (.arr xs), some o =>
          if !xs.all Value.isNum || !o.isNum then throw "d takes an array of numbers and a phase"
        | _, _ => throw "d takes an array and a phase"
      if op == "q" then depth := depth + 1
      if op == "Q" then
        if depth == 0 then throw "Q without q"
        depth := depth - 1
      let named := fun (table : Array (String × Value)) => do
        match (args[0]? : Option Value) with
        | some (.name s) =>
          match table.find? (·.1 == s) with
          | some (_, v) => pure v
          | none => throw s!"{op} names {s}, which the resources do not have"
        | _ => throw s!"{op} takes a name"
      if op == "gs" then
        let v ← resolve lim d x (← named gss)
        let .dict _ := v | throw "an ExtGState that is not a dictionary"
      if op == "sh" then
        let v ← resolve lim d x (← named shs)
        checkShading v
      if op == "Do" then
        let v ← named xos
        let .ref n _ := v | throw "an XObject that is not a reference"
        checkXObject lim d x n fuel
      modify fun st => { st with operators := st.operators + 1 }
    if depth != 0 then throw "q without Q"
    modify fun st => { st with contents := st.contents + 1 }

/-- Checks an XObject drawn by `Do`: a form (its content checked once, with its resources or the
caller's) or an image (its decoded data as long as its size, components and bits ask), each
decoded once (`streamData`). Structural recursion on `fuel`. -/
def checkXObject (lim : Limits) (d : ByteArray) (x : Xref) (n : Nat) :
    Nat → StateT CheckState (Except String) Unit
  | 0 => throw "forms are nested too deeply"
  | fuel + 1 => do
    if (← get).forms.contains n then return
    modify fun st => { st with forms := st.forms.insert n }
    let some (off, g) := x.find? n | throw s!"object {n} is not in the cross-reference table"
    let (v, raw) ← readObject lim d x n g off
    let some raw := raw | throw s!"object {n}: an XObject that is not a stream"
    let data ← streamData n v raw
    match v.get? "Subtype" with
    | some (.name "Form") =>
      let some bbox := v.get? "BBox" | throw s!"object {n}: a form without /BBox"
      let .arr bs := bbox | throw s!"object {n}: /BBox is not an array"
      if bs.size != 4 || !bs.all Value.isNum then throw s!"object {n}: /BBox is not four numbers"
      let res ← match v.get? "Resources" with
        | some r => resolve lim d x r
        | none => pure (.dict #[])
      checkContent lim d x res data fuel
    | some (.name "Image") =>
      let (some w, some h) := ((v.get? "Width").bind Value.nat?, (v.get? "Height").bind Value.nat?)
        | throw s!"object {n}: an image without its size"
      let bpc := ((v.get? "BitsPerComponent").bind Value.nat?).getD 0
      let comps := match v.get? "ColorSpace" with
        | some (.name "DeviceGray") => 1
        | some (.name "DeviceRGB") => 3
        | some (.name "DeviceCMYK") => 4
        | _ => 0
      if bpc != 8 || comps == 0 then throw s!"object {n}: an image PILean does not write"
      if data.size != w * h * comps then
        throw s!"object {n}: the image's data has {data.size} bytes, not {w * h * comps}"
      if let some m := v.get? "SMask" then
        let .ref k _ := m | throw s!"object {n}: /SMask is not a reference"
        checkXObject lim d x k fuel
    | _ => throw s!"object {n}: an XObject that is neither a form nor an image"

end

/-- Walks the page tree from node `n` (its parent `parent`), at most `fuel` levels, with the
inherited `/MediaBox` and `/Resources`: the leaves are pages (checked with their content), the
nodes `/Pages` whose `/Count` is the number of pages below them. Returns that number. A node
reached a second time, from anywhere in the tree, is refused (`CheckState.nodes`), so every node
is read once. Structural recursion on `fuel`. -/
def walkPages (lim : Limits) (d : ByteArray) (x : Xref) (n : Nat) (parent : Option Nat)
    (box res : Option Value) : Nat → StateT CheckState (Except String) Nat
  | 0 => throw "the page tree is too deep"
  | fuel + 1 => do
    if (← get).nodes.contains n then throw s!"object {n} occurs twice in the page tree"
    modify fun st => { st with nodes := st.nodes.insert n }
    let some (off, g) := x.find? n | throw s!"object {n} is not in the cross-reference table"
    let (v, _) ← readObject lim d x n g off
    match v.get? "Parent", parent with
    | some (.ref p _), some q => if p != q then throw s!"object {n}: /Parent is not its parent"
    | none, none => pure ()
    | _, _ => throw s!"object {n}: a wrong /Parent"
    let box := (v.get? "MediaBox").orElse fun _ => box
    let res := (v.get? "Resources").orElse fun _ => res
    match v.get? "Type" with
    | some (.name "Pages") =>
      let some (.arr kids) := v.get? "Kids" | throw s!"object {n}: /Kids is not an array"
      let mut count := 0
      for k in kids do
        let .ref m _ := k | throw s!"object {n}: a kid that is not a reference"
        count := count + (← walkPages lim d x m (some n) box res fuel)
      if (v.get? "Count").bind Value.nat? != some count then
        throw s!"object {n}: /Count is not the number of pages below it ({count})"
      return count
    | some (.name "Page") =>
      let some b := box | throw s!"page {n}: no /MediaBox"
      let .arr bs ← resolve lim d x b | throw s!"page {n}: /MediaBox is not an array"
      if bs.size != 4 || !bs.all Value.isNum then throw s!"page {n}: /MediaBox is not four numbers"
      let resV ← match res with
        | some r => resolve lim d x r
        | none => pure (.dict #[])
      let streams ← match v.get? "Contents" with
        | some (.ref m _) => pure #[m]
        | some (.arr xs) => xs.mapM fun
          | .ref m _ => pure m
          | _ => throw s!"page {n}: a content that is not a reference"
        | none => pure #[]
        | some _ => throw s!"page {n}: /Contents is neither a stream nor an array"
      -- the content streams joined, as a viewer reads them
      let mut all := ByteArray.empty
      for m in streams do
        let some (o, h) := x.find? m | throw s!"object {m} is not in the cross-reference table"
        let (sv, raw) ← readObject lim d x m h o
        let some raw := raw | throw s!"page {n}: content object {m} is not a stream"
        all := all ++ (← streamData m sv raw) ++ "\n".toUTF8
      checkContent lim d x resV all 16
      modify fun st => { st with pages := st.pages + 1 }
      return 1
    | _ => throw s!"object {n}: a node of the page tree that is neither /Pages nor /Page"

/-- Checks the structure of a PDF file (see the module docstring); the summary of what it holds,
or the first problem found. -/
def check (d : ByteArray) (lim : Limits := {}) : Except String Summary := do
  let x ← readXref lim d
  let some size := (x.trailer.get? "Size").bind Value.nat? | throw "the trailer has no /Size"
  if size > lim.maxObjects + 1 then
    throw s!"/Size {size} is above the reader's cap of {lim.maxObjects} objects"
  -- every object in use, where the table says
  let mut values : Array (Nat × Value) := #[]
  for (n, off, g) in x.entries do
    if n == 0 then throw "object 0 is listed in use"
    if n ≥ size then throw s!"object {n} is not below /Size {size}"
    let (v, _) ← readObject lim d x n g off
    values := values.push (n, v)
  -- every reference names an object in use
  let refsOk := fun (v : Value) => (refsOf lim.maxDepth v).all fun m => (x.find? m).isSome
  if let some (n, _) := values.find? fun (_, v) => !refsOk v then
    throw s!"object {n} refers to an object that is not in use"
  if !refsOk x.trailer then throw "the trailer refers to an object that is not in use"
  let some (.ref root _) := x.trailer.get? "Root" | throw "the trailer has no /Root"
  let some (_, cat) := values.find? (·.1 == root) | throw "the catalog is not in use"
  if ((cat.get? "Type").bind Value.name?) != some "Catalog" then throw "/Root is not a catalog"
  let some (.ref pages _) := cat.get? "Pages" | throw "the catalog has no /Pages"
  let (n, st) ← (walkPages lim d x pages none none none 32).run {}
  if n == 0 then throw "the document has no page"
  return { objects := x.entries.size, pages := st.pages, contents := st.contents,
           operators := st.operators, decoded := st.decoded }

end PILean.Pdf
