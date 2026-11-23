/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Svg
import PILean.Png
import PILean.Version

/-!
# Source information in images

A `Source` says which Lean declaration, in which file and line, made an image. It is written into
SVG, PNG, APNG and GIF files and read back; `docs/TRUST.md` describes the vocabulary.

## Main definitions

* `Trust.Source`: the record; `Trust.Source.validate` says whether it can be written.
* `Trust.Source.svgNodes`, `Trust.withSourceSvg`: the `<title>`, `<desc>` and `<metadata>`
  elements, as nodes and as text inserted into a document.
* `Trust.withSourcePng`, `Trust.withSourceGif`, `Trust.withSource`: the source inserted into
  finished PNG, APNG and GIF files, so every writer gets it without change.
* `Trust.Source.read?`: reads the record back from any of the formats.
* `Trust.safeLink?`, `Trust.escapeControl`, `Trust.infoLines`: how a reader shows what it read.

## Implementation notes

* Everything read is untrusted. The reader refuses inputs above `Trust.maxInput` bytes and
  values above `Trust.maxField` bytes, accepts each key at most once, ignores unknown keys, and
  never interprets a value. SVG is scanned by a small bounded tag scanner that reads only the
  attributes of the `pilean:source` element; there is no general XML parser.
* A `Source` is valid for writing if no value contains a character that XML 1.0 cannot carry
  (this includes NUL), no value is longer than `maxField` bytes, and the fingerprint is 64
  lowercase hexadecimal digits. The GIF comment is line based, so a GIF additionally refuses
  values with a line feed or a carriage return; SVG and PNG carry them.
* PNG: one uncompressed `iTXt` chunk per field, keyword `PILean:` followed by the key, inserted
  directly after `IHDR`. The reader looks at the chunks before the first `IDAT` and checks the
  CRC of the chunks it uses; it does not decode the image.
* GIF: one comment extension after the global colour table whose text is the line
  `PILean source 1` and then one `key=value` line a field, in UTF-8, in sub-blocks of at most
  255 bytes.

## References

* PNG Specification, Third Edition (W3C), section "Textual information" (`iTXt`).
* Graphics Interchange Format, Version 89a (CompuServe, 1990), "Comment Extension".
* Scalable Vector Graphics (SVG) 1.1, `title`, `desc` and `metadata`; Extensible Markup Language
  (XML) 1.0, character and entity references.
-/

namespace PILean.Trust

/-- The namespace of the `pilean:source` element. -/
def svgNamespace : String := "https://github.com/eric-vergo/PILean/ns/source/1"

/-- The largest input the reader looks at, in bytes. -/
def maxInput : Nat := 64 * 1024 * 1024

/-- The largest value of one field, in bytes of UTF-8. -/
def maxField : Nat := 4096

/-- The first line of the GIF comment. -/
def gifMagic : String := "PILean source 1"

/-- The keys of the fields, in the order they are written. -/
def keys : Array String :=
  #["module", "decl", "file", "line", "column", "repo", "commit", "version", "fingerprint",
    "standing", "proves"]

/-- Where an image came from: the Lean declaration that built it. -/
structure Source where
  /-- The Lean module of the declaration. -/
  module : String
  /-- The declaration's name. -/
  decl : String
  /-- The file of the declaration, relative to the repository. -/
  file : String
  /-- The line of the declaration (from 1). -/
  line : Nat
  /-- The column of the declaration. -/
  column : Nat
  /-- The repository's URL. -/
  repo : Option String := none
  /-- The commit the image was built from. -/
  commit : Option String := none
  /-- The version of PILean that wrote the image. -/
  version : String
  /-- A SHA-256 fingerprint, 64 lowercase hexadecimal digits. -/
  fingerprint : Option String := none
  /-- The figure's standing as the build recorded it: `proved` or `illustration`
  (`PILean.Trust.Standing.word`). -/
  standing : Option String := none
  /-- For a proved figure, the theorems linked to it, by full name, separated by single spaces. -/
  proves : Option String := none
deriving BEq, Repr, Inhabited

/-- The fields in writing order as `(key, value)`; absent options are left out. -/
def Source.fields (s : Source) : Array (String × String) :=
  #[("module", s.module), ("decl", s.decl), ("file", s.file), ("line", toString s.line),
    ("column", toString s.column)] ++
  (match s.repo with | some r => #[("repo", r)] | none => #[]) ++
  (match s.commit with | some r => #[("commit", r)] | none => #[]) ++
  #[("version", s.version)] ++
  (match s.fingerprint with | some r => #[("fingerprint", r)] | none => #[]) ++
  (match s.standing with | some r => #[("standing", r)] | none => #[]) ++
  (match s.proves with | some r => #[("proves", r)] | none => #[])

/-- Whether a recorded standing and list of theorems are well formed: no standing and no
theorems, `illustration` without theorems, or `proved` with a non-empty list of names separated
by single spaces, each name non-empty and without white space. -/
def standingOk (standing proves : Option String) : Bool :=
  match standing, proves with
  | none, none => true
  | some "illustration", none => true
  | some "proved", some ts =>
    !ts.isEmpty && (ts.splitOn " ").all fun t => !t.isEmpty && !t.any Char.isWhitespace
  | _, _ => false

/-- Whether `s` is 64 lowercase hexadecimal digits. -/
def isFingerprint (s : String) : Bool :=
  s.length == 64 && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- Whether the value can be written: at most `maxField` bytes, only characters XML 1.0 can
carry. -/
def validValue (v : String) : Bool :=
  v.utf8ByteSize ≤ maxField && v.all xmlChar

/-- Checks that the record can be written to every format: valid values, a fingerprint of 64
lowercase hexadecimal digits, a well-formed standing (`standingOk`), a non-empty module,
declaration and file. -/
def Source.validate (s : Source) : Except String Unit := do
  for (k, v) in s.fields do
    if !validValue v then throw s!"the value of {k} is too long or has a character XML cannot carry"
  if s.module.isEmpty || s.decl.isEmpty || s.file.isEmpty || s.version.isEmpty then
    throw "module, decl, file and version must not be empty"
  if let some f := s.fingerprint then
    if !isFingerprint f then throw "the fingerprint is not 64 lowercase hexadecimal digits"
  if !standingOk s.standing s.proves then
    throw "the standing is not proved with its theorems or illustration without any"

/-- The record from a list of `(key, value)` pairs, as the readers collect them: unknown keys are
ignored, a known key twice is an error, a value above `maxField` bytes or with a character XML
cannot carry (so one the writers refuse) is an error, `line` and
`column` are decimal numbers of at most nine digits, a fingerprint is 64 lowercase hexadecimal
digits, the standing and its theorems are well formed (`standingOk`), and `module`, `decl`,
`file`, `line`, `column` and `version` must be present. -/
def Source.ofFields (kvs : Array (String × String)) : Except String Source := do
  let mut seen : Array String := #[]
  for (k, v) in kvs do
    if keys.contains k then
      if seen.contains k then throw s!"the key {k} occurs twice"
      if v.utf8ByteSize > maxField then throw s!"the value of {k} is too long"
      if !v.all xmlChar then throw s!"the value of {k} has a character XML cannot carry"
      seen := seen.push k
  let find := fun (k : String) => (kvs.find? (·.1 == k)).map (·.2)
  let req := fun (k : String) => match find k with
    | some v => Except.ok v
    | none => Except.error s!"the key {k} is missing"
  let num := fun (k : String) => do
    let v ← req k
    if v.isEmpty || v.length > 9 || !v.all Char.isDigit then
      throw s!"the value of {k} is not a number"
    return v.foldl (fun n c => 10 * n + (c.toNat - 48)) 0
  let fp := find "fingerprint"
  if let some f := fp then
    if !isFingerprint f then throw "the fingerprint is not 64 lowercase hexadecimal digits"
  let m ← req "module"
  let d ← req "decl"
  let f ← req "file"
  let l ← num "line"
  let c ← num "column"
  let v ← req "version"
  if !standingOk (find "standing") (find "proves") then
    throw "the standing is not proved with its theorems or illustration without any"
  return { module := m, decl := d, file := f, line := l, column := c, repo := find "repo",
           commit := find "commit", version := v, fingerprint := fp,
           standing := find "standing", proves := find "proves" }

/-- Whether `url` is safe to offer as a link: it starts with `http://` or `https://` (lowercase),
has something after that, is at most `maxField` bytes, and consists of printable ASCII only
(`U+0021 … U+007E`) without `"`, `'`, `` ` ``, `<`, `>` and `\`. Anything else, including a
`javascript:` or `data:` URL, is refused; characters outside ASCII must be percent-encoded. -/
def safeLink? (url : String) : Option String :=
  let rest := if url.startsWith "https://" then some (url.drop 8)
    else if url.startsWith "http://" then some (url.drop 7) else none
  match rest with
  | some r =>
    if !r.isEmpty && url.utf8ByteSize ≤ maxField &&
        url.toList.all (fun c => 0x21 ≤ c.val && c.val ≤ 0x7E && !"\"'`<>\\".toList.contains c)
    then some url else none
  | none => none

/-- Whether a character must not reach a terminal or a log as it is: the C0 and C1 control
characters and `U+007F`; the line and paragraph separators `U+2028`, `U+2029` and `U+0085`; the
bidirectional formatting characters (`U+061C`, `U+200E`, `U+200F`, `U+202A` to `U+202E`,
`U+2066` to `U+2069`); and the invisible formatting characters `U+00AD`, `U+034F`, `U+115F`,
`U+1160`, `U+17B4`, `U+17B5`, `U+180B` to `U+180F`, `U+200B` to `U+200D`, `U+2060` to `U+2064`,
`U+3164`, `U+FE00` to `U+FE0F`, `U+FEFF`, `U+FFA0` and `U+FFF9` to `U+FFFB`. Each of these can
start a terminal escape, end a line, reorder or hide text. -/
def unsafeChar (c : Char) : Bool :=
  let v := c.val
  v < 0x20 || (0x7F ≤ v && v ≤ 0x9F) || v == 0xAD || v == 0x34F || v == 0x61C || v == 0x115F ||
    v == 0x1160 || v == 0x17B4 || v == 0x17B5 || (0x180B ≤ v && v ≤ 0x180F) ||
    (0x200B ≤ v && v ≤ 0x200F) || (0x2028 ≤ v && v ≤ 0x202E) || (0x2060 ≤ v && v ≤ 0x2064) ||
    (0x2066 ≤ v && v ≤ 0x2069) || v == 0x3164 || (0xFE00 ≤ v && v ≤ 0xFE0F) || v == 0xFEFF ||
    v == 0xFFA0 || (0xFFF9 ≤ v && v ≤ 0xFFFB)

/-- The text with every `unsafeChar` and the backslash written as escapes (`\n`, `\r`, `\t`,
`\\`, `\u{..}` in hexadecimal), for showing untrusted text on one line: the result has no
`unsafeChar`, so it cannot move the cursor, start a new line, reorder or hide what follows. The
command-line tools pass every string that comes from their input through it before printing. -/
def escapeControl (s : String) : String :=
  s.foldl (init := "") fun out c =>
    if c == '\n' then out ++ "\\n" else if c == '\r' then out ++ "\\r"
    else if c == '\t' then out ++ "\\t" else if c == '\\' then out ++ "\\\\"
    else if unsafeChar c then
      out ++ "\\u{" ++ String.ofList (Nat.toDigits 16 c.val.toNat) ++ "}"
    else out.push c

/-! ### Bytes -/

/-- The first index at or after `start` where `pat` occurs in `d`. -/
def findBytes (d pat : ByteArray) (start : Nat := 0) : Option Nat := Id.run do
  if pat.size == 0 || d.size < pat.size then return none
  let first := Png.byteAt pat 0
  for i in [start:d.size - pat.size + 1] do
    if Png.byteAt d i == first && d.extract i (i + pat.size) == pat then return some i
  return none

/-- Whether `d` has `pat` at index `i`. -/
def hasAt (d : ByteArray) (i : Nat) (pat : String) : Bool :=
  let p := pat.toUTF8
  i + p.size ≤ d.size && d.extract i (i + p.size) == p

/-- Whether the byte is XML whitespace. -/
def isSpace (b : UInt8) : Bool := b == 32 || b == 9 || b == 10 || b == 13

/-! ### SVG -/

/-- The elements of the source information: `<title>` (the declaration), `<desc>` and
`<metadata>` with the `pilean:source` element. -/
def Source.svgNodes (s : Source) : Array Svg.Node :=
  let attrs := #[("xmlns:pilean", svgNamespace)] ++ s.fields
  #[Svg.el "title" #[] #[.text s.decl],
    Svg.el "desc" #[] #[.text s!"Generated by {s.decl} in {s.file}:{s.line} with PILean \
      {s.version}"],
    Svg.el "metadata" #[] #[Svg.el "pilean:source" attrs]]

/-- The end index of the `>` of the tag whose text starts at `i`, skipping quoted values. -/
def tagEnd (d : ByteArray) (i : Nat) : Option Nat := Id.run do
  let mut quote : UInt8 := 0
  for j in [i:d.size] do
    let b := Png.byteAt d j
    if quote != 0 then
      if b == quote then quote := 0
    else if b == 34 || b == 39 then quote := b
    else if b == 62 then return some j
  return none

/-- `svg` with the source information as the first children of the root element, indented like
the writer's output. Fails if the text has no `<svg ` root tag or already has a source. -/
def withSourceSvg (svg : String) (s : Source) : Except String String := do
  s.validate
  let d := svg.toUTF8
  if (findBytes d "<pilean:source".toUTF8).isSome then throw "the SVG already has a source"
  let some i := findBytes d "<svg ".toUTF8 | throw "no <svg root element"
  let some e := tagEnd d (i + 5) | throw "the <svg tag is not closed"
  let nodes := "\n".intercalate ((s.svgNodes.map (Svg.render 2)).toList)
  let out :=
    if Png.byteAt d (e - 1) == 47 then
      d.extract 0 (e - 1) ++ ">\n".toUTF8 ++ nodes.toUTF8 ++ "\n</svg>".toUTF8 ++
        d.extract (e + 1) d.size
    else d.extract 0 (e + 1) ++ "\n".toUTF8 ++ nodes.toUTF8 ++ d.extract (e + 1) d.size
  match String.fromUTF8? out with
  | some o => return o
  | none => throw "the SVG is not valid UTF-8"

/-- The value of the character reference or entity `name` (the text between `&` and `;`). -/
def entityValue (name : String) : Option Char :=
  match name with
  | "amp" => some '&' | "lt" => some '<' | "gt" => some '>' | "quot" => some '"'
  | "apos" => some '\''
  | _ =>
    if name.startsWith "#x" then
      let h := (name.drop 2).toString
      if h.isEmpty || h.length > 6 || !h.all Char.isHexDigit then none
      else
        let n := h.foldl (fun n c =>
          16 * n + (if c.isDigit then c.toNat - 48 else (c.toLower.toNat - 87))) 0
        (if n ≤ 0x10FFFF && n != 0 then (Char.ofNat n) else none)
    else if name.startsWith "#" then
      let h := (name.drop 1).toString
      if h.isEmpty || h.length > 7 || !h.all Char.isDigit then none
      else
        let n := h.foldl (fun n c => 10 * n + (c.toNat - 48)) 0
        (if n ≤ 0x10FFFF && n != 0 then (Char.ofNat n) else none)
    else none

/-- The attribute value `raw` (UTF-8 bytes) with entities and character references replaced. Fails
on a `<`, an unknown or unterminated entity, a character XML cannot carry, or a result above
`maxField` bytes. -/
def unescapeAttr (raw : ByteArray) : Except String String := do
  let mut out := ByteArray.empty
  let mut i := 0
  for _ in [0:raw.size + 1] do
    if i ≥ raw.size then break
    let b := Png.byteAt raw i
    if b == 60 then throw "a < inside an attribute value"
    else if b == 38 then
      let some j := findBytes raw ";".toUTF8 i | throw "an unterminated entity"
      if j - i > 10 then throw "an unknown entity"
      let some name := String.fromUTF8? (raw.extract (i + 1) j) | throw "an unknown entity"
      let some c := entityValue name | throw "an unknown entity"
      if !xmlChar c then throw "a character reference to a character XML cannot carry"
      out := out ++ (String.singleton c).toUTF8
      i := j + 1
    else
      out := out.push b
      i := i + 1
    if out.size > maxField then throw "an attribute value is too long"
  match String.fromUTF8? out with
  | some v => return v
  | none => throw "an attribute value is not UTF-8"

/-- The attributes of the tag whose attribute list starts at `i`, and the index of its `>`. At
most 64 attributes; every attribute is `name="value"` or `name='value'`, preceded by white space;
a repeated attribute name is an error. -/
def parseAttrs (d : ByteArray) (i : Nat) : Except String (Array (String × String) × Nat) := do
  let mut pos := i
  let mut out : Array (String × String) := #[]
  for _ in [0:d.size + 1] do
    while isSpace (Png.byteAt d pos) && pos < d.size do pos := pos + 1
    if pos ≥ d.size then throw "the tag is not closed"
    let b := Png.byteAt d pos
    if b == 62 then return (out, pos)
    if b == 47 && Png.byteAt d (pos + 1) == 62 then return (out, pos + 1)
    let start := pos
    while pos < d.size && !(isSpace (Png.byteAt d pos) || Png.byteAt d pos == 61 ||
        Png.byteAt d pos == 62 || Png.byteAt d pos == 47) do pos := pos + 1
    if pos == start then throw "a malformed attribute"
    let some name := String.fromUTF8? (d.extract start pos) | throw "a malformed attribute"
    while isSpace (Png.byteAt d pos) && pos < d.size do pos := pos + 1
    if Png.byteAt d pos != 61 then throw "an attribute without a value"
    pos := pos + 1
    while isSpace (Png.byteAt d pos) && pos < d.size do pos := pos + 1
    let q := Png.byteAt d pos
    if q != 34 && q != 39 then throw "an unquoted attribute value"
    let some e := findBytes d ⟨#[q]⟩ (pos + 1) | throw "an unterminated attribute value"
    if e - pos > 8 * maxField then throw "an attribute value is too long"
    let v ← unescapeAttr (d.extract (pos + 1) e)
    if out.any (·.1 == name) then throw s!"the attribute {name} occurs twice"
    if out.size ≥ 64 then throw "too many attributes"
    out := out.push (name, v)
    pos := e + 1
    let n := Png.byteAt d pos
    if !(isSpace n || n == 62 || n == 47) then throw "a malformed attribute list"
  throw "the tag is not closed"

/-- The fields of the one `pilean:source` element of an SVG document (as UTF-8 bytes), outside
comments, processing instructions and CDATA sections; none if there is no such element. Fails
on a second element, on an element whose `xmlns:pilean` is not `svgNamespace`, or on a malformed
attribute list. -/
def svgFields (d : ByteArray) : Except String (Option (Array (String × String))) := do
  let mut found : Option (Array (String × String)) := none
  let mut pos := 0
  for _ in [0:d.size + 1] do
    let some i := findBytes d "<".toUTF8 pos | break
    if hasAt d i "<!--" then
      let some j := findBytes d "-->".toUTF8 (i + 4) | break
      pos := j + 3
    else if hasAt d i "<![CDATA[" then
      let some j := findBytes d "]]>".toUTF8 (i + 9) | break
      pos := j + 3
    else if hasAt d i "<?" then
      let some j := findBytes d "?>".toUTF8 (i + 2) | break
      pos := j + 2
    else if hasAt d i "<pilean:source" && isSpace (Png.byteAt d (i + 14)) ||
        hasAt d i "<pilean:source/" then
      if found.isSome then throw "more than one pilean:source element"
      let (attrs, e) ← parseAttrs d (i + 14)
      if (attrs.find? (·.1 == "xmlns:pilean")).map (·.2) != some svgNamespace then
        throw "the pilean:source element is not in the PILean namespace"
      found := some (attrs.filter (·.1 != "xmlns:pilean"))
      pos := e + 1
    else
      let some e := tagEnd d (i + 1) | break
      pos := e + 1
  return found

/-! ### PNG and APNG -/

/-- The prefix of the keywords of the PNG chunks. -/
def pngPrefix : String := "PILean:"

/-- The `iTXt` chunks of the source, in writing order. -/
def Source.pngChunks (s : Source) : Except String ByteArray := do
  let mut out := ByteArray.empty
  for (k, v) in s.fields do
    let entry : Png.TextEntry := { keyword := pngPrefix ++ k, text := v, international := true }
    out := out ++ (← (Png.textChunk entry).mapError toString)
  return out

/-- The fields of the `iTXt` chunks with keyword `PILean:…` before the first `IDAT` of a PNG or
APNG file. Fails if the file is not a PNG, ends before `IDAT`, or a source chunk has a wrong CRC,
is compressed, has a text that is not UTF-8, or is larger than the field cap allows. -/
def pngFields (d : ByteArray) : Except String (Array (String × String)) := do
  if d.size < 8 || d.extract 0 8 != Png.pngSignature then throw "not a PNG file"
  let mut pos := 8
  let mut out : Array (String × String) := #[]
  let mut done := false
  for _ in [0:d.size / 12 + 1] do
    if pos + 8 > d.size then throw "the PNG file ends before its image data"
    let len := Png.getBe32 d pos
    let ty := d.extract (pos + 4) (pos + 8)
    if ty == "IDAT".toUTF8 || ty == "IEND".toUTF8 then done := true; break
    if len > 0x7FFFFFFF || pos + 12 + len > d.size then throw "a PNG chunk is truncated"
    let body := d.extract (pos + 8) (pos + 8 + len)
    if ty == "iTXt".toUTF8 && body.extract 0 7 == pngPrefix.toUTF8 then
      if len > 8 * maxField then throw "a source chunk is too large"
      let crc := Png.crcUpdate (Png.crcUpdate 0xFFFFFFFF ty) body ^^^ 0xFFFFFFFF
      if crc.toNat != Png.getBe32 d (pos + 8 + len) then throw "a source chunk has a wrong CRC"
      let some nul := (List.range body.size).find? (fun j => Png.byteAt body j == 0)
        | throw "a malformed source chunk"
      let some kw := String.fromUTF8? (body.extract 0 nul) | throw "a malformed source chunk"
      if Png.byteAt body (nul + 1) != 0 then throw "a compressed source chunk"
      let some l1 := (List.range' (nul + 3) (body.size - nul - 3)).find?
          (fun j => Png.byteAt body j == 0) | throw "a malformed source chunk"
      let some l2 := (List.range' (l1 + 1) (body.size - l1 - 1)).find?
          (fun j => Png.byteAt body j == 0) | throw "a malformed source chunk"
      let some v := String.fromUTF8? (body.extract (l2 + 1) body.size)
        | throw "a source chunk is not UTF-8"
      out := out.push ((kw.drop 7).toString, v)
    pos := pos + 12 + len
  if !done then throw "the PNG file ends before its image data"
  return out

/-- The PNG or APNG file `d` with the source as `iTXt` chunks directly after `IHDR`. Fails if
the file does not start with a signature and an `IHDR` chunk, or already has a source. -/
def withSourcePng (d : ByteArray) (s : Source) : Except String ByteArray := do
  s.validate
  if d.size < 33 || d.extract 0 8 != Png.pngSignature || Png.getBe32 d 8 != 13 ||
      d.extract 12 16 != "IHDR".toUTF8 then throw "not a PNG file with an IHDR chunk"
  if !(← pngFields d).isEmpty then throw "the PNG file already has a source"
  return d.extract 0 33 ++ (← s.pngChunks) ++ d.extract 33 d.size

/-! ### GIF -/

/-- The text of the GIF comment. Fails if a value has a line feed or a carriage return. -/
def Source.gifText (s : Source) : Except String ByteArray := do
  let mut out := (gifMagic ++ "\n").toUTF8
  for (k, v) in s.fields do
    if v.any (fun c => c == '\n' || c == '\r') then
      throw s!"the value of {k} has a line break, which a GIF comment cannot carry"
    out := out ++ s!"{k}={v}\n".toUTF8
  return out

/-- The comment extension holding `text` in sub-blocks of at most 255 bytes. -/
def commentExtension (text : ByteArray) : ByteArray := Id.run do
  let mut out : ByteArray := ⟨#[0x21, 0xFE]⟩
  let mut pos := 0
  for _ in [0:text.size / 255 + 1] do
    if pos ≥ text.size then break
    let e := min text.size (pos + 255)
    out := (out.push (e - pos).toUInt8) ++ text.extract pos e
    pos := e
  return out.push 0

/-- The index just after the global colour table of the GIF file `d`; fails on a wrong header. -/
def gifBodyStart (d : ByteArray) (needs89a : Bool) : Except String Nat := do
  let sig := d.extract 0 6
  if d.size < 13 || !(sig == "GIF89a".toUTF8 || (!needs89a && sig == "GIF87a".toUTF8)) then
    throw "not a GIF file (a GIF89a file for writing)"
  let flags := (Png.byteAt d 10).toNat
  let n := if flags &&& 0x80 != 0 then 3 * (1 <<< ((flags &&& 7) + 1)) else 0
  if 13 + n > d.size then throw "the GIF file ends inside its colour table"
  return 13 + n

/-- The sub-blocks starting at `pos` joined, and the index after their terminator. The result is
cut off after `cap` bytes (the second component says it was). -/
def subBlocks (d : ByteArray) (pos cap : Nat) : Except String (ByteArray × Bool × Nat) := do
  let mut p := pos
  let mut out := ByteArray.empty
  let mut cut := false
  for _ in [0:d.size + 1] do
    if p ≥ d.size then throw "the GIF file is truncated"
    let n := (Png.byteAt d p).toNat
    if n == 0 then return (out, cut, p + 1)
    if p + 1 + n > d.size then throw "the GIF file is truncated"
    if out.size + n > cap then cut := true else out := out ++ d.extract (p + 1) (p + 1 + n)
    p := p + 1 + n
  throw "the GIF file is truncated"

/-- The fields of the `PILean source 1` comment before the first image of a GIF file; none if
there is no such comment. Fails on a truncated file, an oversized source comment, text that is
not UTF-8 or has a carriage return (which the writer refuses), or a second source comment. -/
def gifFields (d : ByteArray) : Except String (Option (Array (String × String))) := do
  let mut pos ← gifBodyStart d false
  let mut found : Option (Array (String × String)) := none
  for _ in [0:d.size + 1] do
    if pos ≥ d.size then throw "the GIF file is truncated"
    let b := Png.byteAt d pos
    if b == 0x21 then
      let label := Png.byteAt d (pos + 1)
      let cap := 16 * maxField
      let (data, cut, next) ← subBlocks d (pos + 2) cap
      let line1 := (gifMagic ++ "\n").toUTF8
      if label == 0xFE && (data.extract 0 line1.size == line1 ||
          (cut && data.extract 0 gifMagic.utf8ByteSize == gifMagic.toUTF8)) then
        if cut then throw "the source comment is too large"
        if found.isSome then throw "the GIF file has two source comments"
        let some text := String.fromUTF8? data | throw "the source comment is not UTF-8"
        if text.contains '\r' then throw "the source comment has a carriage return"
        let lines := (text.splitOn "\n").drop 1
        found := some ((lines.filterMap fun l =>
          match l.splitOn "=" with
          | k :: v :: rest => some (k, "=".intercalate (v :: rest))
          | _ => none).toArray)
      pos := next
    else return found
  return found

/-- The GIF89a file `d` with the source as a comment extension after the global colour table.
Fails if the file is not a GIF89a file or a value has a line break. -/
def withSourceGif (d : ByteArray) (s : Source) : Except String ByteArray := do
  s.validate
  let start ← gifBodyStart d true
  if (← gifFields d).isSome then throw "the GIF file already has a source"
  return d.extract 0 start ++ commentExtension (← s.gifText) ++ d.extract start d.size

/-! ### Dispatch -/

/-- Whether `d` is a PNG, a GIF, or (anything else with `<svg`) an SVG document; none otherwise. -/
def Source.format? (d : ByteArray) : Option String :=
  if d.extract 0 8 == Png.pngSignature then some "png"
  else if d.extract 0 4 == "GIF8".toUTF8 then some "gif"
  else if (findBytes d "<svg".toUTF8).isSome then some "svg" else none

/-- The source of an image file, found by its signature: PNG and APNG (`iTXt`), GIF (comment),
or SVG (UTF-8 text with an `<svg` tag and a `pilean:source` element). Fails with a message if
the input is above `maxInput` bytes, is not one of these formats, is damaged where the source
should be, has no source, or the source is invalid (see `Source.ofFields`). Never runs or follows
anything it reads. -/
def Source.read? (d : ByteArray) : Except String Source := do
  if d.size > maxInput then throw "the input is too large"
  match Source.format? d with
  | some "png" =>
    let kvs ← pngFields d
    if kvs.isEmpty then throw "the PNG file has no PILean source chunks"
    Source.ofFields kvs
  | some "gif" =>
    match ← gifFields d with
    | some kvs => Source.ofFields kvs
    | none => throw "the GIF file has no PILean source comment"
  | some _ =>
    if !ByteArray.validateUTF8 d then throw "the SVG file is not valid UTF-8"
    match ← svgFields d with
    | some kvs => Source.ofFields kvs
    | none => throw "the SVG file has no pilean:source element"
  | none => throw "not a PNG, GIF or SVG file"

/-- The source inserted into an image file of any of the formats (PNG and APNG, GIF, SVG as UTF-8
text), found by its signature; see `withSourcePng`, `withSourceGif` and `withSourceSvg`. -/
def withSource (d : ByteArray) (s : Source) : Except String ByteArray :=
  match Source.format? d with
  | some "png" => withSourcePng d s
  | some "gif" => withSourceGif d s
  | some _ =>
    match String.fromUTF8? d with
    | some t => (withSourceSvg t s).map String.toUTF8
    | none => .error "the SVG file is not valid UTF-8"
  | none => .error "not a PNG, GIF or SVG file"

/-! ### Showing -/

/-- The lines `key: value` of the source in a file, one per field, values with control characters
shown as escapes (`escapeControl`); this is what `lake exe pilean-info` prints. Fails as
`Source.read?` does. -/
def infoLines (d : ByteArray) : Except String (Array String) := do
  let s ← Source.read? d
  return s.fields.map fun (k, v) => k ++ ": " ++ escapeControl v

end PILean.Trust
