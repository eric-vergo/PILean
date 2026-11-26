/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Svg
import PILean.Png
import PILean.Version
import PILean.Pdf.Read
import PILean.Pdf.Object
import PILean.Trust.Sha256

/-!
# Source information in images

A `Source` says which Lean declaration, in which file and line, made an image. It is written into
SVG, PNG, APNG, GIF and PDF files and read back; `docs/TRUST.md` describes the vocabulary.

## Main definitions

* `Trust.Source`: the record; `Trust.Source.validate` says whether it can be written.
* `Trust.Source.svgNodes`, `Trust.withSourceSvg`: the `<title>`, `<desc>` and `<metadata>`
  elements, as nodes and as text inserted into a document.
* `Trust.withSourcePng`, `Trust.withSourceGif`, `Trust.withSourcePdf`, `Trust.withSource`: the
  source inserted into finished PNG, APNG, GIF and PDF files, so every writer gets it without
  change.
* `Trust.Source.read?`: reads the record back from any of the formats.
* `Trust.MotionSummary`, `Trust.MotionSummary.text`, `Trust.MotionSummary.ofText?`,
  `Trust.cycleText`, `Trust.cycleOfText?`: what a file of a motion records about it.
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
* PDF: the document information dictionary, added by an incremental update (a new object, a
  cross-reference section for it and a trailer with `/Info` and `/Prev`), so the bytes of the
  file before it are kept. One key per field, `/PILean:` followed by the key, its value a text
  string (UTF-16BE with its byte order mark, as a hexadecimal string), with `/Title` (the
  declaration) and `/Producer` beside them. The reader follows the newest trailer's `/Info`
  through the cross-reference table with the bounded reader of `PILean.Pdf.Read`.

## References

* PNG Specification, Third Edition (W3C), section "Textual information" (`iTXt`).
* Graphics Interchange Format, Version 89a (CompuServe, 1990), "Comment Extension".
* ISO 32000-1:2008 (PDF 1.7), 7.5.6 "Incremental updates", 14.3.3 "Document information
  dictionary", 7.9.2.2 "Text string type".
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


/-! ### The record of a motion -/

/-- The length of a cycle in seconds as a record writes it, exactly: `n` for a whole number,
`n/d` in lowest terms otherwise. -/
def cycleText (q : Rat) : String := if q.den == 1 then s!"{q.num}" else s!"{q.num}/{q.den}"

/-- The non-negative rational number a record's cycle writes: decimal digits (at most 18, no
leading zero), optionally followed by `/` and a denominator of the same form other than `1`, in
lowest terms, so that the text is exactly `cycleText` of the number; none for anything else. A
cycle whose text this does not read back cannot be recorded (`MotionSummary.recordable`). -/
def cycleOfText? (t : String) : Option Rat := do
  let digits := fun (d : String) =>
    if d.isEmpty || d.length > 18 || !d.all Char.isDigit || (d.length > 1 && d.startsWith "0")
    then none else d.toNat?
  let q : Rat ← match t.splitOn "/" with
    | [n] => (digits n).map fun n => (n : Rat)
    | [n, d] => do
      let n ← digits n
      let d ← digits d
      if d == 0 then none else some ((n : Rat) / (d : Rat))
    | _ => none
  if cycleText q == t then some q else none

/-- What every file of a motion records about it, in its source record (the key `motion`,
`MotionSummary.text`) and in the manifest (the keys `kind`, `keys`, `cycle`, `captions`, `checks`,
`errorsLeft` and `narrow`): the number of its key frames, the length of its cycle in seconds,
exactly, the number of its captions, the level its checks were applied at (`fail`, `warn` or
`ignore`), the number of problems that the strict level (`fail`) treats as errors and that did not
stop it (`errorsLeft`: always `0` at `fail`, where an error stops it), and whether it has a narrow
rendition. Only a motion recorded with `checks` `fail` was stopped by every error its checks
find. -/
structure MotionSummary where
  /-- The number of key frames. -/
  keys : Nat
  /-- The length of one cycle, in seconds. -/
  cycle : Rat
  /-- The number of captions (one per key frame). -/
  captions : Nat
  /-- The level the motion's checks were applied at: `fail`, `warn` or `ignore`. -/
  checks : String := "fail"
  /-- The number of problems the strict level treats as errors that did not stop the motion (in a
  rendition that was written). -/
  errorsLeft : Nat := 0
  /-- Whether the motion has a narrow rendition (files with the suffix `-narrow`). -/
  narrow : Bool := false
  deriving BEq, Repr, Inhabited

/-- Whether the record says the motion was checked strictly: at the level `fail`, no error left. -/
def MotionSummary.strict (m : MotionSummary) : Bool := m.checks == "fail" && m.errorsLeft == 0

/-- The levels a motion's checks can be applied at, as a record writes them. -/
def motionCheckWords : Array String := #["fail", "warn", "ignore"]

/-- The record of a motion as one value:
`keys=3;cycle=59/10;captions=3;checks=fail;errorsLeft=0;narrow=no`. -/
def MotionSummary.text (m : MotionSummary) : String :=
  s!"keys={m.keys};cycle={cycleText m.cycle};captions={m.captions};checks={m.checks};\
    errorsLeft={m.errorsLeft};narrow={if m.narrow then "yes" else "no"}"

/-- The record of a motion `MotionSummary.text` writes, read back: exactly its six fields in its
order, the numbers in decimal (at most nine digits, no leading zero), the cycle as
`cycleOfText?` reads it, a known level; none for anything else. -/
def MotionSummary.ofText? (t : String) : Option MotionSummary := do
  let num := fun (d : String) =>
    if d.isEmpty || d.length > 9 || !d.all Char.isDigit || (d.length > 1 && d.startsWith "0")
    then none else d.toNat?
  match t.splitOn ";" with
  | [k, c, n, l, e, w] =>
    let keys ← num (← (k.dropPrefix? "keys=").map (·.toString))
    let cycle ← cycleOfText? (← (c.dropPrefix? "cycle=").map (·.toString))
    let captions ← num (← (n.dropPrefix? "captions=").map (·.toString))
    let checks := (← (l.dropPrefix? "checks=").map (·.toString))
    if !motionCheckWords.contains checks then none
    let errorsLeft ← num (← (e.dropPrefix? "errorsLeft=").map (·.toString))
    let narrow ← match (← (w.dropPrefix? "narrow=").map (·.toString)) with
      | "yes" => some true
      | "no" => some false
      | _ => none
    if keys == 0 then none
    if checks == "fail" && errorsLeft != 0 then none
    let m : MotionSummary := { keys, cycle, captions, checks, errorsLeft, narrow }
    if m.text == t then some m else none
  | _ => none

/-- Whether the record of a motion can be written and read back: its text reads back as itself
(a cycle whose numerator or denominator has more than 18 digits cannot be recorded). -/
def MotionSummary.recordable (m : MotionSummary) : Bool := MotionSummary.ofText? m.text == some m

/-- The keys of the fields, in the order they are written. -/
def keys : Array String :=
  #["module", "decl", "file", "line", "column", "repo", "commit", "version", "fingerprint",
    "standing", "theorems", "motion"]

/-- The key an earlier writer gave the theorems of a figure's standing; the readers take it for
`theorems`. -/
def oldTheoremsKey : String := "proves"

/-- A recorded standing as the readers take it: `proved`, the word an earlier writer gave the
standing of a figure with a linked theorem, reads as `linked`; any other word is kept. -/
def readStanding (w : String) : String := if w == "proved" then "linked" else w

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
  /-- The figure's standing as the build recorded it: `linked` or `illustration`
  (`PILean.Trust.Standing.word`). -/
  standing : Option String := none
  /-- For a linked figure, the theorems linked to it, by full name (as Lean writes a name, so
  with `«` and `»` around a component that needs them), in order; written as an escaped list
  (`theoremsText`). -/
  theorems : Option (Array String) := none
  /-- For a file of a motion, the record of the motion (`MotionSummary`), written as one value
  (`MotionSummary.text`). -/
  motion : Option MotionSummary := none
deriving BEq, Repr, Inhabited

/-- The characters a name is escaped from in a source record's list of theorems
(`theoremsText`): `%`, `,`, `[`, `]`, the backslash (which an inert SVG attribute may not hold,
`PILean.Svg.Inert`) and the control characters below 32. -/
def escapedInList (c : Char) : Bool :=
  c == '%' || c == ',' || c == '[' || c == ']' || c == '\\' || c.val < 32

/-- The two uppercase hexadecimal digits of a number below 256. -/
def hex2 (n : Nat) : String :=
  let d := fun (k : Nat) => if k < 10 then Char.ofNat (48 + k) else Char.ofNat (55 + k)
  String.ofList [d (n / 16 % 16), d (n % 16)]

/-- The theorems of a linked figure as a source record writes them: `[`, the names separated by
`,`, `]`, each name with every character of `escapedInList` written `%XX` (its code in two
uppercase hexadecimal digits), such as `[A.b,C.«d e»]`. The text has no backslash, so an SVG
that carries it stays inert, and every list of names has exactly one such text, which
`theoremsOfText` reads back. -/
def theoremsText (ts : Array String) : String :=
  "[" ++ ",".intercalate (ts.toList.map fun t => t.foldl (init := "") fun out c =>
    if escapedInList c then out ++ "%" ++ hex2 c.val.toNat else out.push c) ++ "]"

/-- A name of a record's list read back: every `%XX` (two uppercase hexadecimal digits) whose
character is one of `escapedInList` becomes that character; any other `%`, and any character of
`escapedInList` written as it is, is an error. -/
def unescapeListName (t : String) : Except String String := do
  let cs := t.toList.toArray
  let hexVal := fun (c : Char) => if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55) else none
  let mut out := ""
  let mut i := 0
  for _ in [0:cs.size] do
    if i ≥ cs.size then break
    let c := cs[i]!
    if c == '%' then
      match (cs[i + 1]?.bind hexVal), (cs[i + 2]?.bind hexVal) with
      | some a, some b =>
        let d := Char.ofNat (16 * a + b)
        if !escapedInList d then throw s!"an escape of a character that is not escaped in {t}"
        out := out.push d
        i := i + 3
      | _, _ => throw s!"a malformed escape in {t}"
    else if escapedInList c then throw s!"a character that must be escaped in {t}"
    else
      out := out.push c
      i := i + 1
  return out

/-- The theorems in the form earlier writers gave them: names separated by single spaces, each
non-empty, without white space and not beginning with `[` (as no name Lean writes does). Fails on
any other text. -/
def theoremsOfSpaced (v : String) : Except String (Array String) :=
  let ts := (v.splitOn " ").toArray
  if v.isEmpty || ts.any (fun t => t.isEmpty || t.any Char.isWhitespace || t.startsWith "[") then
    .error "the theorems are not names separated by single spaces"
  else .ok ts

/-- The theorems a source record's value lists: a value that begins with `[` is the list
`theoremsText` writes (it must end with `]`; `[]` is the empty list); any other value is the form
earlier writers gave (`theoremsOfSpaced`). The two cannot be confused: a name as Lean writes it
never begins with `[` (a component that would is written between `«` and `»`). -/
def theoremsOfText (v : String) : Except String (Array String) := do
  if v.startsWith "[" then
    unless v.endsWith "]" && v.length ≥ 2 do throw "the list of theorems is not closed"
    let inner := ((v.drop 1).dropEnd 1).toString
    if inner.isEmpty then return #[]
    (inner.splitOn ",").toArray.mapM unescapeListName
  else theoremsOfSpaced v

/-- The fields in writing order as `(key, value)`; absent options are left out. -/
def Source.fields (s : Source) : Array (String × String) :=
  #[("module", s.module), ("decl", s.decl), ("file", s.file), ("line", toString s.line),
    ("column", toString s.column)] ++
  (match s.repo with | some r => #[("repo", r)] | none => #[]) ++
  (match s.commit with | some r => #[("commit", r)] | none => #[]) ++
  #[("version", s.version)] ++
  (match s.fingerprint with | some r => #[("fingerprint", r)] | none => #[]) ++
  (match s.standing with | some r => #[("standing", r)] | none => #[]) ++
  (match s.theorems with | some ts => #[("theorems", theoremsText ts)] | none => #[]) ++
  (match s.motion with | some m => #[("motion", m.text)] | none => #[])

/-- Whether a recorded standing and list of theorems are well formed: no standing and no
theorems, `illustration` without theorems, or `linked` with a non-empty list of distinct names,
each non-empty and made of characters XML can carry (`xmlChar`). Any other pair is refused. -/
def standingOk (standing : Option String) (theorems : Option (Array String)) : Bool :=
  match standing, theorems with
  | none, none => true
  | some "illustration", none => true
  | some "linked", some ts =>
    !ts.isEmpty && ts.all (fun t => !t.isEmpty && t.all xmlChar) &&
      ts.toList.eraseDups.length == ts.size
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
  if !standingOk s.standing s.theorems then
    throw "the standing is not linked with its theorems or illustration without any"
  if let some m := s.motion then
    if !m.recordable then
      throw s!"the record of the motion ({m.text}) does not read back: its cycle has more than 18 \
        digits in its numerator or denominator"

/-- The record from a list of `(key, value)` pairs, as the readers collect them: unknown keys are
ignored, a known key twice is an error, a value above `maxField` bytes or with a character XML
cannot carry (so one the writers refuse) is an error, `line` and
`column` are decimal numbers of at most nine digits, a fingerprint is 64 lowercase hexadecimal
digits, the theorems are a list in the record's form or in the earlier one (`theoremsOfText`;
under the earlier key `proves`, in the earlier form only), the standing and its theorems are well
formed (`standingOk`; a standing `proved` reads as `linked`, `readStanding`), and `module`, `decl`,
`file`, `line`, `column` and `version` must be present. -/
def Source.ofFields (kvs : Array (String × String)) : Except String Source := do
  let mut seen : Array String := #[]
  for (k, v) in kvs do
    if keys.contains k || k == oldTheoremsKey then
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
  let standing := (find "standing").map readStanding
  let theorems ← match find "theorems", find oldTheoremsKey with
    | some t, none => some <$> theoremsOfText t
    | none, some t => some <$> theoremsOfSpaced t
    | none, none => pure none
    | some _, some _ => throw s!"the keys theorems and {oldTheoremsKey} occur together"
  if !standingOk standing theorems then
    throw "the standing is not linked with its theorems or illustration without any"
  let motion ← match find "motion" with
    | some t => match MotionSummary.ofText? t with
      | some mo => pure (some mo)
      | none => throw "the record of the motion is malformed"
    | none => pure none
  return { module := m, decl := d, file := f, line := l, column := c, repo := find "repo",
           commit := find "commit", version := v, fingerprint := fp, standing, theorems, motion }

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

/-- The index just after the root's leading `title` element and the `desc` element after it,
when the root's first child is a `title` (or a `desc`); `e`, the end of the root's tag, otherwise. -/
def afterLeadingTitle (d : ByteArray) (e : Nat) : Nat := Id.run do
  let skip := fun (i : Nat) => Id.run do
    let mut j := i
    for _ in [0:d.size] do
      if j < d.size && (Png.byteAt d j == 32 || Png.byteAt d j == 10 || Png.byteAt d j == 13 ||
          Png.byteAt d j == 9) then j := j + 1
      else break
    return j
  let element := fun (i : Nat) (name : String) =>
    let j := skip i
    if (d.extract j (j + name.length + 2)) == ("<" ++ name ++ ">").toUTF8 then
      (findBytes d ("</" ++ name ++ ">").toUTF8 j).map (· + name.length + 3)
    else none
  let mut pos := e + 1
  if let some p := element pos "title" then pos := p
  if let some p := element pos "desc" then pos := p
  return pos - 1

/-- `svg` with the source information as children of the root element, indented like the
writer's output: the first children, or after the root's leading `title` and `desc` when the
document has them (a motion's own title, which then stays the picture's accessible name, the
first `title` child of the root). Fails if the text has no `<svg ` root tag or already has a
source. -/
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
    else
      let at_ := afterLeadingTitle d e
      d.extract 0 (at_ + 1) ++ "\n".toUTF8 ++ nodes.toUTF8 ++ d.extract (at_ + 1) d.size
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

/-! ### PDF -/

/-- The prefix of the keys of the information dictionary's source fields. -/
def pdfPrefix : String := "PILean:"

/-- The source fields of a PDF file's information dictionary (the newest trailer's `/Info`, keys
`/PILean:…`); none if the file has no information dictionary or no such key. Fails if the file is
not a PDF file with a classic cross-reference table that the bounded reader can read
(`Pdf.readXref`), or a source value is not a text string (`Pdf.textString?`). -/
def pdfFields (d : ByteArray) : Except String (Option (Array (String × String))) := do
  let x ← Pdf.readXref {} d
  match ← Pdf.infoDict? {} d x with
  | some (.dict kvs) =>
    let ours := kvs.filter (·.1.startsWith pdfPrefix)
    if ours.isEmpty then return none
    let mut out : Array (String × String) := #[]
    for (k, v) in ours do
      let .str b := v | throw s!"the value of {k} is not a string"
      if b.size > 2 * maxField + 2 then throw s!"the value of {k} is too long"
      let some t := Pdf.textString? b | throw s!"the value of {k} is not a text string"
      out := out.push ((k.drop pdfPrefix.length).toString, t)
    return some out
  | _ => return none

/-- The information dictionary of a source: `/Title` (the declaration), `/Producer` (PILean and
its version) and one `/PILean:key` per field, each a text string. -/
def Source.pdfInfo (s : Source) : Pdf.Obj :=
  .dict (#[("Title", .str (Pdf.utf16Text s.decl)),
    ("Producer", .str (Pdf.utf16Text s!"PILean {s.version}"))] ++
    s.fields.map fun (k, v) => (pdfPrefix ++ k, .str (Pdf.utf16Text v)))

/-- The PDF file `d` with the source as its information dictionary, added by an incremental
update: the object (numbered `/Size`), a cross-reference section with it, and a trailer with
`/Size`, `/Root`, `/Info`, `/Prev` and `/ID` (the first string kept; the second the first 16
bytes of the SHA-256 of the file and the object). Fails if the file cannot be read by the bounded
reader, its trailer has no `/Size` or `/Root`, or it already has a source. -/
def withSourcePdf (d : ByteArray) (s : Source) : Except String ByteArray := do
  s.validate
  let x ← Pdf.readXref {} d
  if (← pdfFields d).isSome then throw "the PDF file already has a source"
  let some n := (x.trailer.get? "Size").bind Pdf.Value.nat? | throw "the trailer has no /Size"
  let some (.ref r g) := x.trailer.get? "Root" | throw "the trailer has no /Root"
  let some prev := x.sections[0]? | throw "no cross-reference section"
  let body := d ++ (if Png.byteAt d (d.size - 1) == 10 then .empty else "\n".toUTF8)
  let off := body.size
  let obj := s!"{n} 0 obj\n{s.pdfInfo.write}\nendobj\n".toUTF8
  let first := match x.trailer.get? "ID" with
    | some (.arr #[.str a, _]) => a
    | _ => (Sha256.hash d).extract 0 16
  let second := (Sha256.hash (body ++ obj)).extract 0 16
  let xref := off + obj.size
  let tail := s!"xref\n{n} 1\n{Pdf.pad10 off} 00000 n \ntrailer\n<< /Size {n + 1} /Root {r} {g} R \
    /Info {n} 0 R /Prev {prev} /ID [{Pdf.hexString first} {Pdf.hexString second}] >>\n\
    startxref\n{xref}\n%%EOF\n"
  return body ++ obj ++ tail.toUTF8

/-! ### Dispatch -/

/-- Whether `d` is a PNG, a GIF, a PDF (`%PDF-` first), or (anything else with `<svg`) an SVG
document; none otherwise. -/
def Source.format? (d : ByteArray) : Option String :=
  if d.extract 0 8 == Png.pngSignature then some "png"
  else if d.extract 0 4 == "GIF8".toUTF8 then some "gif"
  else if d.extract 0 5 == "%PDF-".toUTF8 then some "pdf"
  else if (findBytes d "<svg".toUTF8).isSome then some "svg" else none

/-- The source of an image file, found by its signature: PNG and APNG (`iTXt`), GIF (comment),
PDF (information dictionary), or SVG (UTF-8 text with an `<svg` tag and a `pilean:source`
element). Fails with a message if
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
  | some "pdf" =>
    match ← pdfFields d with
    | some kvs => Source.ofFields kvs
    | none => throw "the PDF file has no PILean source in its information dictionary"
  | some _ =>
    if !ByteArray.validateUTF8 d then throw "the SVG file is not valid UTF-8"
    match ← svgFields d with
    | some kvs => Source.ofFields kvs
    | none => throw "the SVG file has no pilean:source element"
  | none => throw "not a PNG, GIF, PDF or SVG file"

/-- The source inserted into an image file of any of the formats (PNG and APNG, GIF, PDF, SVG as
UTF-8 text), found by its signature; see `withSourcePng`, `withSourceGif`, `withSourcePdf` and
`withSourceSvg`. -/
def withSource (d : ByteArray) (s : Source) : Except String ByteArray :=
  match Source.format? d with
  | some "png" => withSourcePng d s
  | some "gif" => withSourceGif d s
  | some "pdf" => withSourcePdf d s
  | some _ =>
    match String.fromUTF8? d with
    | some t => (withSourceSvg t s).map String.toUTF8
    | none => .error "the SVG file is not valid UTF-8"
  | none => .error "not a PNG, GIF, PDF or SVG file"

/-! ### Showing -/

/-- The lines `key: value` of the source in a file, one per field, values with control characters
shown as escapes (`escapeControl`); this is what `lake exe pilean-info` prints. Fails as
`Source.read?` does. -/
def infoLines (d : ByteArray) : Except String (Array String) := do
  let s ← Source.read? d
  return s.fields.map fun (k, v) => k ++ ": " ++ escapeControl v

end PILean.Trust
