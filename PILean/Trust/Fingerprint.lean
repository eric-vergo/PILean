/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Trust.Figure
import PILean.Trust.Provenance
import PILean.Trust.Sha256
import PILean.Trust.Renderer

/-!
# Fingerprints of figures

A fingerprint is the SHA-256, as 64 lowercase hexadecimal digits, of one byte string that binds
what is drawn to the declaration that draws it.

## The serialisation

The byte string is the header `PILean fingerprint 2` and a line feed, then nine fields in this
order: module, declaration, file, line, column, library version, renderer (`rendererId`, which
changes with any change to the code that turns a figure into bytes, and with the text engine for
an engine other than the built-in lettering, `rendererWith`), source-text hash,
specification.
Each field is written as its length in bytes, a 64-bit unsigned number in big-endian order,
followed by its bytes. The text fields are UTF-8; the line and the column are their decimal
digits; the source-text hash is the 64 hexadecimal digits of the SHA-256 of the declaration's
source text; the specification is the `Output.spec` of the output.

## Main definitions

* `SourceData`: the recorded source of a declaration
* `fingerprint`: the fingerprint of a specification and a source
* `FigureEntry`: a declaration with its source data and a thunk producing its outputs
* `FigureEntry.source`: the `Source` record of one output
* `FigureEntry.standing`: the figure's standing (`Standing`), as `figures%` set it
-/

namespace PILean.Trust

/-- What is recorded about a declaration that draws a figure. -/
structure SourceData where
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
  /-- The SHA-256 of the declaration's source text, 64 lowercase hexadecimal digits. -/
  sourceHash : String
deriving BEq, Repr, Inhabited

/-- The header of the byte string a fingerprint is taken of. -/
def fingerprintHeader : String := "PILean fingerprint 2\n"

/-- The field as eight bytes of its length (big-endian) and then its bytes. -/
def lengthPrefixed (b : ByteArray) : ByteArray := Id.run do
  let n := b.size
  let mut out := ByteArray.empty
  for i in [0:8] do
    out := out.push ((n >>> (8 * (7 - i))) % 256).toUInt8
  return out ++ b

/-- The byte string whose SHA-256 is the fingerprint (see the module docstring). -/
def fingerprintInput (spec : ByteArray) (d : SourceData) (version : String := PILean.version)
    (renderer : String := rendererId) : ByteArray :=
  fingerprintHeader.toUTF8 ++ lengthPrefixed d.module.toUTF8 ++ lengthPrefixed d.decl.toUTF8 ++
    lengthPrefixed d.file.toUTF8 ++ lengthPrefixed (toString d.line).toUTF8 ++
    lengthPrefixed (toString d.column).toUTF8 ++ lengthPrefixed version.toUTF8 ++
    lengthPrefixed renderer.toUTF8 ++ lengthPrefixed d.sourceHash.toUTF8 ++ lengthPrefixed spec

/-- The fingerprint of an output specification and the source data of its declaration: the
lowercase hexadecimal SHA-256 of `fingerprintInput`. -/
def fingerprint (spec : ByteArray) (d : SourceData) (version : String := PILean.version)
    (renderer : String := rendererId) : String :=
  Sha256.hex (Sha256.hash (fingerprintInput spec d version renderer))

/-- A declaration that draws figures: its recorded source and the thunk that renders it. -/
structure FigureEntry extends SourceData where
  /-- The files the declaration is rendered to. -/
  outputs : Unit → Array Output

/-- The standing of the entry's figure: the standing `figures%` set on its outputs (the first
output's; every output of an entry `figures%` makes has the same), an unmarked illustration for an
entry without outputs. -/
def FigureEntry.standing (e : FigureEntry) : Standing :=
  ((e.outputs ())[0]?.map (·.standing)).getD (.illustration false)

/-- The standing and the theorems as a source record and a manifest write them: the word of
`Standing.word`, and for a linked figure its theorems separated by single spaces. -/
def Standing.fields (s : Standing) : Option String × Option String :=
  (some s.word, if s.theorems.isEmpty then none else some (" ".intercalate s.theorems.toList))

/-- The `Source` record written into the file of an output: the recorded source, the library
version, the fingerprint of the output's specification, the output's standing with its theorems
(`Standing.fields`), and the repository and commit if given. The standing is not part of the
fingerprint, which identifies the drawing and its declaration; it is part of the file, so its
SHA-256 in the manifest covers it. -/
def FigureEntry.source (e : FigureEntry) (o : Output) (repo commit : Option String := none) :
    Source :=
  { module := e.module, decl := e.decl, file := e.file, line := e.line, column := e.column,
    repo, commit, version := PILean.version,
    fingerprint := some (fingerprint o.spec e.toSourceData
      (renderer := rendererWith o.textEngine)),
    standing := o.standing.fields.1, theorems := o.standing.fields.2 }

end PILean.Trust
