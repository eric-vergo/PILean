/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Trust.Json
import PILean.Trust.Fingerprint

/-!
# The manifest of a build

`manifest.json` lists the files `pilean-build` wrote: one `ManifestEntry` per file, sorted by
path. `ManifestEntry.toJson` writes an entry and `Manifest.parse` reads a manifest back,
treating it as untrusted: every key must be present with a value of the right type, the paths
must be safe (`safePath`), and the numbers of entries and of bytes are bounded.

## Main definitions

* `ManifestEntry`, `Manifest.render`, `Manifest.parse`
* `sanitize`, `safePath`, `outputPath`: the file names
-/

namespace PILean.Trust

/-- The name of the manifest file in the output directory. -/
def manifestName : String := "manifest.json"

/-- The value of the manifest's `format` key. -/
def manifestFormat : String := "pilean-manifest-1"

/-- The most entries of a build or of a manifest. -/
def maxEntries : Nat := 4096

/-- The most files a manifest lists (a figure can have several outputs). -/
def maxManifestFiles : Nat := 65536

/-- The largest output file, in bytes (64 MiB): the largest file whose source record
`Source.read?` reads (`maxInput`), so that every file a build writes can be verified. The
builder holds the finished file, source record included, to it. -/
def maxOutputBytes : Nat := maxInput

/-- Whether the PNG file `d` is animated: an `acTL` chunk comes before its first `IDAT` chunk.
Only the chunk lengths and types are read; none if the walk does not reach an `IDAT` chunk. -/
def pngAnimated? (d : ByteArray) : Option Bool := Id.run do
  let mut pos := 8
  for _ in [0:d.size / 12 + 1] do
    if pos + 12 > d.size then return none
    let len := Png.getBe32 d pos
    let ty := d.extract (pos + 4) (pos + 8)
    if ty == "acTL".toUTF8 then return some true
    if ty == "IDAT".toUTF8 then return some false
    pos := pos + 12 + len
  return none

/-- The manifest's name for the format of the bytes `d`, read from them: `svg`, `gif`, `pdf`,
`png`, or `apng` for a PNG file with an `acTL` chunk before its image data (`Source.format?` tells
the signatures apart; `pngAnimated?` the two kinds of PNG). None if it is none of these. -/
def detectedFormat? (d : ByteArray) : Option String :=
  match Source.format? d with
  | some "png" => (pngAnimated? d).map fun a => if a then "apng" else "png"
  | f => f

/-- A file of a build, as the manifest lists it. -/
structure ManifestEntry where
  /-- The path relative to the output directory, with `/` as separator. -/
  path : String
  /-- The format: `svg`, `png`, `apng`, `gif` or `pdf`. -/
  format : String
  /-- The size of the file in bytes. -/
  bytes : Nat
  /-- The SHA-256 of the file's bytes, in hexadecimal. -/
  sha256 : String
  /-- The fingerprint recorded in the file. -/
  fingerprint : String
  /-- The module of the declaration that draws the figure. -/
  module : String
  /-- The declaration's name. -/
  decl : String
  /-- The declaration's file, relative to the repository. -/
  file : String
  /-- The declaration's line. -/
  line : Nat
  /-- The declaration's column. -/
  column : Nat
  /-- The version of PILean. -/
  version : String
  /-- The repository, if the build was given one. -/
  repo : Option String := none
  /-- The commit, if the build was given one. -/
  commit : Option String := none
  /-- For an SVG file a page can put inline: the light colours (`#rrggbb`) paired with the dark
  ones that the page's dark theme restyles them to (`Output.theme`); empty otherwise. -/
  darkColours : Array (String × String) := #[]
  /-- The tint opacities paired the same way. -/
  darkOpacities : Array (String × String) := #[]
  /-- The figure's standing recorded in the file (`proved` or `illustration`), if it has one. -/
  standing : Option String := none
  /-- The theorems of a proved figure recorded in the file, separated by single spaces. -/
  proves : Option String := none
deriving BEq, Repr, Inhabited

/-- A character a file name may have: a letter, a digit, `.`, `_`, `-`; all ASCII. -/
def nameChar (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') || c == '.' || c == '_' ||
    c == '-'

/-- The string with every other character replaced by `_`. -/
def sanitize (s : String) : String := s.map fun c => if nameChar c then c else '_'

/-- Whether a manifest path is safe to join to a directory: not empty, not longer than 1024
bytes, only the characters of `nameChar` and `/`, no component empty, `.` or `..` (so it is not
absolute and does not climb), so no backslash and no drive letter either. -/
def safePath (p : String) : Bool :=
  !p.isEmpty && p.utf8ByteSize ≤ 1024 && p.all (fun c => nameChar c || c == '/') &&
    (p.splitOn "/").all fun c => !c.isEmpty && c != "." && c != ".."

/-- The path of an output below the output directory: the module's components as directories
(dots as slashes), then the declaration (without the module as a prefix) and the output's suffix
as the file stem, and the format's extension; everything outside `nameChar` replaced, and the
result must be `safePath`. -/
def outputPath (e : SourceData) (o : Output) : Except String String := do
  let decl := if e.decl.startsWith (e.module ++ ".") then
      (e.decl.drop (e.module.length + 1)).toString else e.decl
  let dirs := (e.module.splitOn ".").map sanitize
  let stem := sanitize decl ++ sanitize o.name ++ "." ++ o.format.ext
  let p := "/".intercalate (dirs ++ [stem])
  if safePath p then return p
  else throw s!"the output of {e.module}.{e.decl} has no safe file name"

/-- The manifest text of an entry: one line, keys in a fixed order, strings escaped. -/
def ManifestEntry.render (m : ManifestEntry) : String :=
  let s := fun (k v : String) => s!"\"{k}\":\"{Json.escape v}\""
  let n := fun (k : String) (v : Nat) => s!"\"{k}\":{v}"
  let opt := fun (k : String) (v : Option String) =>
    match v with | some v => [s k v] | none => []
  let pairs := fun (k : String) (v : Array (String × String)) =>
    if v.isEmpty then [] else
      [s!"\"{k}\":[" ++ ",".intercalate (v.toList.map fun (a, b) =>
        s!"[\"{Json.escape a}\",\"{Json.escape b}\"]") ++ "]"]
  "{" ++ ",".intercalate ([s "path" m.path, s "format" m.format, n "bytes" m.bytes,
    s "sha256" m.sha256, s "fingerprint" m.fingerprint, s "module" m.module, s "decl" m.decl,
    s "file" m.file, n "line" m.line, n "column" m.column, s "version" m.version] ++
    opt "repo" m.repo ++ opt "commit" m.commit ++ pairs "darkColours" m.darkColours ++
    pairs "darkOpacities" m.darkOpacities ++ opt "standing" m.standing ++
    opt "proves" m.proves) ++ "}"

/-- The manifest text of a list of entries (in the given order). -/
def Manifest.render (es : Array ManifestEntry) : String :=
  "{\"format\":\"" ++ manifestFormat ++ "\",\"files\":[" ++
    (if es.isEmpty then "" else "\n  " ++ ",\n  ".intercalate (es.toList.map (·.render)) ++ "\n") ++
    "]}\n"

/-- The entry a JSON object describes; every key but `repo`, `commit`, the colour pairs,
`standing` and `proves` must be there with a string or a number as its kind, the hashes in the
form of `isFingerprint`, the format one of `svg`, `png`, `apng`, `gif`, `pdf`, the path `safePath`, and
the standing with its theorems well formed (`standingOk`). -/
def ManifestEntry.ofJson (j : Json) : Except String ManifestEntry := do
  let str := fun (k : String) => do
    match j.get? k with
    | some (.str s) => return s
    | _ => throw s!"the key {k} must be a string"
  let num := fun (k : String) => do
    match j.get? k with
    | some (.num n) => return n
    | _ => throw s!"the key {k} must be a number"
  let opt := fun (k : String) => do
    match j.get? k with
    | none => return none
    | some (.str s) => return some s
    | _ => throw s!"the key {k} must be a string"
  let pairs := fun (k : String) => do
    match j.get? k with
    | none => return #[]
    | some (.arr xs) => xs.mapM fun
      | .arr #[.str a, .str b] => return (a, b)
      | _ => throw s!"the key {k} must be a list of pairs of strings"
    | _ => throw s!"the key {k} must be a list of pairs of strings"
  let m : ManifestEntry := {
    path := ← str "path", format := ← str "format", bytes := ← num "bytes",
    sha256 := ← str "sha256", fingerprint := ← str "fingerprint", module := ← str "module",
    decl := ← str "decl", file := ← str "file", line := ← num "line", column := ← num "column",
    version := ← str "version", repo := ← opt "repo", commit := ← opt "commit",
    darkColours := ← pairs "darkColours", darkOpacities := ← pairs "darkOpacities",
    standing := ← opt "standing", proves := ← opt "proves" }
  if !standingOk m.standing m.proves then
    throw "the standing is not proved with its theorems or illustration without any"
  if !safePath m.path then throw s!"the path {m.path} is not a safe relative path"
  if (Format.ofName? m.format).isNone then throw s!"the format {m.format} is unknown"
  if !isFingerprint m.sha256 || !isFingerprint m.fingerprint then
    throw "a hash is not 64 lowercase hexadecimal digits"
  return m

/-- Reads a manifest: its text must be JSON as `Json.parse` reads it, an object with the right
`format` and a `files` array of at most `maxManifestFiles` entries that `ManifestEntry.ofJson`
accepts, with no path twice. -/
def Manifest.parse (d : ByteArray) : Except String (Array ManifestEntry) := do
  let j ← Json.parse d
  match j.get? "format" with
  | some (.str f) => if f != manifestFormat then throw s!"unknown manifest format {f}"
  | _ => throw "the manifest has no format"
  let some (.arr files) := j.get? "files" | throw "the manifest has no files list"
  if files.size > maxManifestFiles then throw "the manifest lists too many files"
  let mut out : Array ManifestEntry := #[]
  let mut seen : Std.HashSet String := {}
  for f in files do
    let m ← ManifestEntry.ofJson f
    if seen.contains m.path then throw s!"the path {m.path} is listed twice"
    seen := seen.insert m.path
    out := out.push m
  return out

end PILean.Trust
