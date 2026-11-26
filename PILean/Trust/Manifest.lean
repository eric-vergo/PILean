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
* `motionKeyProblem?`: the key stills a motion's manifest entries must list
* `sanitize`, `safePath`, `outputPath`: the file names
-/

namespace PILean.Trust

/-- The name of the manifest file in the output directory. -/
def manifestName : String := "manifest.json"

/-- The value of the manifest's `format` key. In this format the theorems of a linked figure are
a JSON array of strings, the files of a motion record it (the keys `kind`, `keys`, `cycle`,
`captions`, `checks`, `errorsLeft` and `narrow`), and an entry with a key the format does not have is refused. -/
def manifestFormat : String := "pilean-manifest-4"

/-- The format before motions, which `Manifest.parse` reads too: the same entries without the keys
of a motion; other keys are ignored, as its reader ignored them. -/
def previousManifestFormat : String := "pilean-manifest-3"

/-- The earlier format of the manifests, which `Manifest.parse` reads too: the same entries, with
the theorems of a linked figure as one string of names separated by single spaces. -/
def spacedManifestFormat : String := "pilean-manifest-2"

/-- The format of the manifests the first writer made, which `Manifest.parse` reads too: as
`spacedManifestFormat`, with the standing of a figure with a linked theorem written `proved` and
its theorems under the key `proves` (read as `linked` and `theorems`). -/
def oldManifestFormat : String := "pilean-manifest-1"

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
  /-- The figure's standing recorded in the file (`linked` or `illustration`), if it has one. -/
  standing : Option String := none
  /-- The theorems of a linked figure recorded in the file, by full name, in order. -/
  theorems : Option (Array String) := none
  /-- For a file of a motion: its record (`Output.motion`, the same as the file's source record
  holds), written as the keys `kind` (`motion`), `keys`, `cycle`, `captions`, `checks` and
  `errorsLeft` and `narrow`. -/
  motion : Option MotionSummary := none
deriving BEq, Repr, Inhabited

/-- The keys an entry of a manifest of the format `manifestFormat` may have. -/
def manifestKeys : Array String :=
  #["path", "format", "bytes", "sha256", "fingerprint", "module", "decl", "file", "line", "column",
    "version", "repo", "commit", "darkColours", "darkOpacities", "standing", "theorems", "kind",
    "keys", "cycle", "captions", "checks", "errorsLeft", "narrow"]

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
    (match m.theorems with
      | some ts => [s!"\"theorems\":[" ++
          ",".intercalate (ts.toList.map fun t => s!"\"{Json.escape t}\"") ++ "]"]
      | none => []) ++
    (match m.motion with
      | some mo => [s "kind" "motion", n "keys" mo.keys, s "cycle" (cycleText mo.cycle),
          n "captions" mo.captions, s "checks" mo.checks,
          n "errorsLeft" mo.errorsLeft, s!"\"narrow\":{if mo.narrow then "true" else "false"}"]
      | none => [])) ++ "}"

/-- The manifest text of a list of entries (in the given order). -/
def Manifest.render (es : Array ManifestEntry) : String :=
  "{\"format\":\"" ++ manifestFormat ++ "\",\"files\":[" ++
    (if es.isEmpty then "" else "\n  " ++ ",\n  ".intercalate (es.toList.map (·.render)) ++ "\n") ++
    "]}\n"

/-- The entry a JSON object of a manifest describes; every key but `repo`, `commit`, the colour
pairs, `standing` and `theorems` (or `proves`, read as `theorems`) and the keys of a motion must be
there with a string or a number as its kind, the hashes in the form of `isFingerprint`, the format
one of `svg`, `png`, `apng`, `gif`, `pdf`, the path `safePath`, and the standing with its theorems
well formed (`standingOk`; a standing `proved` reads as `linked`, `readStanding`). The theorems
are an array of strings when `spaced` is false (`manifestFormat` and `previousManifestFormat`),
and one string of names separated by single spaces when it is true (the earlier formats,
`theoremsOfSpaced`). With `current` (`manifestFormat`), a key outside `manifestKeys` is refused,
and the keys of a motion are read: `kind` is absent or `motion`, and with `motion` the number of
keys (at least one) and of captions, the cycle (`cycleOfText?`), the check level (`fail`, `warn`
or `ignore`), `errorsLeft` (a number, `0` at the level `fail`) and `narrow` (a boolean) must be there, and without it none of them; the earlier
formats have no motion, and their other keys are ignored. -/
def ManifestEntry.ofJson (j : Json) (spaced : Bool := false) (current : Bool := false) :
    Except String ManifestEntry := do
  if current then
    if let .obj kvs := j then
      if let some (k, _) := kvs.find? (!manifestKeys.contains ·.1) then
        throw s!"the key {k} is not one of this format"
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
  let theorems ← match j.get? "theorems", j.get? oldTheoremsKey, spaced with
    | some (.str t), none, true => some <$> theoremsOfSpaced t
    | none, some (.str t), true => some <$> theoremsOfSpaced t
    | some (.arr xs), none, false => some <$> xs.mapM fun
      | .str t => pure t
      | _ => throw "the key theorems must be a list of strings"
    | none, none, _ => pure none
    | some _, some _, _ => throw s!"the keys theorems and {oldTheoremsKey} occur together"
    | none, some _, false => throw s!"the key {oldTheoremsKey} belongs to an earlier format"
    | _, _, true => throw "the key theorems must be a string in this format"
    | _, _, false => throw "the key theorems must be a list of strings"
  let motion ← if !current then pure none else
    match j.get? "kind", (j.get? "keys", j.get? "cycle", j.get? "captions"),
        (j.get? "checks", j.get? "errorsLeft", j.get? "narrow") with
    | none, (none, none, none), (none, none, none) => pure none
    | some (.str "motion"), (some (.num keys), some (.str c), some (.num captions)),
        (some (.str checks), some (.num errorsLeft), some (.bool narrow)) =>
      match cycleOfText? c with
      | some cycle =>
        if keys == 0 then throw "a motion has at least one key"
        if !motionCheckWords.contains checks then
          throw s!"the check level {checks} is not fail, warn or ignore"
        if checks == "fail" && errorsLeft != 0 then
          throw "a motion checked at the level fail has no error left"
        pure (some { keys, cycle, captions, checks, errorsLeft, narrow })
      | none => throw s!"the cycle {c} is not a non-negative number n or n/d in lowest terms"
    | some (.str "motion"), _, _ =>
      throw "a motion needs the numbers keys, captions and errorsLeft, the strings cycle and checks \
        and the boolean narrow"
    | some (.str k), _, _ => throw s!"the kind {k} is unknown"
    | some _, _, _ => throw "the key kind must be a string"
    | none, _, _ =>
      throw "the keys keys, cycle, captions, checks, errorsLeft and narrow belong to a motion \
        (kind motion)"
  let m : ManifestEntry := {
    path := ← str "path", format := ← str "format", bytes := ← num "bytes",
    sha256 := ← str "sha256", fingerprint := ← str "fingerprint", module := ← str "module",
    decl := ← str "decl", file := ← str "file", line := ← num "line", column := ← num "column",
    version := ← str "version", repo := ← opt "repo", commit := ← opt "commit",
    darkColours := ← pairs "darkColours", darkOpacities := ← pairs "darkOpacities",
    standing := (← opt "standing").map readStanding,
    theorems, motion }
  if !standingOk m.standing m.theorems then
    throw "the standing is not linked with its theorems or illustration without any"
  if !safePath m.path then throw s!"the path {m.path} is not a safe relative path"
  if (Format.ofName? m.format).isNone then throw s!"the format {m.format} is unknown"
  if !isFingerprint m.sha256 || !isFingerprint m.fingerprint then
    throw "a hash is not 64 lowercase hexadecimal digits"
  return m

/-- The stem and the key of a key still's path, `X-key-k.svg` or `X-key-k.png` (`X` may end in
`-narrow`); none for another path. -/
def keyStillOf? (path : String) : Option (String × Nat) := do
  let base ← if path.endsWith ".svg" || path.endsWith ".png" then
      some (path.dropEnd 4).toString else none
  let parts := base.splitOn "-key-"
  let k ← parts.getLast?
  if parts.length < 2 || k.isEmpty || !k.all Char.isDigit || (k.length > 1 && k.startsWith "0")
    then none
  let stem := "-key-".intercalate parts.dropLast
  return (stem, ← k.toNat?)

/-- Why the entries `es` of one declaration, whose files record the motion `mo`, do not list its
files as the record says, if they do not: the key stills of one stem `X` (the SVG and the PNG of
each key `0` to `keys - 1`, and of no other) with the animated SVG `X.svg`, and, exactly when the
record says the motion has a narrow rendition, the same for the stem `X-narrow`. -/
def motionKeyProblem? (decl : String) (mo : MotionSummary) (es : Array ManifestEntry) :
    Option String :=
  let stills := es.filterMap fun m => (keyStillOf? m.path).map fun (s, k) => (s, k, m.format)
  let stems := (stills.map (·.1)).toList.eraseDups
  let mains := stems.filter (!·.endsWith "-narrow")
  let narrows := stems.filter (·.endsWith "-narrow")
  let paths := es.map (·.path)
  if mains.length != 1 then some s!"the files of {decl} record a motion of {mo.keys} keys but list \
    key stills of {mains.length} pictures"
  else if narrows != (if mo.narrow then mains.map (· ++ "-narrow") else []) then
    some s!"the files of {decl} record a motion {if mo.narrow then "with" else "without"} a narrow \
      rendition but list the narrow key stills {narrows}"
  else if !(stems.all fun stem => paths.contains (stem ++ ".svg")) then
    some s!"the files of {decl} record a motion but do not list its animated SVG at each width"
  else stems.findSome? fun stem =>
    let want := (List.range mo.keys).flatMap fun k => [(k, "svg"), (k, "png")]
    let have_ := (stills.filter (·.1 == stem)).toList.map fun (_, k, f) => (k, f)
    if want.all have_.contains && have_.all want.contains && have_.length == want.length then
      none
    else some s!"the files of {decl} record a motion of {mo.keys} keys but list the key stills \
      {(have_.map (·.1)).eraseDups} of {stem}"

/-- Reads a manifest: its text must be JSON as `Json.parse` reads it, an object with a known
`format` (`manifestFormat`; or `previousManifestFormat`, or one of the earlier
`spacedManifestFormat` and `oldManifestFormat`, whose theorems are one string of names separated
by single spaces) and a `files` array of at most `maxManifestFiles` entries that
`ManifestEntry.ofJson` accepts, with no path twice, in which the files of one declaration all
record the same motion or none, and in which the files of a motion list exactly its key stills
(`motionKeyProblem?`). -/
def Manifest.parse (d : ByteArray) : Except String (Array ManifestEntry) := do
  let j ← Json.parse d
  let (spaced, current) ← match j.get? "format" with
  | some (.str f) =>
    if f == manifestFormat then pure (false, true)
    else if f == previousManifestFormat then pure (false, false)
    else if f == spacedManifestFormat || f == oldManifestFormat then pure (true, false)
    else throw s!"unknown manifest format {f}"
  | _ => throw "the manifest has no format"
  let some (.arr files) := j.get? "files" | throw "the manifest has no files list"
  if files.size > maxManifestFiles then throw "the manifest lists too many files"
  let mut out : Array ManifestEntry := #[]
  let mut seen : Std.HashSet String := {}
  let mut motions : Std.HashMap String (Option MotionSummary) := {}
  for f in files do
    let m ← ManifestEntry.ofJson f spaced current
    if seen.contains m.path then throw s!"the path {m.path} is listed twice"
    seen := seen.insert m.path
    let key := m.module ++ "\n" ++ m.decl
    match motions[key]? with
    | some mo =>
      if mo != m.motion then
        throw s!"the files of {m.decl} do not all record the same motion"
    | none => motions := motions.insert key m.motion
    out := out.push m
  for (key, mo) in motions.toArray do
    if let some mo := mo then
      let es := out.filter fun m => m.module ++ "\n" ++ m.decl == key
      if let some why := motionKeyProblem? ((es[0]?.map (·.decl)).getD "") mo es then throw why
  return out

end PILean.Trust
