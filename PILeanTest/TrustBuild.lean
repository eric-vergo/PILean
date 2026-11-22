/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Trust.Attr
import PILeanTest.Examples

/-!
# Tests of the attribute, the fingerprint, `pilean-build` and `pilean-verify`

The attribute `figure` records the module, declaration, file, line, column and source hash of the
three small figures below; `figures%` lists them with the gallery's, sorted; the fingerprint has a
golden value and changes with each input; a build into a directory under `.lake` is checked,
verified, damaged in several ways (a changed byte, a deleted file, an extra file, a manifest with
hostile paths or garbage) and the damage reported; the bounded JSON reader is exercised.
-/

namespace PILeanTest.TrustBuild

open PILean PILean.Trust

/-- A small tagged figure of a function plot. -/
@[figure] def sampleFigure : Plot.Figure :=
  { title := "T", width := 160, height := 100,
    panels := #[{ series := #[.function "x²" (fun x => x * x) (-1) 1] }] }

/-- A small tagged graph. -/
@[figure] def sampleGraph : Graph := Graph.ofPairs [(0, 1), (1, 2)]

/-- A small tagged animation of three frames. -/
@[figure] def sampleAnimation : Animation :=
  { width := 24, height := 16, fps := 5, duration := 0.6, loops := 1,
    frame := fun t =>
      .path (Canvas.rect 0 0 (4 + 20 * t) 16) (some (.solid ⟨200, 30, 30, 255⟩)) none,
    text := Style.light.text }

/-- error: @[figure] needs a type with a ToOutputs instance,
but PILeanTest.TrustBuild.notAFigure has type Nat -/
#guard_msgs (error) in
/-- Not a figure. -/
@[figure] def notAFigure : Nat := 3

/-- Every figure of the environment, as `figures%` gives them. -/
def allFigures : Array FigureEntry := figures%

/-- The tagged figures of this module, which the build tests use (the gallery's are slower). -/
def mine : Array FigureEntry := allFigures.filter (·.module == "PILeanTest.TrustBuild")

/-- The 1-based number of the first line of `text` that starts with `pre`, or 0. -/
def lineOf (text pre : String) : Nat :=
  match (text.splitOn "\n").findIdx? (·.startsWith pre) with
  | some i => i + 1
  | none => 0

/-- The entry for a declaration of this module. -/
def entryOf (d : String) : Option FigureEntry := mine.find? (·.decl == d)

/-- The source data used for the golden fingerprint. -/
def sampleData : SourceData :=
  { module := "M", decl := "M.d", file := "M.lean", line := 3, column := 4,
    sourceHash := Sha256.hex (Sha256.hashString "def d := 1") }

/-- The golden fingerprint of the specification `spec` and `sampleData` in version `0.1.0` with
the renderer `test-renderer` (computed independently with Python's `hashlib`, from the
serialisation in `docs/TRUST.md`). -/
def goldenFingerprint : String :=
  "125a80b5541d6a486e7c295cf14e776de3ac9d9a6bc0ba7c56d9ada338228f75"

/-- The fingerprint with the renderer `test-renderer`, so the golden value does not depend on the
library's sources. -/
def fpT (spec : ByteArray) (d : SourceData) (version : String := "0.1.0") : String :=
  fingerprint spec d version "test-renderer"

/-- Checks that need no files. -/
def checks : Array (String × Bool) :=
  let e := (entryOf "PILeanTest.TrustBuild.sampleFigure")
  let names := allFigures.map fun e => e.module ++ " " ++ e.decl
  let sorted := names.qsort (· < ·)
  let spec := "spec".toUTF8
  let fp := fpT spec sampleData
  #[("figures%: the tagged figures are all there",
      ["PILeanTest.Examples PILeanTest.Examples.functions",
        "PILeanTest.Examples PILeanTest.Examples.GraphFigures.compiler",
        "PILeanTest.Examples PILeanTest.Examples.Animations.wave",
        "PILeanTest.TrustBuild PILeanTest.TrustBuild.sampleFigure",
        "PILeanTest.TrustBuild PILeanTest.TrustBuild.sampleGraph",
        "PILeanTest.TrustBuild PILeanTest.TrustBuild.sampleAnimation"].all names.contains),
    ("figures%: sorted by module and declaration, each once",
      names == sorted && (names.toList.eraseDups.length == names.size)),
    ("figure attribute: the module, file and column of a declaration",
      e.all fun e => e.module == "PILeanTest.TrustBuild" && e.file == "PILeanTest/TrustBuild.lean"
        && e.column == 0),
    ("fingerprint: golden value", fp == goldenFingerprint),
    ("fingerprint: 64 lowercase hexadecimal digits", isFingerprint fp),
    ("fingerprint: another specification gives another one",
      fpT "spec2".toUTF8 sampleData != fp),
    ("fingerprint: another source hash gives another one",
      fpT spec { sampleData with sourceHash := Sha256.hex (Sha256.hashString "x") }
        != fp),
    ("fingerprint: another line gives another one",
      fpT spec { sampleData with line := 4 } != fp),
    ("fingerprint: another version gives another one",
      fpT spec sampleData (version := "0.1.1") != fp),
    ("fingerprint: fields are length prefixed (moving a character between fields changes it)",
      fpT spec { sampleData with module := "Ma", decl := ".d" } != fp),
    ("fingerprint: input starts with the header",
      (fingerprintInput spec sampleData).extract 0 21 == "PILean fingerprint 2\n".toUTF8),
    ("fingerprint: another renderer gives another one",
      fingerprint spec sampleData "0.1.0" "other" != fp),
    ("renderer: the identity is 64 hexadecimal digits and covers the rasteriser, the lettering \
        and the PNG writer",
      isFingerprint rendererId && ["PILean.Raster.Draw", "PILean.Text.Lettering",
        "PILean.Png.Write", "PILean.Svg"].all (rendererSources.map (·.1)).contains),
    ("fingerprint: length prefix is eight bytes big-endian",
      lengthPrefixed "abc".toUTF8 == ⟨#[0, 0, 0, 0, 0, 0, 0, 3, 97, 98, 99]⟩),
    ("outputs: the SVG output's specification is its SVG text",
      (e.map fun e => (e.outputs ()).any fun o =>
        o.format == .svg && o.spec == (match o.bytes () with | .ok b => b | .error _ => .empty))
        == some true),
    ("outputs: the formats and suffixes of a figure, a graph and an animation",
      (mine.map fun e =>
        (e.decl, (e.outputs ()).toList.map fun o => o.format.name ++ o.name)).toList
        == [("PILeanTest.TrustBuild.sampleAnimation", ["svg", "apng", "gif", "png-poster"]),
          ("PILeanTest.TrustBuild.sampleFigure", ["svg", "png"]),
          ("PILeanTest.TrustBuild.sampleGraph", ["svg", "png"])]),
    ("path: module as directories, declaration and suffix as the stem",
      (outputPath { sampleData with module := "A.B", decl := "A.B.c.d" }
        { name := "-dark", format := .svg, bytes := fun _ => .ok .empty, spec := .empty }).toOption
        == some "A/B/c.d-dark.svg"),
    ("path: an animated PNG is a png file",
      (outputPath sampleData
        { name := "", format := .apng, bytes := fun _ => .ok .empty, spec := .empty }).toOption
        == some "M/d.png"),
    ("path: unusual characters are replaced",
      (outputPath { sampleData with decl := "M.«a b»/∀" }
        { name := "", format := .svg, bytes := fun _ => .ok .empty, spec := .empty }).toOption
        == some "M/_a_b___.svg"),
    ("path: an empty or dot component is refused",
      (outputPath { sampleData with module := "A..B" }
        { name := "", format := .svg, bytes := fun _ => .ok .empty, spec := .empty }).toOption
        == none),
    ("safePath: ordinary paths", safePath "A/b/c.svg" && safePath "x-y_z.1.png"),
    ("safePath: refuses .., absolute, backslash, empty parts, colon, space",
      !safePath "../x" && !safePath "a/../x" && !safePath "/etc/passwd" && !safePath "a\\b" &&
      !safePath "a//b" && !safePath "" && !safePath "C:/x" && !safePath "a b" && !safePath "./a"
      && !safePath "a/" && !safePath "."),
    ("json: values",
      (Json.parse "{\"a\":[1,true,null,\"x\\n\\u00e9\\ud83d\\ude00\"]}".toUTF8).toOption.isSome),
    ("json: string escapes decode",
      match Json.parse "\"a\\n\\u00e9\\ud83d\\ude00\\\"\"".toUTF8 with
      | .ok (.str s) => s == "a\né😀\""
      | _ => false),
    ("json: escape and parse round trip",
      match Json.parse ("\"" ++ Json.escape "q\"\\\n\t\u0001é" ++ "\"").toUTF8 with
      | .ok (.str s) => s == "q\"\\\n\t\u0001é"
      | _ => false),
    ("json: trailing text, a repeated key, a leading zero, fractions, lone surrogates, control \
      characters and unclosed values are refused",
      ["1 2", "{\"a\":1,\"a\":2}", "01", "1.5", "1e3", "\"\\ud800\"", "\"a\nb\"", "[1", "{\"a\"",
        "\"abc", "", "[1,]", "{,}", "nul", "-1", "\"\\x\"", "\"\\u12\""].all fun t =>
        (Json.parse t.toUTF8).toOption.isNone),
    ("json: nesting beyond the limit is refused, within it is read",
      (Json.parse (String.ofList (List.replicate 20 '[') ++
        String.ofList (List.replicate 20 ']')).toUTF8).toOption.isNone &&
      (Json.parse (String.ofList (List.replicate 6 '[') ++
        String.ofList (List.replicate 6 ']')).toUTF8).toOption.isSome),
    ("json: a number of 16 digits is refused",
      (Json.parse "1234567890123456".toUTF8).toOption.isNone &&
      (Json.parse "123456789012345".toUTF8).toOption.isSome),
    ("args: defaults and options",
      match parseArgs ["--out", "d", "--repo", "https://x.org/r", "--commit", "abcd1234",
          "--check"] with
      | .ok (o, opts) => o == "d" && opts.repo == some "https://x.org/r" &&
          opts.commit == some "abcd1234" && opts.check
      | .error _ => false),
    ("args: unknown options, a missing value, a bad link and a bad commit are refused",
      [["--bogus"], ["--out"], ["--repo", "javascript:alert(1)"], ["--commit", "xyz"],
        ["--commit", "ABCD1234"], ["--repo", "file:///etc"], ["x"]].all fun a =>
        (parseArgs a).toOption.isNone)]

/-- The result of `verifyDir`, as a list of `verdict path` words, or `error`. -/
def verdicts (dir : System.FilePath) : IO (List String) := do
  match ← verifyDir dir with
  | .ok vs => return vs.toList.map fun (p, v) => v.text ++ " " ++ p
  | .error _ => return ["error"]

/-- The report of `checkLines` of the directory for the entries. -/
def checkReport (entries : Array FigureEntry) (dir : System.FilePath) :
    IO (List String) := do
  match ← renderAll entries {} with
  | .ok files =>
    return (← checkLines files (Manifest.render (files.map (·.entry))).toUTF8 dir).toList
  | .error e => return [e]

/-- The message of a failed `renderAll`, or empty if it succeeded. -/
def renderError (entries : Array FigureEntry) : IO String := do
  match ← renderAll entries {} with
  | .ok _ => return ""
  | .error e => return e

/-- The builder's bounds: a file whose bytes are not of its output's format, a file that is
within the cap before its source record is inserted and over it after, and an entry with more
outputs than a manifest may list (refused before any is rendered). -/
def builderBounds : IO (Array (String × Bool)) := do
  let some base := mine[0]? | return #[("build bounds: a figure to start from", false)]
  let one (format : Format) (b : ByteArray) : FigureEntry :=
    let o : Output :=
      { name := "", format := format, bytes := fun _ => .ok b, spec := "s".toUTF8 }
    { base with outputs := fun _ => #[o] }
  let plain := (Png.encode { width := 1, height := 1, mode := .l, data := ⟨#[0]⟩ }).toOption.getD
    .empty
  let wrongFormat ← renderError #[one .apng plain]
  let rightFormat ← renderError #[one .png plain]
  let head := "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"1\" height=\"1\">"
  let tail := "</svg>"
  let big := (head.pushn ' ' (maxOutputBytes - head.length - tail.length) ++ tail).toUTF8
  let overCap ← renderError #[one .svg big]
  let many : FigureEntry := { base with outputs := fun _ =>
    (Array.range (maxManifestFiles + 1)).map fun i =>
      { name := s!"-{i}", format := .svg, bytes := fun _ => .error "rendered", spec := .empty } }
  let tooMany ← renderError #[many]
  return #[
    ("build: a file whose bytes are not of its output's format is refused",
      (wrongFormat.splitOn "not a file of the format apng").length > 1 && rightFormat == ""),
    ("build: a file over the cap once its source record is in is refused",
      big.size == maxOutputBytes &&
        (overCap.splitOn "with its source record is larger").length > 1),
    ("build: more outputs than a manifest lists are refused before any is rendered",
      (tooMany.splitOn s!"more than {maxManifestFiles} files").length > 1 &&
        (tooMany.splitOn "rendered").length == 1)]

/-- The checks that build into a directory and damage it. -/
def ioChecks : IO (Array (String × Bool)) := do
  let root : System.FilePath := ".lake" / "pilean-test-build"
  if ← root.pathExists then IO.FS.removeDirAll root
  let a := root / "a"
  let b := root / "b"
  let code ← build mine a {}
  let code2 ← build mine b {}
  let manifestA ← IO.FS.readBinFile (a / manifestName)
  let manifestB ← IO.FS.readBinFile (b / manifestName)
  let entries := (Manifest.parse manifestA).toOption.getD #[]
  let mut sameBytes := true
  let mut sourcesOk := true
  for m in entries do
    let x ← IO.FS.readBinFile (a / m.path)
    let y ← IO.FS.readBinFile (b / m.path)
    if x != y then sameBytes := false
    match Source.read? x with
    | .ok s => if !m.matches s || m.sha256 != Sha256.hex (Sha256.hash x) || m.bytes != x.size then
        sourcesOk := false
    | .error _ => sourcesOk := false
  let withSrc ←
    build mine (root / "c") { repo := some "https://example.org/r", commit := some "abc1234" }
  let cEntries :=
    (Manifest.parse (← IO.FS.readBinFile (root / "c" / manifestName))).toOption.getD #[]
  let me ← IO.FS.readFile "PILeanTest/TrustBuild.lean"
  let figLine := lineOf me "/-- A small tagged figure of a function plot."
  let figText := "\n".intercalate (((me.splitOn "\n").drop (figLine - 1)).take 4)
  let figHash := Sha256.hex (Sha256.hashString figText)
  let report0 ← checkReport mine a
  let verdict0 ← verdicts a
  let allOk := verdict0.all (·.startsWith "ok ")
  -- the paths of the build
  let paths := entries.map (·.path) |>.toList
  -- a changed byte
  let victim := a / "PILeanTest" / "TrustBuild" / "sampleGraph.svg"
  let victimBytes ← IO.FS.readBinFile victim
  IO.FS.writeBinFile victim (victimBytes.set! 0 (victimBytes.get! 0 ^^^ 1))
  let reportChanged ← checkReport mine a
  let verdictChanged ← verdicts a
  IO.FS.writeBinFile victim victimBytes
  -- a deleted file
  IO.FS.removeFile victim
  let reportMissing ← checkReport mine a
  let verdictMissing ← verdicts a
  IO.FS.writeBinFile victim victimBytes
  -- an extra file, also in a new directory
  IO.FS.writeFile (a / "PILeanTest" / "TrustBuild" / "stray.svg") "<svg/>"
  IO.FS.createDirAll (a / "other")
  IO.FS.writeFile (a / "other" / "x.txt") "x"
  let reportExtra ← checkReport mine a
  let verdictExtra ← verdicts a
  IO.FS.removeFile (a / "PILeanTest" / "TrustBuild" / "stray.svg")
  IO.FS.removeDirAll (a / "other")
  -- a file below more directories than the listing descends: the folder cannot be checked
  let deep := (List.range (maxListDepth + 2)).foldl (fun p i => p / s!"d{i + 1}") (a / "deep")
  IO.FS.createDirAll deep
  IO.FS.writeFile (deep / "planted.svg") "<svg/>"
  let reportDeep ← checkReport mine a
  let verdictDeep ← verdicts a
  IO.FS.removeDirAll (a / "deep")
  -- the same at the bounds of a small listing, and a listing exactly at them
  let small := root / "small"
  IO.FS.createDirAll (small / "x" / "y")
  for n in ["1", "2", "3"] do IO.FS.writeFile (small / "x" / "y" / n) n
  let atBounds ← listFiles small (maxDepth := 2) (maxEntries := 5)
  let tooDeep ← listFiles small (maxDepth := 1) (maxEntries := 5)
  let tooMany ← listFiles small (maxDepth := 2) (maxEntries := 4)
  -- a name listed in another spelling: a file system that ignores case (as macOS's does by
  -- default) finds the file under it, and the verdicts must not depend on that
  let doubled := root / "doubled"
  IO.FS.createDirAll (doubled / "PILeanTest" / "TrustBuild")
  let gm := (entries.find? (·.path.endsWith "sampleGraph.svg")).get!
  IO.FS.writeBinFile (doubled / gm.path) (← IO.FS.readBinFile (a / gm.path))
  let upper := { gm with path := gm.path.replace "sampleGraph" "SampleGraph" }
  IO.FS.writeFile (doubled / manifestName) (Manifest.render #[upper, gm])
  let verdictDoubled ← verdicts doubled
  IO.FS.writeFile (doubled / manifestName) (Manifest.render #[upper])
  let verdictRenamed ← verdicts doubled
  -- the same size and hash but another source: the manifest says another line
  let manifestText := String.fromUTF8! manifestA
  let aSrc := root / "d"
  IO.FS.createDirAll aSrc
  for m in entries do
    let p := aSrc / m.path
    if let some par := p.parent then IO.FS.createDirAll par
    IO.FS.writeBinFile p (← IO.FS.readBinFile (a / m.path))
  let tweaked := entries.map fun m =>
    if m.path.endsWith "sampleGraph.svg" then { m with line := m.line + 1 } else m
  IO.FS.writeFile (aSrc / manifestName) (Manifest.render tweaked)
  let verdictDiffers ← verdicts aSrc
  -- a file without source information, listed with its right size and hash
  let plain := (Plot.Figure.toSvg {}).toUTF8
  let noSrc := entries.map fun m =>
    if m.path.endsWith "sampleGraph.svg" then
      { m with bytes := plain.size, sha256 := Sha256.hex (Sha256.hash plain) } else m
  IO.FS.writeBinFile (aSrc / "PILeanTest" / "TrustBuild" / "sampleGraph.svg") plain
  IO.FS.writeFile (aSrc / manifestName) (Manifest.render noSrc)
  let verdictNoSrc ← verdicts aSrc
  -- a format in the manifest that the bytes do not have: a PNG called animated, an animated
  -- PNG called plain, an SVG called a GIF
  let refmt := entries.map fun m =>
    if m.path.endsWith "sampleGraph.png" then { m with format := "apng" }
    else if m.path.endsWith "sampleAnimation.png" then { m with format := "png" }
    else if m.path.endsWith "sampleFigure.svg" then { m with format := "gif" } else m
  for m in entries do IO.FS.writeBinFile (aSrc / m.path) (← IO.FS.readBinFile (a / m.path))
  IO.FS.writeFile (aSrc / manifestName) (Manifest.render refmt)
  let verdictFormat ← verdicts aSrc
  -- hostile manifests
  let hostile := root / "h"
  IO.FS.createDirAll hostile
  let first := entries[0]!
  let mut hostileOk := true
  for p in ["../x", "/etc/passwd", "a\\b", "a/../b", "", "C:/x", "a/./b"] do
    IO.FS.writeFile (hostile / manifestName) (Manifest.render #[{ first with path := p }])
    if (← verdicts hostile) != ["error"] then hostileOk := false
  for t in ["garbage", "{}", "[]", "{\"format\":\"pilean-manifest-1\"}",
      "{\"format\":\"x\",\"files\":[]}",
      "{\"format\":\"pilean-manifest-1\",\"files\":[1]}",
      "{\"format\":\"pilean-manifest-1\",\"files\":[{}]}"] do
    IO.FS.writeFile (hostile / manifestName) t
    if (← verdicts hostile) != ["error"] then hostileOk := false
  -- a path listed twice, a short hash
  IO.FS.writeFile (hostile / manifestName) (Manifest.render #[first, first])
  if (← verdicts hostile) != ["error"] then hostileOk := false
  IO.FS.writeFile (hostile / manifestName) (Manifest.render #[{ first with sha256 := "abc" }])
  if (← verdicts hostile) != ["error"] then hostileOk := false
  let noManifest ← verdicts (root / "nothing-here")
  -- the command lines
  let usageCode ← buildMain mine ["--bogus"]
  let verifyUsage ← verifyMain []
  let verifyCode ← verifyMain [a.toString]
  let mainCheck ← buildMain mine ["--out", a.toString, "--check"]
  let mainBuild ← buildMain mine ["--out", (root / "e").toString]
  let mainVerifyBad ← verifyMain [(root / "h").toString]
  IO.FS.removeDirAll root
  return #[
    ("build: exit 0 and the same for two directories", code == 0 && code2 == 0),
    ("figure attribute: the line and the hash of the source text of a declaration",
      (entryOf "PILeanTest.TrustBuild.sampleFigure").all fun e =>
        e.line == figLine && e.sourceHash == figHash),
    ("build: the manifest is the same on every run", manifestA == manifestB),
    ("build: every file is the same on every run", sameBytes),
    ("build: files and manifest as expected",
      paths == ["PILeanTest/TrustBuild/sampleAnimation-poster.png",
        "PILeanTest/TrustBuild/sampleAnimation.gif", "PILeanTest/TrustBuild/sampleAnimation.png",
        "PILeanTest/TrustBuild/sampleAnimation.svg", "PILeanTest/TrustBuild/sampleFigure.png",
        "PILeanTest/TrustBuild/sampleFigure.svg", "PILeanTest/TrustBuild/sampleGraph.png",
        "PILeanTest/TrustBuild/sampleGraph.svg"]),
    ("build: each file's source record matches the manifest, size and hash", sourcesOk),
    ("build: the repository and commit are recorded",
      cEntries.size == entries.size &&
        cEntries.all (fun m => m.repo == some "https://example.org/r" &&
          m.commit == some "abc1234") && withSrc == 0),
    ("check: a fresh build matches", report0 == [] && manifestText.endsWith "]}\n"),
    ("verify: a fresh build is ok", allOk && verdict0.length == entries.size),
    ("check: a changed byte is stale",
      reportChanged == ["stale: PILeanTest/TrustBuild/sampleGraph.svg"]),
    ("verify: a changed byte is changed",
      verdictChanged.contains "changed PILeanTest/TrustBuild/sampleGraph.svg" &&
        (verdictChanged.filter (·.startsWith "ok ")).length == entries.size - 1),
    ("check: a deleted file is missing",
      reportMissing == ["missing: PILeanTest/TrustBuild/sampleGraph.svg"]),
    ("verify: a deleted file is missing",
      verdictMissing.contains "missing PILeanTest/TrustBuild/sampleGraph.svg"),
    ("check: extra files, also in other directories, are reported",
      reportExtra == ["extra: PILeanTest/TrustBuild/stray.svg", "extra: other/x.txt"] ||
        reportExtra == ["extra: other/x.txt", "extra: PILeanTest/TrustBuild/stray.svg"]),
    ("verify: files the manifest does not list are reported",
      verdictExtra.contains "extra PILeanTest/TrustBuild/stray.svg" &&
        verdictExtra.contains "extra other/x.txt" &&
        (verdictExtra.filter (·.startsWith "ok ")).length == entries.size),
    ("check: a file below more directories than the listing descends makes the folder \
      uncheckable", reportDeep.any (·.startsWith "cannot check: ") &&
        !reportDeep.any (·.startsWith "extra: ")),
    ("verify: a file below more directories than the listing descends is an error, not ok",
      verdictDeep == ["error"]),
    ("list: a folder at the bounds is listed; one over the depth or the entry bound is an error",
      atBounds.toOption == some #["x/y/1", "x/y/2", "x/y/3"] && (tooDeep matches .error _) &&
        (tooMany matches .error _)),
    ("verify: a file is ok only under the exact name the manifest gives",
      verdictDoubled == [s!"missing {upper.path}", s!"ok {gm.path}"] &&
        verdictRenamed == [s!"missing {upper.path}", s!"extra {gm.path}"]),
    ("verify: a source that differs from the manifest is reported",
      verdictDiffers.contains "source differs PILeanTest/TrustBuild/sampleGraph.svg"),
    ("verify: a file without source information is reported",
      verdictNoSrc.contains "no source PILeanTest/TrustBuild/sampleGraph.svg"),
    ("verify: a format the bytes do not have is reported",
      ["sampleGraph.png", "sampleAnimation.png", "sampleFigure.svg"].all (fun f =>
        verdictFormat.contains s!"format differs PILeanTest/TrustBuild/{f}") &&
        (verdictFormat.filter (·.startsWith "ok ")).length == entries.size - 3),
    ("verify: hostile and garbage manifests are rejected cleanly", hostileOk),
    ("verify: no manifest is an error", noManifest == ["error"]),
    ("main: a wrong command line exits 2", usageCode == 2 && verifyUsage == 2),
    ("main: verify, check and build exit codes",
      verifyCode == 0 && mainCheck == 0 && mainBuild == 0 && mainVerifyBad == 1)] ++
    (← builderBounds)

end PILeanTest.TrustBuild
