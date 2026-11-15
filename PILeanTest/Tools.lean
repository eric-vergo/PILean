/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanTest.Bounds
import PILeanTest.TrustBuild

/-!
# The command-line tools on hostile folders and files

`pilean-info` and `pilean-verify` are run as the user runs them, in child processes under limits
(`PILeanTest.Bounds.runLimited`), on special files, planted symbolic links and text made to
forge or hide output; `pilean-build`'s writer (`PILean.Trust.build`) is run in this process on
an output folder with planted links. A check fails if a tool waits, reads without end, prints a
character `escapeControl` would escape, follows a link or writes outside its folder.

## Main definitions

* `ioChecks`: the checks.
-/

namespace PILeanTest.Tools

open PILean PILean.Trust PILeanTest.Bounds

/-- Whether a tool's output has no `unsafeChar` other than the line feeds that end its lines. -/
def clean (s : String) : Bool := s.all fun c => c == '\n' || !unsafeChar c

/-- Runs a tool with a CPU limit of 20 s and a watchdog of 10 s. -/
def tool (exe : String) (args : Array String) (scratch : System.FilePath) : IO Run :=
  runLimited exe args 20 10000 scratch

/-- Makes a FIFO at `p` with `mkfifo`. -/
def mkfifo (p : System.FilePath) : IO Bool := do
  let r ← IO.Process.output { cmd := "mkfifo", args := #[p.toString] }
  return r.exitCode == 0

/-- Makes a symbolic link at `link` that points to `target`. -/
def symlink (target link : System.FilePath) : IO Bool := do
  let r ← IO.Process.output { cmd := "ln", args := #["-s", target.toString, link.toString] }
  return r.exitCode == 0

/-- The source file of a module of this repository. -/
def moduleFile (m : String) : System.FilePath :=
  ((m.splitOn ".").foldl (fun p c => p / c) ("." : System.FilePath)).addExtension "lean"

/-- The `PILean` modules the given ones import, directly or not, themselves included, sorted by
name: read from the `import` lines of the sources. -/
def importClosure (roots : Array String) : IO (Array String) := do
  let mut seen : Array String := #[]
  let mut todo := roots
  for _ in [0:10000] do
    let some m := todo.back? | break
    todo := todo.pop
    if seen.contains m || !m.startsWith "PILean." then continue
    seen := seen.push m
    for l in (← IO.FS.readFile (moduleFile m)).splitOn "\n" do
      if l.startsWith "import " then todo := todo.push ((l.drop 7).trimAscii.toString)
  return seen.qsort (· < ·)

/-- Every Unicode scalar value once. -/
def everyChar : String := Id.run do
  let mut s := ""
  for v in [0:0x110000] do
    if v < 0xD800 || 0xDFFF < v then s := s.push (Char.ofNat v)
  return s

/-- The checks. -/
def ioChecks : IO (Array (String × Bool)) := do
  let scratch ← IO.FS.realPath (← IO.FS.createTempDir)
  let mut r : Array (String × Bool) := #[]
  try
    r := r.push ("escape: no character that escapeControl lets through is unsafe",
      clean (escapeControl everyChar) && !(escapeControl everyChar).contains '\n')
    -- special files
    let fifo := scratch / "fifo"
    let made ← mkfifo fifo
    let info ← tool "pilean-info" #[fifo.toString] scratch
    r := r.push ("info: a FIFO is refused without waiting",
      made && info.status == some 1 && (info.err.splitOn "not a regular file").length > 1)
    let zero ← tool "pilean-info" #["/dev/zero"] scratch
    r := r.push ("info: a device is refused without reading", zero.status == some 1 &&
      (zero.rss.map (fun m => decide (m < 64 <<< 20))).getD true)
    -- text that would forge or hide output
    let src : Source :=
      { module := "M", decl := "d\u202Eevil\u2066x\u200B\uFEFF", file := "F.lean", line := 1,
        column := 0, version := PILean.version }
    let png :=
      (Png.encode { width := 1, height := 1, mode := .l, data := ⟨#[0]⟩ }).toOption.getD .empty
    let withSrc := (withSourcePng png src).toOption.getD .empty
    IO.FS.writeBinFile (scratch / "bidi.png") withSrc
    let bidi ← tool "pilean-info" #[(scratch / "bidi.png").toString] scratch
    r := r.push ("info: bidirectional and invisible characters are shown escaped",
      bidi.status == some 0 && clean bidi.out && (bidi.out.splitOn "\\u{202e}").length > 1)
    -- a build to verify, and the same build damaged
    let good := scratch / "good"
    let _ ← build TrustBuild.mine good {}
    let ok ← tool "pilean-verify" #[good.toString] scratch
    r := r.push ("verify: a fresh build is ok", ok.status == some 0)
    let linkDir := scratch / "link-to-good"
    let _ ← symlink good linkDir
    let viaLink ← tool "pilean-verify" #[linkDir.toString] scratch
    r := r.push ("verify: the folder named through a link is resolved once and verified",
      viaLink.status == some 0)
    let manifest ← IO.FS.readFile (good / manifestName)
    let entries := (Manifest.parse manifest.toUTF8).toOption.getD #[]
    let first := entries[0]!
    -- forged lines: escape sequences and line feeds in a path and in a key
    let forge := scratch / "forge"
    IO.FS.createDirAll forge
    let mut forgedClean := true
    for t in [Manifest.render #[{ first with path := "a\u001b[2K\rok: all\nok: x" }],
        "{\"format\":\"pilean-manifest-1\",\"files\":[{\"pa\\u001bth\\n\":1}]}",
        "{\"format\":\"pilean-manifest-1\u001b]0;t\u0007\",\"files\":[]}",
        "{\"format\":\"pilean-manifest-1\",\"files\":[" ++
          (first.render.replace "\"module\":\"" "\"module\":\"\u001b[31m\u202E") ++ "]}"] do
      IO.FS.writeFile (forge / manifestName) t
      let v ← tool "pilean-verify" #[forge.toString] scratch
      if v.status != some 1 || !clean v.err || !clean v.out then forgedClean := false
    r := r.push ("verify: escape sequences, line feeds and bidi characters are printed escaped",
      forgedClean)
    -- a FIFO as the manifest
    let fifoDir := scratch / "fifo-manifest"
    IO.FS.createDirAll fifoDir
    let _ ← mkfifo (fifoDir / manifestName)
    let vf ← tool "pilean-verify" #[fifoDir.toString] scratch
    r := r.push ("verify: a FIFO as the manifest is refused without waiting", vf.status == some 1)
    -- a symbolic link as the manifest
    let linkMan := scratch / "link-manifest"
    IO.FS.createDirAll linkMan
    let _ ← symlink (good / manifestName) (linkMan / manifestName)
    let vl ← tool "pilean-verify" #[linkMan.toString] scratch
    r := r.push ("verify: a symbolic link as the manifest is refused", vl.status == some 1)
    -- a symbolic link to a directory on the way to every file, and one to a single file
    let linked := scratch / "linked"
    IO.FS.createDirAll linked
    IO.FS.writeFile (linked / manifestName) manifest
    let _ ← symlink (good / "PILeanTest") (linked / "PILeanTest")
    let vd ← tool "pilean-verify" #[linked.toString] scratch
    r := r.push ("verify: files reached through a linked directory are not ok",
      vd.status == some 1 && (vd.out.splitOn "\n").all (·.startsWith "not a regular file: "))
    let one := scratch / "one-link"
    IO.FS.createDirAll (one / "PILeanTest" / "TrustBuild")
    IO.FS.writeFile (one / manifestName) manifest
    for m in entries do
      if m.path != first.path then
        IO.FS.writeBinFile (one / m.path) (← IO.FS.readBinFile (good / m.path))
    let _ ← symlink (good / first.path) (one / first.path)
    let vo ← tool "pilean-verify" #[one.toString] scratch
    r := r.push ("verify: a linked file is not ok and the others are",
      vo.status == some 1 && vo.out.startsWith s!"not a regular file: {first.path}" &&
        (vo.out.splitOn "\nok: ").length == entries.size)
    -- the writer: a planted link to a directory outside, and one to a file outside
    let outside := scratch / "outside"
    IO.FS.createDirAll outside
    IO.FS.writeFile (outside / "keep.txt") "keep"
    let out1 := scratch / "out1"
    IO.FS.createDirAll out1
    let _ ← symlink outside (out1 / "PILeanTest")
    let c1 ← build TrustBuild.mine out1 {}
    let wroteOutside := (← outside.readDir).size != 1
    r := r.push ("build: a linked directory in the output is refused, nothing written through it",
      c1 == 1 && !wroteOutside)
    let out2 := scratch / "out2"
    IO.FS.createDirAll (out2 / "PILeanTest" / "TrustBuild")
    let _ ← symlink (outside / "keep.txt") (out2 / first.path)
    let c2 ← build TrustBuild.mine out2 {}
    r := r.push ("build: a linked file in the output is refused and its target kept",
      c2 == 1 && (← IO.FS.readFile (outside / "keep.txt")) == "keep")
    let checkLinked ← TrustBuild.checkReport TrustBuild.mine (← IO.FS.realPath linked)
    r := r.push ("check: files reached through a linked directory are stale",
      checkLinked.any (·.startsWith "stale: PILeanTest/") &&
        !checkLinked.any (·.startsWith "missing: PILeanTest/"))
    -- the renderer's identity covers exactly the imported modules, with their current text
    let closure ← importClosure #["PILean.Trust.Figure", "PILean.Trust.Provenance",
      "PILean.Trust.Sha256"]
    let listed := rendererSources.map (·.1)
    let missing := closure.filter (!listed.contains ·)
    let extra := listed.filter (!closure.contains ·)
    let mut stale : Array String := #[]
    for (m, t) in rendererSources do
      if (← IO.FS.readFile (moduleFile m)) != t then stale := stale.push m
    r := r.push (s!"renderer: the identity covers exactly the modules Renderer.lean imports \
      (missing {missing}, not imported {extra}) with their current text (stale {stale})",
      missing.isEmpty && extra.isEmpty && stale.isEmpty && isFingerprint rendererId)
    -- a figure whose text the lettering cannot draw is refused, not drawn with boxes
    let fig : Plot.Figure := { width := 200, height := 120, title := "snow \u2603" }
    let entry : FigureEntry :=
      { module := "M", decl := "M.f", file := "M.lean", line := 1, column := 0,
        sourceHash := String.ofList (List.replicate 64 '0'),
        outputs := fun _ => ToOutputs.outputs fig }
    let refused := (entry.outputs ()).any fun o =>
      match renderOutput entry o {} with
      | .error e => (e.splitOn "no glyph for \u2603").length > 1
      | .ok _ => false
    r := r.push ("build: a figure with a character the lettering lacks is refused, naming it",
      refused)
    -- the bounded reader
    IO.FS.writeFile (scratch / "ten") "0123456789"
    let r10 ← readRegular (scratch / "ten") 10
    let r9 ← readRegular (scratch / "ten") 9
    r := r.push ("read: a file at the cap is read, one byte over is refused",
      (r10.toOption.map (·.size)) == some 10 && r9.toOption.isNone)
  finally
    IO.FS.removeDirAll scratch
  return r

end PILeanTest.Tools
