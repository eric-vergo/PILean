/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Trust.Attr
import PILean.Trust.Build
import PILean.Trust.Verify

/-!
# Tests of a figure's standing

Three small figures: one linked to a theorem (`proved`), one marked `@[figure illustration]`, one
neither. `figures%` gives each its standing; a build records it in every file's source record
and in the manifest, `pilean-verify` repeats it; `pilean-build --require-standing` refuses the
unmarked illustration and accepts the others; `figure_proves` refuses a marked figure; the
attribute refuses any other argument; a source record or a manifest with a malformed standing
is refused.
-/

namespace PILeanTest.Standing

open PILean PILean.Trust PILean.Diagram

/-- A figure with a theorem: the Dyck path `UD`. -/
@[figure] def provedPath : Diagram := (LatticePath.ofDyck [true, false]).figure

/-- The figure draws two steps, ending at `(2, 0)`. -/
theorem provedPath_spec : provedPath.steps.map (fun (_, _, q) => q) = [(1, 1), (2, 0)] := by
  decide +kernel

figure_proves provedPath provedPath_spec

/-- A figure marked as an illustration: a dot. -/
@[figure illustration] def markedSketch : Diagram :=
  { marks := [{ part := .guide, shape := .dot (0, 0) }] }

/-- A figure neither proved nor marked: a dot. -/
@[figure] def unmarkedSketch : Diagram :=
  { marks := [{ part := .guide, shape := .dot (1, 0) }] }

/-- A statement about the marked figure. -/
theorem markedSketch_marks : markedSketch.marks.length = 1 := rfl

/--
error: PILeanTest.Standing.markedSketch is marked @[figure illustration]; a figure tied to its object by a theorem is not an illustration: remove the marking
-/
#guard_msgs in
figure_proves markedSketch markedSketch_marks

/-- error: @[figure] takes no argument other than `illustration` -/
#guard_msgs in
/-- Not registered: the argument is not `illustration`. -/
@[figure proved] def badArgument : Diagram := { marks := [] }

/-- The figures of this module, as `figures%` gives them. -/
def entries : Array FigureEntry :=
  (figures% : Array FigureEntry).filter (·.module == "PILeanTest.Standing")

/-- The entry of a declaration of this module. -/
def entryOf (d : String) : Option FigureEntry :=
  entries.find? (·.decl == s!"PILeanTest.Standing.{d}")

/-- The source record of the first output of an entry. -/
def sourceOf (d : String) : Option Source :=
  (entryOf d).bind fun e => (e.outputs ())[0]?.map (e.source ·)

/-- Checks that need no files. -/
def checks : Array (String × Bool) :=
  let valid : Source :=
    { module := "M", decl := "M.d", file := "M.lean", line := 1, column := 0, version := "1" }
  #[("standing: a linked figure is proved, by its theorem",
      (entryOf "provedPath").map (·.standing) ==
        some (.proved #["PILeanTest.Standing.provedPath_spec"])),
    ("standing: a marked figure is a marked illustration",
      (entryOf "markedSketch").map (·.standing) == some (.illustration true)),
    ("standing: a figure neither linked nor marked is an unmarked illustration",
      (entryOf "unmarkedSketch").map (·.standing) == some (.illustration false)),
    ("standing: every output of a figure carries its standing",
      entries.all fun e => (e.outputs ()).all (·.standing == e.standing)),
    ("standing: --require-standing names the unmarked illustration only",
      unmarkedIllustrations entries == #["PILeanTest.Standing.unmarkedSketch"]),
    ("standing: the source record of a proved figure names its theorem",
      (sourceOf "provedPath").map (fun s => (s.standing, s.proves)) ==
        some (some "proved", some "PILeanTest.Standing.provedPath_spec")),
    ("standing: the source record of an illustration says so, with no theorem",
      (sourceOf "markedSketch").map (fun s => (s.standing, s.proves)) ==
        some (some "illustration", none)),
    ("standing: a record that claims proved without a theorem cannot be written or read",
      (Source.validate { valid with standing := some "proved" } matches .error _) &&
        (Source.ofFields (valid.fields.push ("standing", "proved")) matches .error _) &&
        (Source.ofFields (valid.fields ++ #[("standing", "illustration"), ("proves", "T")])
          matches .error _) &&
        (Source.ofFields (valid.fields.push ("standing", "certain")) matches .error _) &&
        (Source.ofFields (valid.fields ++ #[("standing", "proved"), ("proves", "A  B")])
          matches .error _)),
    ("standing: a well-formed record is read back",
      (Source.ofFields (valid.fields ++ #[("standing", "proved"), ("proves", "A B")])).toOption ==
        some { valid with standing := some "proved", proves := some "A B" })]

/-- The standing in each format of file, a build with and without `--require-standing`, and the
lines of `pilean-verify`. -/
def ioChecks : IO (Array (String × Bool)) := do
  let root : System.FilePath := ".lake" / "pilean-test-standing"
  if ← root.pathExists then IO.FS.removeDirAll root
  let strict ← renderAll entries { requireStanding := true }
  let strictMsg := match strict with | .error e => e | .ok _ => ""
  let fine := entries.filter (!·.standing.unmarked)
  let ok ← build fine (root / "a") { requireStanding := true }
  let all ← build entries (root / "b") {}
  let manifest :=
    (Manifest.parse (← IO.FS.readBinFile (root / "a" / manifestName))).toOption.getD #[]
  let mut filesAgree := !manifest.isEmpty
  for m in manifest do
    match Source.read? (← IO.FS.readBinFile (root / "a" / m.path)) with
    | .ok s => if s.standing != m.standing || s.proves != m.proves || m.standing.isNone then
        filesAgree := false
    | .error _ => filesAgree := false
  let lines ← verifyDirEntries (root / "a")
  let recorded := match lines with
    | .ok vs => vs.toList.map fun ((p, v, m) : String × Verdict × Option ManifestEntry) =>
        s!"{v.text}: {p}{(m.map recordedStanding).getD ""}"
    | .error _ => []
  -- a manifest whose standing is malformed is refused as a whole
  let bad := (Manifest.render (manifest.map fun m => { m with proves := none })).toUTF8
  let refused := (Manifest.parse bad) matches .error _
  IO.FS.removeDirAll root
  return #[
    ("standing: --require-standing refuses the unmarked illustration, naming it",
      (strictMsg.splitOn "unmarkedSketch is an illustration").length == 2 &&
        (strictMsg.splitOn "markedSketch is").length == 2),
    ("standing: --require-standing builds the proved and the marked figures", ok == 0),
    ("standing: without the option every figure builds", all == 0),
    ("standing: each file records the standing its manifest entry lists", filesAgree),
    ("standing: pilean-verify repeats the recorded standing on its ok lines",
      recorded.any (fun l => l.startsWith "ok: PILeanTest/Standing/provedPath.svg [recorded: \
        proved by PILeanTest.Standing.provedPath_spec]") &&
        recorded.any (fun l => l.startsWith "ok: PILeanTest/Standing/markedSketch.svg \
          [recorded: illustration]")),
    ("standing: a manifest that lists a proved figure without its theorem is refused", refused)]

end PILeanTest.Standing
