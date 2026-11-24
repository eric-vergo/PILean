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

Small figures: one with a linked theorem (`linked`), one linked with the command's other name
`figure_proves`, one marked `@[figure illustration]`, one neither, and three whose linked
theorems say nothing of substance about them (the rule is about names, so they are `linked`
too: the standing says that a theorem is linked, not what it says). `figures%` gives each its standing; a build records it in every file's source record
and in the manifest, `pilean-verify` repeats it; `pilean-build --require-standing` refuses the
unmarked illustration and accepts the others; `figure_links` refuses a marked figure; the
attribute refuses any other argument; a source record or a manifest with a malformed standing
is refused, and one that writes the standing `proved` and the key `proves` reads as `linked`
with `theorems`.
-/

namespace PILeanTest.Standing

open PILean PILean.Trust PILean.Diagram

/-- A figure with a theorem: the Dyck path `UD`. -/
@[figure] def linkedPath : Diagram := (LatticePath.ofDyck [true, false]).figure

/-- The figure draws two steps, ending at `(2, 0)`. -/
theorem linkedPath_spec : linkedPath.steps.map (fun (_, _, q) => q) = [(1, 1), (2, 0)] := by
  decide +kernel

figure_links linkedPath linkedPath_spec

/-- A figure marked as an illustration: a dot. -/
@[figure illustration] def markedSketch : Diagram :=
  { marks := [{ part := .guide, shape := .dot (0, 0) }] }

/-- A figure linked with `figure_proves`, the command's other name: the Dyck path `UUDD`. -/
@[figure] def aliasPath : Diagram := (LatticePath.ofDyck [true, true, false, false]).figure

/-- The figure draws four steps, ending at `(4, 0)`. -/
theorem aliasPath_spec :
    aliasPath.steps.map (fun (_, _, q) => q) = [(1, 1), (2, 2), (3, 1), (4, 0)] := by
  decide +kernel

figure_proves aliasPath aliasPath_spec

/-- A figure whose title claims something false and whose linked theorem is a disjunction with
`True`. -/
@[figure]
def vacuousOr : Diagram :=
  { marks := [{ part := .note 0, shape := .text "K(5,2) has 16 edges" (0, 0) .center }],
    title := "The Petersen graph" }

/-- True, and says nothing of the figure. -/
theorem vacuousOr_spec : True ∨ vacuousOr = vacuousOr := Or.inl trivial

figure_links vacuousOr vacuousOr_spec

/-- A figure named only in an unused hypothesis of its linked theorem. -/
@[figure]
def vacuousHypothesis : Diagram := { marks := [], title := "All primes are odd" }

/-- `1 = 1`, under a hypothesis about the figure that is not used. -/
theorem vacuousHypothesis_spec (_h : vacuousHypothesis = vacuousHypothesis) : 1 = 1 := rfl

figure_links vacuousHypothesis vacuousHypothesis_spec

/-- A figure whose linked theorem is a property every diagram has. -/
@[figure]
def vacuousBound : Diagram := { marks := [], title := "π = 3" }

/-- The number of marks is at least zero. -/
theorem vacuousBound_spec : vacuousBound.marks.length ≥ 0 := Nat.zero_le _

figure_links vacuousBound vacuousBound_spec

/-- The word of `pinnedPath`: `UD`. -/
def pinnedWord : List Bool := [true, false]

/-- A figure whose linked theorem writes it out: the Dyck path of `pinnedWord`. -/
@[figure] def pinnedPath : Diagram := (LatticePath.ofDyck pinnedWord).figure

/-- The figure is the Dyck path of the word `UD`, both written out, so the statement determines
the figure. -/
theorem pinnedPath_spec :
    pinnedPath = (LatticePath.ofDyck pinnedWord).figure ∧ pinnedWord = [true, false] :=
  ⟨rfl, rfl⟩

figure_links pinnedPath pinnedPath_spec

/-- The figure written out in terms of the word, which is not. -/
theorem pinnedPath_open : pinnedPath = (LatticePath.ofDyck pinnedWord).figure := rfl

/-- The word's pin mentions the word. -/
theorem pinnedPath_circular :
    pinnedPath = (LatticePath.ofDyck pinnedWord).figure ∧ pinnedWord = pinnedWord.take 2 :=
  ⟨rfl, rfl⟩

/-- The pins depend on a variable of the statement. -/
theorem pinnedPath_bound (w : List Bool) (h : pinnedWord = w) :
    pinnedPath = (LatticePath.ofDyck w).figure ∧ pinnedWord = w :=
  ⟨h ▸ rfl, h⟩

-- A statement determines its figure when it writes out the figure and every definition of the
-- local modules the value uses; one that leaves a definition open, pins a definition by itself,
-- or pins through a variable does not, and neither does a statement that names the figure only.
#guard_msgs in
run_cmd do
  let problem := fun (fig thm : Lean.Name) => Lean.Elab.Command.liftTermElabM
    (figurePinProblem? (`PILeanTest.Standing).isPrefixOf fig thm)
  if let some m ← problem `PILeanTest.Standing.pinnedPath `PILeanTest.Standing.pinnedPath_spec then
    throwError "the written-out statement is refused: {m}"
  for t in [`PILeanTest.Standing.pinnedPath_open, `PILeanTest.Standing.pinnedPath_circular,
      `PILeanTest.Standing.pinnedPath_bound] do
    if (← problem `PILeanTest.Standing.pinnedPath t).isNone then throwError "{t} is accepted"
  if (← problem `PILeanTest.Standing.linkedPath `PILeanTest.Standing.linkedPath_spec).isNone then
    throwError "a statement about the figure's steps is accepted"

/-- A figure with no linked theorem and no marking: a dot. -/
@[figure] def unmarkedSketch : Diagram :=
  { marks := [{ part := .guide, shape := .dot (1, 0) }] }

/-- A statement about the marked figure. -/
theorem markedSketch_marks : markedSketch.marks.length = 1 := rfl

/--
error: PILeanTest.Standing.markedSketch is marked @[figure illustration]; a figure with a linked theorem is not an illustration: remove the marking
-/
#guard_msgs in
figure_links markedSketch markedSketch_marks

/-- error: @[figure] takes no argument other than `illustration` -/
#guard_msgs in
/-- Not registered: the argument is not `illustration`. -/
@[figure linked] def badArgument : Diagram := { marks := [] }

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
  #[("standing: a figure with a linked theorem is linked, to its theorem",
      (entryOf "linkedPath").map (·.standing) ==
        some (.linked #["PILeanTest.Standing.linkedPath_spec"])),
    ("standing: figure_proves links as figure_links does",
      (entryOf "aliasPath").map (·.standing) ==
        some (.linked #["PILeanTest.Standing.aliasPath_spec"])),
    ("standing: theorems that say nothing of the figure are linked, and the word is linked",
      ["vacuousOr", "vacuousHypothesis", "vacuousBound"].all fun d =>
        (entryOf d).map (fun e => (e.standing.word, e.standing.theorems)) ==
          some ("linked", #[s!"PILeanTest.Standing.{d}_spec"])),
    ("standing: no standing is worded proved",
      entries.all fun e => e.standing.word == "linked" || e.standing.word == "illustration"),
    ("standing: a marked figure is a marked illustration",
      (entryOf "markedSketch").map (·.standing) == some (.illustration true)),
    ("standing: a figure neither linked nor marked is an unmarked illustration",
      (entryOf "unmarkedSketch").map (·.standing) == some (.illustration false)),
    ("standing: every output of a figure carries its standing",
      entries.all fun e => (e.outputs ()).all (·.standing == e.standing)),
    ("standing: --require-standing names the unmarked illustration only",
      unmarkedIllustrations entries == #["PILeanTest.Standing.unmarkedSketch"]),
    ("standing: the source record of a linked figure names its theorem",
      (sourceOf "linkedPath").map (fun s => (s.standing, s.theorems)) ==
        some (some "linked", some #["PILeanTest.Standing.linkedPath_spec"]) &&
        (sourceOf "linkedPath").any (·.fields.any (·.1 == "theorems")) &&
        !(sourceOf "linkedPath").any (·.fields.any (·.1 == "proves"))),
    ("standing: the source record of an illustration says so, with no theorem",
      (sourceOf "markedSketch").map (fun s => (s.standing, s.theorems)) ==
        some (some "illustration", none)),
    ("standing: a record that claims a link without a theorem cannot be written or read",
      (Source.validate { valid with standing := some "linked" } matches .error _) &&
        (Source.validate { valid with standing := some "proved", theorems := some #["A"] }
          matches .error _) &&
        (Source.ofFields (valid.fields.push ("standing", "linked")) matches .error _) &&
        (Source.ofFields (valid.fields.push ("standing", "proved")) matches .error _) &&
        (Source.ofFields (valid.fields ++ #[("standing", "illustration"), ("theorems", "T")])
          matches .error _) &&
        (Source.ofFields (valid.fields.push ("standing", "certain")) matches .error _) &&
        (Source.ofFields (valid.fields ++ #[("standing", "linked"), ("theorems", "A  B")])
          matches .error _) &&
        (Source.ofFields (valid.fields ++
          #[("standing", "linked"), ("theorems", "A"), ("proves", "A")]) matches .error _) &&
        (Source.ofFields (valid.fields ++
          #[("standing", "linked"), ("proves", "A"), ("proves", "A")]) matches .error _)),
    ("standing: a well-formed record is read back",
      (Source.ofFields (valid.fields ++
        #[("standing", "linked"), ("theorems", "[\"A\",\"B\"]")])).toOption ==
        some { valid with standing := some "linked", theorems := some #["A", "B"] }),
    ("standing: a record in the earlier form, names separated by spaces, is read",
      (Source.ofFields (valid.fields ++ #[("standing", "linked"), ("theorems", "A B")])).toOption ==
        some { valid with standing := some "linked", theorems := some #["A", "B"] }),
    ("standing: a record that writes proved and proves reads as linked with its theorems",
      (Source.ofFields (valid.fields ++ #[("standing", "proved"), ("proves", "A B")])).toOption ==
        some { valid with standing := some "linked", theorems := some #["A", "B"] }),
    ("standing: names with a space and with quotes are written and read back as they are",
      let ts := #["A.«b c»", "D.«e \"f\" g»", "H.i"]
      let r : Source := { valid with standing := some "linked", theorems := some ts }
      r.fields.contains ("theorems", "[\"A.«b c»\",\"D.«e \\\"f\\\" g»\",\"H.i\"]") &&
        (Source.ofFields r.fields).toOption == some r && r.validate matches .ok _),
    ("standing: a list of theorems that is empty, has an empty or a repeated name, or is not a \
        list of strings is refused",
      ["[]", "[\"\"]", "[\"A\",\"A\"]", "[\"A\",1]", "[\"A\"", "[[\"A\"]]", "{}"].all fun v =>
        Source.ofFields (valid.fields ++ #[("standing", "linked"), ("theorems", v)])
          matches .error _),
    ("standing: under the earlier key, only the earlier form is read",
      Source.ofFields (valid.fields ++ #[("standing", "linked"), ("proves", "[\"A\"]")])
        matches .error _)]

/-- A manifest entry of a linked figure whose theorems' names hold a space and quotes. -/
def quotedEntry : ManifestEntry :=
  { path := "M/fig.svg", format := "svg", bytes := 1,
    sha256 := String.ofList (List.replicate 64 'a'),
    fingerprint := String.ofList (List.replicate 64 'b'), module := "M", decl := "M.fig",
    file := "M.lean", line := 1, column := 0, version := "1", standing := some "linked",
    theorems := some #["M.«fig spec»", "M.«the \"fig\"»", "M.fig_spec"] }

/-- The manifest text of one entry in the format `pilean-manifest-2`, from its rendering in the
current format with the theorems `ts` written `spaced`. -/
def spacedManifest (m : ManifestEntry) (spaced : String) : String :=
  let t := Manifest.render #[{ m with theorems := none }]
  ((t.replace manifestFormat spacedManifestFormat).replace "\"standing\":\"linked\""
    s!"\"standing\":\"linked\",\"theorems\":\"{spaced}\"")

/-- Checks of the manifest's list of theorems: names with a space and quotes go through it as
they are, the earlier format's string of names is read, and a list in the wrong form for its
format is refused. -/
def manifestChecks : Array (String × Bool) :=
  let text := Manifest.render #[quotedEntry]
  let current := (Manifest.parse text.toUTF8).toOption == some #[quotedEntry]
  let plain := { quotedEntry with theorems := some #["M.a", "M.b"] }
  #[("standing: a manifest lists the theorems as a JSON array, names with a space and quotes \
        as they are",
      current &&
        (text.splitOn "\"theorems\":[\"M.«fig spec»\",\"M.«the \\\"fig\\\"»\",").length == 2),
    ("standing: a manifest of the earlier format, names separated by spaces, is read",
      (Manifest.parse (spacedManifest plain "M.a M.b").toUTF8).toOption == some #[plain]),
    ("standing: the earlier format's string of names is not read in the current format",
      Manifest.parse ((spacedManifest plain "M.a M.b").replace spacedManifestFormat
        manifestFormat).toUTF8 matches .error _),
    ("standing: a list of names is not read in the earlier format",
      Manifest.parse (text.replace manifestFormat spacedManifestFormat).toUTF8 matches .error _),
    ("standing: a manifest whose list of theorems repeats a name is refused",
      Manifest.parse (Manifest.render #[{ quotedEntry with
        theorems := some #["M.a", "M.a"] }]).toUTF8 matches .error _)]

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
    | .ok s => if s.standing != m.standing || s.theorems != m.theorems || m.standing.isNone then
        filesAgree := false
    | .error _ => filesAgree := false
  let lines ← verifyDirEntries (root / "a")
  let recorded := match lines with
    | .ok vs => vs.toList.map fun ((p, v, m) : String × Verdict × Option ManifestEntry) =>
        s!"{v.text}: {p}{(m.map recordedStanding).getD ""}"
    | .error _ => []
  -- a manifest whose standing is malformed is refused as a whole
  let bad := (Manifest.render (manifest.map fun m => { m with theorems := none })).toUTF8
  let refused := (Manifest.parse bad) matches .error _
  -- a manifest in the earlier format, with `proved` and `proves`, reads as the current one
  let text := (String.fromUTF8? (Manifest.render manifest).toUTF8).getD ""
  let old := (((text.replace manifestFormat oldManifestFormat).replace "\"standing\":\"linked\""
    "\"standing\":\"proved\"").replace "\"theorems\":[\"" "\"proves\":\"").replace "\"]}" "\"}"
  let oldRead := (Manifest.parse old.toUTF8).toOption == some manifest &&
    (old.splitOn "\"proved\"").length > 1
  IO.FS.removeDirAll root
  return #[
    ("standing: --require-standing refuses the unmarked illustration, naming it",
      (strictMsg.splitOn "unmarkedSketch is an illustration").length == 2 &&
        (strictMsg.splitOn "markedSketch is").length == 2),
    ("standing: --require-standing builds the linked and the marked figures", ok == 0),
    ("standing: without the option every figure builds", all == 0),
    ("standing: each file records the standing its manifest entry lists", filesAgree),
    ("standing: pilean-verify repeats the recorded standing on its ok lines",
      recorded.any (fun l => l.startsWith "ok: PILeanTest/Standing/linkedPath.svg [recorded: \
        linked to PILeanTest.Standing.linkedPath_spec]") &&
        recorded.any (fun l => l.startsWith "ok: PILeanTest/Standing/markedSketch.svg \
          [recorded: illustration]")),
    ("standing: a manifest that lists a linked figure without its theorem is refused", refused),
    ("standing: a manifest of the earlier format, with proved and proves, is read", oldRead)]

end PILeanTest.Standing
