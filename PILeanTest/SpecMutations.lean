/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# Changes to a figure that must break its specification

A figure's specification writes out what the figure draws, so that a change to the figure breaks
the build. `SpecMutation` describes one such change: edits to the source file of the figure, made
in its definitions (after an anchor and before the specification), and the specification they
must break. `check` compiles a copy of the file with the edits, with the `lean` of the build
(`LEAN`, which `lake test` sets), and holds when the copy fails to compile with every error inside
the specification or its `figure_proves` line, and the unchanged copy compiles. The changes of
the core's figures are `mutations`; the LeAnTeX package checks its own with the same `check`.

## Main definitions

* `SpecMutation`, `SpecMutation.apply`, `errorLines`, `check`, `checkAll`, `mutations`,
  `ioChecks`.
-/

namespace PILeanTest.SpecMutations

/-- A change to the definitions of a figure that its specification must catch. -/
structure SpecMutation where
  /-- The source file, relative to the package's root. -/
  file : System.FilePath
  /-- What the change does, as the check names it. -/
  what : String
  /-- The text after which the edits are made: it occurs once in the file, before the
  specification. -/
  anchor : String
  /-- Each edit replaces the first occurrence of its first text after the anchor with its
  second; every occurrence replaced must end before the specification. -/
  edits : List (String × String)
  /-- The name of the specification, as written after `theorem`. -/
  spec : String

/-- The byte position of the first occurrence of `pat` in `s` at or after `start`. -/
def findFrom (s pat : String) (start : Nat) : Option Nat := Id.run do
  let b := s.toUTF8
  let p := pat.toUTF8
  if p.size == 0 then return none
  let mut i := start
  while i + p.size ≤ b.size do
    if (List.range p.size).all fun k => b[i + k]! == p[k]! then return some i
    i := i + 1
  return none

/-- The number of occurrences of `pat` in `s`. -/
def occurrences (s pat : String) : Nat := (s.splitOn pat).length - 1

/-- The text of `s` between the byte positions `a` and `b`. -/
def slice (s : String) (a b : Nat) : String :=
  (String.fromUTF8? (s.toUTF8.extract a b)).getD ""

/-- The file's text with the edits made, or why they cannot be: the anchor or the specification
does not occur exactly once, an edit's text is not found after the anchor, or an edit would
reach into the specification. -/
def SpecMutation.apply (m : SpecMutation) (text : String) : Except String String := do
  if occurrences text m.anchor != 1 then throw s!"the anchor {m.anchor.quote} is not unique"
  let specHead := s!"theorem {m.spec} "
  if occurrences text specHead != 1 then throw s!"no single theorem {m.spec}"
  let mut t := text
  for (old, new) in m.edits do
    let some a := findFrom t m.anchor 0 | throw "the anchor is gone"
    let some sp := findFrom t specHead 0 | throw "the specification is gone"
    let some i := findFrom t old a | throw s!"{old.quote} does not occur after the anchor"
    if i + old.utf8ByteSize > sp then throw s!"{old.quote} is not before the specification"
    t := slice t 0 i ++ new ++ slice t (i + old.utf8ByteSize) t.utf8ByteSize
  return t

/-- The lines (from 1) of the errors in the output of `lean` for the file `path`. -/
def errorLines (out : String) (path : String) : Array Nat :=
  (out.splitOn "\n").toArray.filterMap fun l =>
    if l.startsWith (path ++ ":") then
      match ((l.drop (path.length + 1)).toString.splitOn ":") with
      | line :: _ :: rest => if (":".intercalate rest).trimAsciiStart.startsWith "error" then
          line.toNat? else none
      | _ => none
    else none

/-- The lines (from 1) of the specification in `text`: from its `theorem` line to the
`figure_proves` line that names it. -/
def specLines (text spec : String) : Option (Nat × Nat) := do
  let ls := (text.splitOn "\n").toArray
  let first ← ls.findIdx? (·.startsWith s!"theorem {spec} ")
  let last ← ls.findIdx? fun l => l.startsWith "figure_proves " && l.endsWith s!" {spec}"
  return (first + 1, last + 1)

/-- Runs the `lean` of the build on a file; its exit code and its output. -/
def compile (lean : String) (path : System.FilePath) : IO (UInt32 × String) := do
  let r ← IO.Process.output { cmd := lean, args := #[path.toString] }
  return (r.exitCode, r.stdout ++ r.stderr)

/-- Whether the change breaks the specification and nothing else: the copy with the edits fails
to compile, with at least one error and every error inside the specification's lines; and the
copy without them compiles. The copies are written to `scratch`. -/
def check (lean : String) (scratch : System.FilePath) (m : SpecMutation) (k : Nat) :
    IO (Except String Unit) := do
  let text ← IO.FS.readFile m.file
  let mutated ← match m.apply text with
    | .ok t => pure t
    | .error e => return .error e
  let some (lo, hi) := specLines mutated m.spec | return .error s!"no lines for {m.spec}"
  let stem := (m.file.fileStem.getD "Spec")
  let plain := scratch / s!"{stem}Plain{k}.lean"
  let changed := scratch / s!"{stem}Changed{k}.lean"
  IO.FS.writeFile plain text
  IO.FS.writeFile changed mutated
  let (c0, out0) ← compile lean plain
  if c0 != 0 || !(errorLines out0 plain.toString).isEmpty then
    return .error s!"the unchanged copy does not compile: {(out0.take 400).toString}"
  let (c1, out1) ← compile lean changed
  let errs := errorLines out1 changed.toString
  if c1 == 0 || errs.isEmpty then return .error "the changed copy compiles"
  if errs.any (fun l => l < lo || l > hi) then
    return .error s!"an error outside {m.spec} (lines {lo} to {hi}): errors at {errs}"
  return .ok ()

/-- The checks of the changes, named `the change breaks SPEC: WHAT`, run side by side; each fails
with its reason printed. Without `LEAN` in the environment (set by `lake test` and `lake env`) the
check fails instead of running a `lean` of unknown origin. -/
def checkAll (ms : Array SpecMutation) : IO (Array (String × Bool)) := do
  let some lean ← IO.getEnv "LEAN"
    | return #[("the changes to the figures are checked (LEAN is not set)", false)]
  let scratch ← IO.FS.createTempDir
  let tasks ← ms.zipIdx.mapM fun (m, k) => IO.asTask (check lean scratch m k)
  let mut out := #[]
  for (m, t) in ms.zip tasks do
    let name := s!"the change breaks {m.spec}: {m.what}"
    match t.get with
    | .ok (.ok ()) => out := out.push (name, true)
    | .ok (.error why) => IO.eprintln s!"{name}: {why}"; out := out.push (name, false)
    | .error e => IO.eprintln s!"{name}: {e}"; out := out.push (name, false)
  IO.FS.removeDirAll scratch
  return out

/-- The changes to the core's figures with specifications (`PILeanTest.Examples` and
`PILeanTest.PlaneExact`). -/
def mutations : Array SpecMutation :=
  let disks : System.FilePath := "PILeanTest" / "Examples.lean"
  let plane : System.FilePath := "PILeanTest" / "PlaneExact.lean"
  #[{ file := disks, what := "the point E is not drawn", anchor := "def items : Array Item :=",
      edits := [("lowerCrossing, pointNegE, pointE,", "lowerCrossing, pointNegE,")],
      spec := "disks_spec" },
    { file := disks, what := "the label E is at -E", anchor := "def items : Array Item :=",
      edits := [("Plane.Exact.label \"E\" chordEnd", "Plane.Exact.label \"E\" (-chordEnd)")],
      spec := "disks_spec" },
    { file := disks, what := "the disks' colours are swapped", anchor := "def leftDisk : Item :=",
      edits := [("leftCentre critical |>.accent 0", "leftCentre critical |>.accent 1"),
        ("rightCentre critical |>.accent 1", "rightCentre critical |>.accent 0")],
      spec := "disks_spec" },
    { file := disks, what := "the angle mark's radius is 50 pixels",
      anchor := "def items : Array Item :=", edits := [("(some 46)", "(some 50)")],
      spec := "disks_spec" },
    { file := disks, what := "the upper crossing is a dot",
      anchor := "def upperCrossing : Item :=", edits := [("|>.marker .ring", "|>.marker .dot")],
      spec := "disks_spec" },
    { file := plane, what := "the point E is at 2E", anchor := "def items : Array Item :=",
      edits := [("pointZero, pointE,", "pointZero, Plane.Exact.point (E + E),")],
      spec := "reference_spec" },
    { file := plane, what := "the left circle's radius is 2", anchor := "def leftCircle : Item :=",
      edits := [("Plane.Exact.disk left R", "Plane.Exact.disk left (⟨⟨4, 0⟩⟩ : SqrtOf QSqrt5)")],
      spec := "reference_spec" },
    { file := plane, what := "the corners do not record the lens",
      anchor := "def cornerPoint (c : Zeta5) : Item :=",
      edits := [("\n    |>.incident .on \"the lens\"", "")], spec := "reference_spec" },
    { file := plane, what := "the first piece and its label are drawn in the other order",
      anchor := "def items : Array Item :=",
      edits := [("pieceS1, pieceLabel (-E) (-F) \"s1\" \"S₁\",",
        "pieceLabel (-E) (-F) \"s1\" \"S₁\", pieceS1,")], spec := "reference_spec" },
    { file := plane, what := "the second piece's label reads S₄",
      anchor := "def items : Array Item :=", edits := [("\"s2\" \"S₂\"", "\"s2\" \"S₄\"")],
      spec := "reference_spec" },
    { file := plane, what := "the steps are in accent 1", anchor := "def stepItems (j : Nat)",
      edits := [("then .accent 0 else", "then .accent 1 else")], spec := "zetaSteps_spec" },
    { file := plane, what := "the label of ζ² reads ζ2", anchor := "def stepLabel (j : Nat)",
      edits := [("\"ζ²\"", "\"ζ2\"")], spec := "zetaSteps_spec" },
    { file := plane, what := "the points do not record the window",
      anchor := "def stepPoint (j : Nat) : Item :=",
      edits := [("Plane.Exact.pointNearDisk (Zeta5.pow j) windowCentre windowRadius \"the window\"",
        "Plane.Exact.point (Zeta5.pow j)")], spec := "zetaSteps_spec" }]

/-- The checks of `mutations`. -/
def ioChecks : IO (Array (String × Bool)) := checkAll mutations

end PILeanTest.SpecMutations
