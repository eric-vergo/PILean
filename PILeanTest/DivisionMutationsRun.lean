/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanTest.Motion
import PILeanTest.MotionPanels

/-!
# One motion checked against a writer that divides its timeline unsoundly

`lean --run PILeanTest/DivisionMutationsRun.lean NAME` is what `PILeanTest.DivisionMutations` runs,
with a search path in which `PILean.Plane.MotionPlan` is a copy whose division has been changed so
that it is unsound: the interpreter then runs the motions' code against the changed writer. For
the test motion `NAME`, at each check level (`fail`, `warn`, `ignore`), it prints an `ok:` or a
`FAIL:` line for each of: the report has segments divided unsoundly; what stops the checked motion
is exactly their messages; every output (the APNG and the GIF included) fails, with no inline
picture and no page data; the animation fails and no rendition has a moving picture for a page.
The CPU time it may take is bounded by its caller.
-/

open PILean PILean.Plane PILean.Trust

/-- The test motions this driver knows, by name: the single motions, and the picture of panels
as a checked motion (with its report's unsound segments). -/
def motionsOf (name : String) (l : CheckLevel) :
    Option (Array Anim.SegKind × CheckedMotion) :=
  let single := fun (m : Motion) =>
    let m := { m with checks := l }
    some (m.report.unsound, m.checked)
  match name with
  | "announce" => single PILeanTest.MotionChecks.announceMotion
  | "crowd" => single PILeanTest.MotionChecks.crowdMotion
  | "steep" => single PILeanTest.MotionChecks.steepMotion
  | "sampled" => single PILeanTest.MotionChecks.sampledMotion
  | "announce-panels" =>
    let P := { PILeanTest.MotionPanelsChecks.announcePanels with checks := l }
    some (P.report.unsound, P.checked)
  | _ => none

/-- The checks of the motion `name` at the level `l`, each with its name. -/
def checksAt (name : String) (l : CheckLevel) : Array (String × Bool) :=
  match motionsOf name l with
  | none => #[(s!"{name} is a test motion", false)]
  | some (unsound, c) =>
    let msgs := (unsoundProblems unsound).map (·.message)
    let outs := motionOutputs c (rasters := true)
    let at_ := s!"{name} at {reprStr l}"
    #[(s!"{at_}: its timeline is divided unsoundly", !unsound.isEmpty),
      (s!"{at_}: what stops it is exactly the unsound segments", c.stops == msgs),
      (s!"{at_}: every output fails, with no inline picture and no page data",
        !outs.isEmpty && outs.all fun o =>
          (o.bytes ()).toOption.isNone && (o.inline ()).isNone && (o.motionPage ()).isNone),
      (s!"{at_}: its animation fails and no rendition has a moving picture",
        (c.animation 30).toOption.isNone && c.main.live.isEmpty &&
          c.narrow.all (·.live.isEmpty))]

/-- Prints the checks of the motion named by the argument at every level; exits with status 1
when one fails. -/
def main (args : List String) : IO UInt32 := do
  let [name] := args | IO.eprintln "usage: DivisionMutationsRun NAME"; return 2
  let mut failed := false
  for l in [CheckLevel.fail, .warn, .ignore] do
    for (what, ok) in checksAt name l do
      IO.println s!"{if ok then "ok" else "FAIL"}: {what}"
      if !ok then failed := true
  return if failed then 1 else 0
