/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanTest.Bounds

/-!
# Changes to the writer's division that must stop the motions they reach

A motion's timeline is divided by its writer (`PILean.Plane.divisionOf`); a division that is not
sound must stop the motion at every check level, promptly (`PILean.Plane.unsoundProblems`,
`PILean.Plane.MotionDivision.soundOn`). `DivisionMutation` is one change to
`PILean/Plane/MotionPlan.lean` that makes some divisions unsound, with the test motions it
reaches. `check` compiles a copy of the file with the change into a search path that has the
package's build for everything else (symbolic links), and for each motion it reaches runs
`PILeanTest/DivisionMutationsRun.lean` with Lean's interpreter on that search path, under a CPU
limit and a wall-clock watchdog: the interpreter runs the imported code of the motions against
the changed writer. Each run must print only `ok:` lines and exit with status 0, within
`maxUserMs` of user CPU time.

## Main definitions

* `DivisionMutation`, `mutations`, `overlay`, `runBounded`, `check`, `ioChecks`.
-/

namespace PILeanTest.DivisionMutations

open PILeanTest.Bounds (userTime)

/-- A change to the writer's division and the test motions it makes unsound (the names
`PILeanTest/DivisionMutationsRun.lean` knows). -/
structure DivisionMutation where
  /-- What the change does, as the check names it. -/
  what : String
  /-- The text replaced, which occurs once in the file, and its replacement. -/
  edit : String × String
  /-- The test motions the change reaches. -/
  motions : Array String

/-- The file the changes are made in, relative to the package's root. -/
def file : System.FilePath := "PILean" / "Plane" / "MotionPlan.lean"

/-- The changes: a part of a step cut by a fade's window that runs backwards, the parts of a rest
in reverse order, and the samples of a morph in reverse order. -/
def mutations : Array DivisionMutation :=
  #[{ what := "the parts of a step cut by its windows run backwards",
      edit := ("(easedParts s.easing maxEasedDepth a b)", "(easedParts s.easing maxEasedDepth b a)"),
      motions := #["announce", "steep", "announce-panels"] },
    { what := "the parts of a rest are in reverse order",
      edit := ("      ((starts.zip ends).map fun (a, b) =>
          (b, if ws.contains (a, b) then d.restEasing else .linear),",
        "      (((starts.zip ends).map fun (a, b) =>
          (b, if ws.contains (a, b) then d.restEasing else .linear)).reverse,"),
      motions := #["announce", "crowd", "announce-panels"] },
    { what := "the samples of a morph are in reverse order",
      edit := ("(τ (i + 1), straightEasing)", "(τ (n - i), straightEasing)"),
      motions := #["sampled"] }]

/-- The bound on the user CPU time of one run, in milliseconds: the interpreter's start and the
checks of one motion at three levels took 0.8 to 4 s; a division whose parts blow up takes hours
(a part of a step halved 16 times alone took 27 s in the interpreter). -/
def maxUserMs : Nat := 20000

/-- The wall-clock time after which a run is killed, in milliseconds. -/
def maxWallMs : Nat := 300000

/-- A search path `dir` that is the build `lib` (the directory with `PILean.olean`) except for
`PILean/Plane/MotionPlan.olean`, which is left out for the changed copy: symbolic links to every
other entry. -/
def overlay (lib dir : System.FilePath) : IO Bool := do
  let script := "set -e; b=$1; d=$2; mkdir -p \"$d/PILean/Plane\"; " ++
    "ln -s \"$b/PILean.olean\" \"$d/PILean.olean\"; ln -s \"$b/PILeanTest\" \"$d/PILeanTest\"; " ++
    "for e in \"$b\"/PILean/*; do n=${e##*/}; [ \"$n\" = Plane ] || ln -s \"$e\" \"$d/PILean/$n\"; " ++
    "done; for e in \"$b\"/PILean/Plane/*; do n=${e##*/}; case $n in MotionPlan.*) ;; " ++
    "*) ln -s \"$e\" \"$d/PILean/Plane/$n\";; esac; done"
  let r ← IO.Process.output
    { cmd := "/bin/sh", args := #["-c", script, "sh", lib.toString, dir.toString] }
  return r.exitCode == 0

/-- What a bounded run gave: its exit status (none if the watchdog killed it), its standard
output, and its user CPU time in milliseconds when `/usr/bin/time` reported it. -/
structure Run where
  /-- The exit status. -/
  status : Option UInt32
  /-- The standard output. -/
  out : String
  /-- The user CPU time. -/
  userMs : Option Nat

/-- Runs `cmd args` with the environment `env` in its own process group under a CPU limit of
`cpuS` seconds, the group killed after `wallMs` milliseconds, measured with `/usr/bin/time`; its
outputs go to files in `scratch` named after `tag`. -/
def runBounded (cmd : String) (args : Array String) (env : Array (String × Option String))
    (cpuS wallMs : Nat) (scratch : System.FilePath) (tag : String) : IO Run := do
  let outF := scratch / s!"{tag}.out"
  let timeF := scratch / s!"{tag}.time"
  let flag := if System.Platform.isOSX then "-l" else "-v"
  let script := s!"ulimit -t {cpuS}; o=$1; t=$2; shift 2; export o; " ++
    s!"exec /usr/bin/time {flag} /bin/sh -c 'exec \"$@\" > \"$o\" 2>&1' sh \"$@\" 2> \"$t\""
  let child ← IO.Process.spawn
    { cmd := "/bin/sh", setsid := true, env := env,
      args := #["-c", script, "sh", outF.toString, timeF.toString, cmd] ++ args }
  let mut status : Option UInt32 := none
  for _ in [0:wallMs / 50 + 1] do
    if let some s ← child.tryWait then
      status := some s
      break
    IO.sleep 50
  if status.isNone then
    let _ ← IO.Process.output { cmd := "/bin/kill", args := #["-9", "--", s!"-{child.pid}"] }
    let _ ← child.wait
  let out ← try IO.FS.readFile outF catch _ => pure ""
  let tm ← try IO.FS.readFile timeF catch _ => pure ""
  return { status, out, userMs := userTime tm }

/-- Whether the change `m` stops every motion it reaches, promptly: the copy of the writer with
the change compiles (with the `lean` of the build, `lean`, on the search path `path`, whose entry
`lib` is the package's build), and each motion's run passes within the bounds. The copies are
made in `scratch`. -/
def check (lean : String) (lib : System.FilePath) (path : List System.FilePath)
    (scratch : System.FilePath) (m : DivisionMutation) (k : Nat) :
    IO (Except String Unit) := do
  let text ← IO.FS.readFile file
  let (old, new) := m.edit
  if (text.splitOn old).length != 2 then return .error s!"{old.quote} does not occur once"
  let root := scratch / s!"src{k}"
  let dir := scratch / s!"lib{k}"
  let copy := root / file
  IO.FS.createDirAll (copy.parent.getD root)
  IO.FS.writeFile copy (text.replace old new)
  unless ← overlay lib dir do return .error "the search path cannot be made"
  let sep := toString System.SearchPath.separator
  let buildPath := sep.intercalate (path.map toString)
  let c ← IO.Process.output
    { cmd := lean, env := #[("LEAN_PATH", some buildPath)],
      args := #[s!"--root={root}", "-o", (dir / "PILean" / "Plane" / "MotionPlan.olean").toString,
        copy.toString] }
  if c.exitCode != 0 then
    return .error s!"the changed copy does not compile: {(c.stdout ++ c.stderr).take 400}"
  let others := path.filter (· != lib)
  let runPath := sep.intercalate ((dir :: others).map toString)
  for name in m.motions do
    let r ← runBounded lean #["--run", "PILeanTest/DivisionMutationsRun.lean", name]
      #[("LEAN_PATH", some runPath)] (maxUserMs / 1000) maxWallMs scratch s!"run{k}-{name}"
    let fails := (r.out.splitOn "\n").filter (!·.startsWith "ok:") |>.filter (!·.isEmpty)
    if r.status != some 0 || !fails.isEmpty then
      return .error s!"{name}: status {r.status}: {"; ".intercalate (fails.take 4)}"
    match r.userMs with
    | none => return .error s!"{name}: no CPU time was measured"
    | some t =>
      if t > maxUserMs then return .error s!"{name}: {t} ms of CPU time"
      IO.println s!"division mutations: {m.what}: {name} stopped at every level, user {t} ms"
  return .ok ()

/-- The checks of the changes, named `the change stops the motions it reaches: WHAT`, run side by
side; each fails with its reason printed. Without `LEAN` and a `LEAN_PATH` holding the package's
build (both set by `lake test`) the check fails instead of running a `lean` of unknown origin. -/
def ioChecks : IO (Array (String × Bool)) := do
  let some lean ← IO.getEnv "LEAN"
    | return #[("the changes to the writer's division are checked (LEAN is not set)", false)]
  let path := System.SearchPath.parse ((← IO.getEnv "LEAN_PATH").getD "")
  let some lib ← path.findM? fun p => (p / "PILean.olean").pathExists
    | return #[("the changes to the writer's division are checked (no build on LEAN_PATH)",
        false)]
  let scratch ← IO.FS.createTempDir
  let tasks ← mutations.zipIdx.mapM fun (m, k) =>
    IO.asTask (check lean lib path scratch m k)
  let mut out := #[]
  for (m, t) in mutations.zip tasks do
    let name := s!"the change stops the motions it reaches: {m.what}"
    match t.get with
    | .ok (.ok ()) => out := out.push (name, true)
    | .ok (.error why) => IO.eprintln s!"{name}: {why}"; out := out.push (name, false)
    | .error e => IO.eprintln s!"{name}: {e}"; out := out.push (name, false)
  -- `rm` removes the links themselves, never what they point to
  let _ ← IO.Process.output { cmd := "/bin/rm", args := #["-rf", "--", scratch.toString] }
  return out

end PILeanTest.DivisionMutations
