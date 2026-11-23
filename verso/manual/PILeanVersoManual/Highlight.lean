/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import SubVerso.Module
import SubVerso.Module.Decl
import PILeanVersoManual.PageData

/-!
# The highlighted source of a figure's code

A figure's page shows its declarations as highlighted Lean, with the hovers Lean's elaborator
gives each name. The environment of the site's generator does not hold the source, so it is read
from the per-module JSON files that SubVerso's `highlighted` module facet writes into the
workspace's build folder (`.lake/build/highlighted/<Module>.json`), as Verso Blueprint does for its
declaration sources. `prepare` runs one `lake build +M:highlighted …` for the modules of the pages'
declarations, with the `lake` the generator was started by (the variable `LAKE`, which `lake exe`
sets); without it nothing is run and the pages show signatures, saying so.

Each module file is read only if it is a regular file of at most `maxHighlightedBytes`, and only
for a module name whose components are neither empty nor `.` nor `..` and hold no `/`, so a page
reads nothing outside the build folder.

## Main definitions

* `prepare`, `declCode?`: building and reading the modules' highlighted source
* `plainCode`, `takeLines`, `statementPart`, `withoutDocComment`: what a page shows of a command
-/

namespace PILeanVerso

open Lean SubVerso.Highlighting SubVerso.Module

/-- The largest highlighted-module file a page reads. -/
def maxHighlightedBytes : Nat := 64 * 1024 * 1024

/-- Whether a module name can name a file of the build folder: every component is a non-empty
string other than `.` and `..`, without `/`, `\` or a NUL. -/
def safeModuleName (m : Name) : Bool :=
  !m.isAnonymous && m.components.all fun c => match c with
    | .str .anonymous s => !s.isEmpty && s != "." && s != ".." &&
        !s.any (fun ch => ch == '/' || ch == '\\' || ch == '\x00')
    | _ => false

/-- The file the `highlighted` facet writes for the module `m` in the workspace at `root`. -/
def highlightedPath (root : System.FilePath) (m : Name) : System.FilePath :=
  (m.components.foldl (init := root / ".lake" / "build" / "highlighted")
    fun p c => p / c.toString (escape := false)).addExtension "json"

/-- The highlighted modules loaded so far (`none`: building or reading it failed). -/
initialize highlightedRef : IO.Ref (Std.HashMap Name (Option SubVerso.Module.Module)) ← IO.mkRef {}

/-- Reads the highlighted module file `p`: a regular file of at most `maxHighlightedBytes`. -/
def readModule (p : System.FilePath) : IO (Except String SubVerso.Module.Module) := do
  try
    let md ← p.symlinkMetadata
    if md.type != .file then return .error s!"{p.fileName.getD ""}: not a regular file"
    if md.byteSize.toNat > maxHighlightedBytes then
      return .error s!"{p.fileName.getD ""}: larger than {maxHighlightedBytes} bytes"
    let text ← IO.FS.readFile p
    match Json.parse text with
    | .error e => return .error s!"invalid JSON: {e}"
    | .ok j => return SubVerso.Module.Module.fromJson? j
  catch e => return .error (toString e)

/-- Builds and loads the highlighted source of the modules `mods` (those not loaded yet) of the
workspace in the working directory. Returns the warnings: why a module has no highlighted source.
Without `LAKE` in the environment nothing is built and every module is left without one. -/
def prepare (mods : Array Name) : IO (Array String) := do
  let loaded ← highlightedRef.get
  let todo := mods.foldl (init := #[]) fun acc m =>
    if loaded.contains m || acc.contains m || !safeModuleName m then acc else acc.push m
  if todo.isEmpty then return #[]
  let some lake ← IO.getEnv "LAKE"
    | highlightedRef.modify fun h => todo.foldl (fun h m => h.insert m none) h
      return #["the highlighted source was not built: LAKE is not set (run the generator with \
        lake exe); the figures' pages show signatures"]
  let out ← IO.Process.output {
    cmd := lake, args := #["build", "--no-ansi"] ++ todo.map (s!"+{·}:highlighted") }
  let mut warnings := #[]
  let failed := out.exitCode != 0
  let root ← IO.currentDir
  let mut h := ← highlightedRef.get
  let mut missing := #[]
  for m in todo do
    match ← readModule (highlightedPath root m) with
    | .ok mod => h := h.insert m (some mod)
    | .error e =>
      if failed then missing := missing.push m else warnings := warnings.push s!"{m}: {e}"
      h := h.insert m none
  highlightedRef.set h
  if failed then
    let names := ", ".intercalate ((missing.extract 0 10).toList.map toString)
    warnings := warnings.push s!"building the highlighted source failed (exit {out.exitCode}); \
      the pages of the figures in {missing.size} modules show signatures: {names}\
      {if missing.size > 10 then ", …" else ""} (`lake build +M:highlighted` says why)"
  return warnings

/-- The highlighted command that declares `d`, if its module's source was loaded. -/
def declCode? (d : CodeDecl) : IO (Option Highlighted) := do
  let some (some mod) := (← highlightedRef.get)[d.module.toName]? | return none
  let pos : Option Lean.Position := if d.line > 0 then some ⟨d.line, d.column⟩ else none
  return (mod.findDecl? d.name.toName pos).map (·.code)

/-! ### What a page shows of a command -/

/-- The code without proof states, messages and points: the tokens and the text, which is what a
page shows (proof states would multiply its size). -/
partial def plainCode : Highlighted → Array Highlighted
  | .seq hs => hs.flatMap plainCode
  | .span _ h => plainCode h
  | .tactics _ _ _ h => plainCode h
  | .point .. => #[]
  | h@(.text s) => if s.isEmpty then #[] else #[h]
  | h => #[h]

/-- The first `n` lines of the code, and whether lines were left out. -/
def takeLines (n : Nat) (hs : Array Highlighted) : Array Highlighted × Bool := Id.run do
  let mut out := #[]
  let mut lines := 0
  for h in hs do
    match h with
    | .text s | .unparsed s =>
      let parts := s.splitOn "\n"
      let room := n - lines
      if parts.length - 1 < room then
        out := out.push h
        lines := lines + (parts.length - 1)
      else
        out := out.push (.text ("\n".intercalate (parts.take room)))
        return (out, true)
    | _ => out := out.push h
  return (out, false)

private def tokenText? : Highlighted → Option String
  | .token t => some t.content
  | _ => none

private def blank : Highlighted → Bool
  | .text s | .unparsed s => s.all Char.isWhitespace
  | _ => false

/-- The code without a leading doc comment and the white space around it. -/
def withoutDocComment (hs : Array Highlighted) : Array Highlighted := Id.run do
  let mut i := 0
  while i < hs.size && blank hs[i]! do i := i + 1
  if let some (.token ⟨.docComment, _⟩) := hs[i]? then
    i := i + 1
    while i < hs.size && blank hs[i]! do i := i + 1
  return hs.extract i hs.size

/-- The statement of a theorem's command: everything before its first `:=` outside brackets,
without the doc comment; `none` if it has no such `:=`. -/
def statementPart (hs : Array Highlighted) : Option (Array Highlighted) := Id.run do
  let hs := withoutDocComment hs
  let opens := ["(", "[", "{", "⦃", "⟨", "⟦"]
  let closes := [")", "]", "}", "⦄", "⟩", "⟧"]
  let mut depth := 0
  for h : i in [0:hs.size] do
    if let some t := tokenText? hs[i] then
      if opens.contains t then depth := depth + 1
      else if closes.contains t then depth := depth - 1
      else if t == ":=" && depth == 0 then
        let stmt := hs.extract 0 i
        -- trailing white space before `:=`
        let stmt := match stmt.back? with
          | some (.text s) => stmt.pop.push (.text s.trimAsciiEnd.toString)
          | _ => stmt
        return some stmt
  return none

end PILeanVerso
