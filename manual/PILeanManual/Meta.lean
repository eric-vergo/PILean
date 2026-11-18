/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual

/-!
# The manual's own markup

* ```` ```leanResult name ``` ```` (an empty code block): every message that the elaborated
  example `` ```lean (name := name) `` produced when the manual was built, shown as Lean
  output. Nothing is written by hand: what the page shows is what the build printed, so a change
  of the library that changes a result changes the page, and an example that stops compiling
  fails the build.
* `{api}` followed by a module name in backticks: the name, linked to the module's page in the
  API reference. The module must be one of the core's and imported where the role is used, so a
  renamed or removed module fails the build.
* `{sourceFile}` followed by a path in backticks: a file of the repository, by its path from the
  repository's root. The file must exist when the manual is built.
* `{inSource "path"}` followed by a declaration name in backticks: a declaration of one of the
  repository's optional packages, which this manual does not build (it would need their
  dependencies). The file must exist and declare the name's last component (`theorem`, `lemma`
  or `def` followed by it, or by the whole name), so a rename breaks the build; the statement
  itself is not elaborated here.
-/

namespace PILeanManual

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean
open Lean.Doc.Syntax

/-- The argument of `leanResult`: the name of an elaborated example. -/
structure LeanResultArgs where
  /-- The example's name, as given by `(name := …)`. -/
  name : Ident

instance : FromArgs LeanResultArgs DocElabM where
  fromArgs := LeanResultArgs.mk <$> .positional `name .ident "the example's name"

/-- Shows every message of the elaborated example `name`, as the build produced it; the block's
own text must be empty. -/
@[code_block]
def leanResult : CodeBlockExpanderOf LeanResultArgs
  | ⟨x⟩, str => do
    unless str.getString.trimAscii.isEmpty do
      throwErrorAt str "leanResult shows what the build produced: leave the block empty"
    let msgs ← getOutputs x
    if msgs.isEmpty then
      throwErrorAt x "the example {x.getId} produced no output"
    let blocks : Array Term ← msgs.toArray.mapM fun msg =>
      `(Verso.Doc.Block.other {Verso.Genre.Manual.InlineLean.Block.leanOutput with
          data := ToJson.toJson ($(quote msg), false, ([] : List Name))}
        #[Verso.Doc.Block.code $(quote msg.toString)])
    ``(Verso.Doc.Block.concat #[$blocks,*])

/-- The text of a role's argument, which must be one code span. -/
def codeArg (args : TSyntaxArray `inline) : DocElabM (Syntax × String) := do
  let #[arg] := args | throwError "expected one code span"
  let `(inline|code( $s:str )) := arg | throwErrorAt arg "expected a code span"
  return (arg, s.getString)

/-- A core module's name, linked to its page in the API reference (see the module docstring). -/
@[role]
def api : RoleExpanderOf Unit
  | (), args => do
    let (stx, nm) ← codeArg args
    let mod := nm.toName
    unless mod == `PILean || (`PILean).isPrefixOf mod do
      throwErrorAt stx "{nm} is not a module of PILean's core"
    if (← getEnv).getModuleIdx? mod |>.isNone then
      throwErrorAt stx "the module {nm} is not imported here (or does not exist)"
    ``(Verso.Doc.Inline.other (Verso.Genre.Manual.Inline.ref $(quote ("api-" ++ nm)) none none)
        #[Verso.Doc.Inline.code $(quote nm)])

/-- A file of the repository, by its path from the repository's root; it must exist. -/
@[role]
def sourceFile : RoleExpanderOf Unit
  | (), args => do
    let (stx, path) ← codeArg args
    if path.startsWith "/" || (path.splitOn "..").length > 1 then
      throwErrorAt stx "{path}: give a path inside the repository"
    unless ← (System.FilePath.mk ".." / path).pathExists do
      throwErrorAt stx "{path} does not exist in the repository"
    ``(Verso.Doc.Inline.code $(quote path))

/-- The argument of `inSource`: a file of the repository. -/
structure InSourceArgs where
  /-- The path from the repository's root. -/
  path : String

instance : FromArgs InSourceArgs DocElabM where
  fromArgs := InSourceArgs.mk <$> .positional `path .string

/-- A declaration of an optional package, checked against its source text (see the module
docstring). -/
@[role]
def inSource : RoleExpanderOf InSourceArgs
  | ⟨path⟩, args => do
    let (stx, nm) ← codeArg args
    if path.startsWith "/" || (path.splitOn "..").length > 1 then
      throwErrorAt stx "{path}: give a path inside the repository"
    let file := System.FilePath.mk ".." / path
    unless ← file.pathExists do throwErrorAt stx "{path} does not exist in the repository"
    let text ← IO.FS.readFile file
    let last := (nm.splitOn ".").getLast!
    let found := ["theorem ", "lemma ", "def "].any fun kw =>
      [last, nm].any fun n =>
        (text.splitOn (kw ++ n ++ " ")).length > 1 || (text.splitOn (kw ++ n ++ "\n")).length > 1
    unless found do throwErrorAt stx "{path} declares no {nm}"
    ``(Verso.Doc.Inline.code $(quote nm))

end PILeanManual
