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
* ```` ```fileText "path" ``` ```` (an empty code block): the text of a file of the repository,
  by its path from the repository's root, from its first `import` line on (the licence header
  is left out), shown as a code block. The file must exist when the manual is built, so the page
  shows what the file holds. The manual's `lake test` runs the one file Getting Started shows
  this way, `manual/FirstProgram/Main.lean`; other files shown with it are not elaborated.
* `{toolchain}[]`: the toolchain named in the repository's `lean-toolchain`, read when the
  manual is built, as code.
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

/-- A path from the repository's root, read when the manual is built: it must be relative, not
climb with `..`, and name a file that exists. -/
def repoFile (stx : Syntax) (path : String) : DocElabM System.FilePath := do
  if path.startsWith "/" || (path.splitOn "..").length > 1 then
    throwErrorAt stx "{path}: give a path inside the repository"
  let file := System.FilePath.mk ".." / path
  unless ← file.pathExists do throwErrorAt stx "{path} does not exist in the repository"
  return file

/-- The argument of `fileText`: a file of the repository. -/
structure FileTextArgs where
  /-- The path from the repository's root. -/
  path : String

instance : FromArgs FileTextArgs DocElabM where
  fromArgs := FileTextArgs.mk <$> .positional `path .string

/-- The text of a file from its first `import` line on. -/
def fromFirstImport (text : String) : String :=
  let lines := text.splitOn "\n"
  "\n".intercalate (lines.dropWhile (!·.startsWith "import "))

/-- Shows a file of the repository from its first `import` line on (see the module docstring);
the block's own text must be empty. -/
@[code_block]
def fileText : CodeBlockExpanderOf FileTextArgs
  | ⟨path⟩, str => do
    unless str.getString.trimAscii.isEmpty do
      throwErrorAt str "fileText shows a file of the repository: leave the block empty"
    let text := fromFirstImport (← IO.FS.readFile (← repoFile str path))
    if text.trimAscii.isEmpty then throwErrorAt str "{path} has no import line"
    ``(Verso.Doc.Block.code $(quote text))

/-- The toolchain named in the repository's `lean-toolchain` (see the module docstring); the
role takes no text. -/
@[role]
def toolchain : RoleExpanderOf Unit
  | (), args => do
    unless args.isEmpty do throwError "toolchain reads lean-toolchain: give it no text"
    let name := (← IO.FS.readFile (← repoFile .missing "lean-toolchain")).trimAscii.toString
    ``(Verso.Doc.Inline.code $(quote name))

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
