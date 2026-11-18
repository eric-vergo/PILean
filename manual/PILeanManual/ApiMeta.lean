/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import VersoManual
import PILeanManual.ApiScope
import PILeanManual.ApiAllow

/-!
# The API reference's markup

* `{apiModule PILean.Color}`: a module's page. Its module docstrings (rendered as Markdown, code
  elaborated as Lean where it can be), then Verso's docstring block of every public declaration
  of the module (`PILeanManual.publicDecls`), in source order. A public declaration with a part
  that has no docstring fails the build, unless the allow-list (`PILeanManual.apiAllowed?`)
  names it: then its block is shown with what it has, followed by the allow-list's reason.
* `{apiCoverage}`: the coverage of the whole reference, counted when the page is elaborated:
  the modules, the public declarations, how many are documented and how many are allowed.

Nothing on these pages is written by hand, so they cannot drift from the code: a renamed
declaration is renamed on its page, a changed signature is shown changed, and a new declaration
without a docstring stops the build.
-/

namespace PILeanManual

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre.Manual

/-- The argument of `apiModule`: the module. -/
structure ApiModuleArgs where
  /-- The module's name. -/
  name : Ident

instance : FromArgs ApiModuleArgs DocElabM where
  fromArgs := ApiModuleArgs.mk <$> .positional `name .ident "the module's name"

/-- A paragraph of emphasised text, for a note on a page. -/
def noteBlock (text : String) : DocElabM Term :=
  ``(Verso.Doc.Block.para #[Verso.Doc.Inline.emph #[Verso.Doc.Inline.text $(quote text)]])

/-- The module docstrings of `mod`, as blocks; the later ones only when they say more than a
section heading. -/
def moduleDocBlocks (ref : Syntax) (mod : Name) : DocElabM (Array Term) := do
  let some docs := getModuleDoc? (← getEnv) mod
    | throwErrorAt ref "{mod} has no module docstring"
  let mut out := #[]
  for (d, i) in docs.toList.zipIdx do
    let lines := (d.doc.splitOn "\n").filter (!·.trimAscii.isEmpty)
    if i > 0 && lines.length ≤ 1 then continue
    let some ast := MD4Lean.parse d.doc
      | throwErrorAt ref "the module docstring of {mod} is not valid Markdown"
    out := out ++ (← ast.blocks.mapM (blockFromMarkdownWithLean []))
  return out

/-- A module's page (see the module docstring). -/
@[block_command]
def apiModule : BlockCommandOf ApiModuleArgs
  | ⟨x⟩ => do
    let mod := x.getId
    unless coreModule mod do throwErrorAt x "{mod} is not a module of PILean's core"
    let mut out ← moduleDocBlocks x mod
    let decls ← publicDecls mod
    if decls.isEmpty then
      out := out.push (← noteBlock "This module has no public declarations of its own.")
    for n in decls do
      let missing ← undocumentedParts n
      if missing.isEmpty then
        out := out.push (← docstring { name := (mkIdentFrom x n, n), allowMissing := false })
      else
        let some reason := apiAllowed? (← getEnv) n
          | throwErrorAt x "{n} has parts without a docstring: {missing.toList}; document them \
              or put {n} on the allow-list (PILeanManual.ApiAllow) with a reason"
        let saved := (← getThe Core.State).messages
        let block ← docstring { name := (mkIdentFrom x n, n), allowMissing := true }
        modifyThe Core.State fun s => { s with messages := saved }
        out := out.push block
        out := out.push (← noteBlock s!"No docstring: {reason}")
    ``(Verso.Doc.Block.concat #[$out,*])

/-- The coverage of the reference, as a paragraph (see `coverageCounts`). -/
@[block_command]
def apiCoverage : BlockCommandOf Unit
  | () => do
    let (mods, total, documented, allowed, gaps) ← coverageCounts
    unless gaps.isEmpty do
      throwError "undocumented public declarations: {gaps.toList}"
    let text := s!"When this manual was built, the {mods} modules of the core had {total} public \
      declarations: {documented} with docstrings, {allowed} on the allow-list, none uncovered."
    ``(Verso.Doc.Block.para #[Verso.Doc.Inline.text $(quote text)])

end PILeanManual
