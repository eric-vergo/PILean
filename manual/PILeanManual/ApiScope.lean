/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Lean
import PILeanManual.ApiAllow

/-!
# What the API reference covers

The API reference has one page per module of PILean's core (the files below `PILean/` and
`PILean.lean`). A page lists the module's *public declarations*, read from the environment when
the page is elaborated, so a declaration added, renamed or removed in the library changes the
page without anyone editing it.

A declaration of a module is public when it was written in that module's source (it has a
declaration range), is not private, has no internal name component (one that starts with `_`, or
a number), and is not one of the parts that its type's block already shows: a structure's
projections and an inductive type's constructors (their docstrings are shown, and required,
inside the type's block), nor a declaration whose name is below an instance's name (where a
`deriving` clause puts what it defines), nor one whose name is below a function's, a value's or
a theorem's name (where `let rec` and `where` put their helpers). These are tests of the name's
shape: a declaration given such a name by hand is left out too. Instances count as declarations
like any other.

A public declaration is *covered* when it has a docstring or is on the allow-list
(`PILeanManual.ApiAllow`); the API pages fail the manual's build on any declaration that is
neither, and `lake test` prints the counts.

## Main definitions

* `coreModule`: whether a module name is one of the core's.
* `publicDecls`: a module's public declarations, in source order.
* `documentedParts`, `undocumentedParts`: what of a declaration needs a docstring, and what
  lacks one.
* `coverageCounts`: the counts over every core module in the environment.
-/

namespace PILeanManual

open Lean

/-- Whether `m` is a module of PILean's core: `PILean` itself or a module below it. -/
def coreModule (m : Name) : Bool := m == `PILean || (`PILean).isPrefixOf m

/-- Whether a name has a component that marks a generated or internal declaration: one that
starts with `_`, or a number. -/
def internalName (n : Name) : Bool :=
  n.components.any fun
    | .str _ s => s.startsWith "_"
    | .num _ _ => true
    | .anonymous => false

/-- Whether `n` is shown inside another declaration's block: a structure's projection or an
inductive type's constructor. -/
def shownInside (env : Environment) (n : Name) : Bool :=
  (env.getProjectionFnInfo? n).isSome ||
    match env.find? n with
    | some (.ctorInfo _) => true
    | some (.recInfo _) => true
    | _ => false

/-- Whether `n` is a helper defined inside another definition (a `let rec` or a `where` clause):
the declaration its name is below is a function or a value, not a type. -/
def helperOf (env : Environment) (n : Name) : Bool :=
  match env.find? n.getPrefix with
  | some (.defnInfo i) => !i.type.getForallBody.isSort
  | some (.thmInfo _) => true
  | _ => false

/-- The public declarations of module `mod` (see the module docstring), in source order (by
the line, then the column, of their declaration range). -/
def publicDecls (mod : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let some idx := env.getModuleIdx? mod | return #[]
  let mut out : Array (Nat × Nat × Name) := #[]
  for (n, _) in env.constants.map₁.toList do
    unless env.getModuleIdxFor? n == some idx do continue
    if isPrivateName n || internalName n || shownInside env n then continue
    if Meta.isInstanceCore env n.getPrefix || helperOf env n then continue
    if isAuxRecursor env n || isNoConfusion env n then continue
    let some r ← findDeclarationRanges? n | continue
    out := out.push (r.range.pos.line, r.range.pos.column, n)
  let sorted := out.qsort fun (l, c, a) (l', c', b) =>
    l < l' || (l == l' && (c < c' || (c == c' && a.toString < b.toString)))
  return sorted.map (·.2.2)

/-- The parts of `n` that need a docstring on its page: `n` itself, a structure's own fields and
an inductive type's constructors (as Verso's docstring block shows them). -/
def documentedParts (n : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let mut out := #[n]
  if isStructure env n then
    for f in getStructureFields env n do
      if (isSubobjectField? env n f).isSome then continue
      if let some p := getProjFnForField? env n f then
        unless isPrivateName p do out := out.push p
  else if let some (.inductInfo ii) := env.find? n then
    for c in ii.ctors do
      unless isPrivateName c do out := out.push c
  return out

/-- The parts of `n` (see `documentedParts`) that have no docstring. -/
def undocumentedParts (n : Name) : CoreM (Array Name) := do
  let env ← getEnv
  (← documentedParts n).filterM fun m => return (← findDocString? env m).isNone

/-- The coverage of the API reference over every core module in the environment: modules,
public declarations, documented, allowed, and the undocumented ones (an error). -/
def coverageCounts : CoreM (Nat × Nat × Nat × Nat × Array Name) := do
  let env ← getEnv
  let mods := env.header.moduleNames.filter coreModule
  let mut total := 0
  let mut documented := 0
  let mut allowed := 0
  let mut gaps := #[]
  for m in mods do
    for n in ← publicDecls m do
      total := total + 1
      if (← undocumentedParts n).isEmpty then documented := documented + 1
      else if (apiAllowed? env n).isSome then allowed := allowed + 1
      else gaps := gaps.push n
  return (mods.size, total, documented, allowed, gaps)

end PILeanManual
