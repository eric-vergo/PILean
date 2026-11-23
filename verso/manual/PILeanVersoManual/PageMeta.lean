/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Lean
import PILean.Trust.Attr
import PILeanVersoManual.PageData

/-!
# Collecting a figure's code from the environment

`figurePageData` computes, where `site_figures%` is elaborated, what a figure's page shows of the
Lean code (`FigurePageData`):

* the figure's declaration, and each theorem of its standing (`PILean.Trust.figureStanding`) with
  its statement as Lean prints it and the axioms it rests on (`Lean.collectAxioms`);
* the declarations *of the project* that the figure's value (and type) and the theorems'
  statements name, and those that these name in turn, to `codeDepth` levels, nearest first. A
  declaration is of the project when its module's first component is the figure module's (for
  `Example.Figures`, every module `Example.…`); a theorem is followed by its statement only,
  never by its proof. Constructors, recursors and projections count as their type; matchers,
  auxiliary recursors and other compiler-made names are left out. The first `codeInlineCap` are
  shown in full; the next `codeMoreCap` are listed by name, and how many more there were is said;
* the declarations of other packages (Lean, Mathlib, PILean, …) that the figure's value or a
  statement names directly, by name only (`externalCap`), leaving out instances and Lean's core
  library `Init` (`listedExternal`).
-/

namespace PILeanVerso

open Lean Meta PILean.Trust

/-- The module of a declaration, `none` for one of the module being elaborated. -/
def declModule? (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

/-- The declaration a constant is shown as: the type of a constructor, a recursor or a
projection, the constant itself otherwise; `none` for names made by the compiler or the
elaborator that are not shown (matchers, auxiliary recursors, `noConfusion`, internal names). -/
def shownAs? (env : Environment) (n : Name) : Option Name :=
  if n.isInternal || isMatcherCore env n || isAuxRecursor env n || isNoConfusion env n then none
  else match env.find? n with
    | some (.ctorInfo c) => some c.induct
    | some (.recInfo r) => some r.getMajorInduct
    | some _ =>
      match env.getProjectionFnInfo? n with
      | some p => some p.ctorName.getPrefix
      | none => some n
    | none => none

/-- The kind of a declaration as a page names it. -/
def declKind (env : Environment) (n : Name) : String :=
  match env.find? n with
  | some (.thmInfo _) => "theorem"
  | some (.defnInfo _) => if isInstanceCore env n then "instance" else "def"
  | some (.opaqueInfo _) => if isInstanceCore env n then "instance" else "opaque"
  | some (.axiomInfo _) => "axiom"
  | some (.inductInfo _) => if isStructure env n then "structure" else "inductive"
  | _ => "def"

/-- `s` cut to `signatureCap` characters. -/
def capText (s : String) : String :=
  if s.length ≤ signatureCap then s else (s.take signatureCap).toString ++ " …"

/-- A declaration's place and signature, at the distance `depth`, reached through `via`. -/
def codeDecl (n : Name) (depth : Nat) (via : String := "") : MetaM CodeDecl := do
  let env ← getEnv
  let mod := (declModule? env n).getD env.mainModule
  let ranges ← findDeclarationRanges? n
  let signature ← try pure (capText (toString (← PrettyPrinter.ppSignature n).fmt))
    catch _ => pure ""
  return {
    name := n.toString, module := mod.toString, file := moduleFile mod,
    line := (ranges.map (·.range.pos.line)).getD 0,
    column := (ranges.map (·.range.pos.column)).getD 0,
    endLine := (ranges.map (·.range.endPos.line)).getD 0,
    kind := declKind env n, signature, depth, via }

/-- The constants a declaration names, for the search: a definition's type and value, a
theorem's statement only, an inductive type's constructors' types, an opaque constant's type. -/
def namedConstants (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some (.defnInfo d) => d.type.getUsedConstants ++ d.value.getUsedConstants
  | some (.thmInfo t) => t.type.getUsedConstants
  | some (.inductInfo i) =>
    i.type.getUsedConstants ++ i.ctors.toArray.flatMap fun c =>
      ((env.find? c).map (·.type.getUsedConstants)).getD #[]
  | some ci => ci.type.getUsedConstants
  | none => #[]

/-- Whether a declaration belongs to the project whose modules start with one of `roots`. -/
def inProject (env : Environment) (roots : Array Name) (n : Name) : Bool :=
  match declModule? env n with
  | some m => roots.contains m.getRoot
  | none => false

/-- Whether a declaration of another package is listed on a page: not an instance (Lean inserts
those itself) and not of Lean's core library `Init` (equality, conjunction, numerals and the
like, which every statement uses). -/
def listedExternal (env : Environment) (n : Name) : Bool :=
  !isInstanceCore env n && match declModule? env n with
    | some m => m.getRoot != `Init
    | none => false

/-- What a figure's page shows of the Lean code, for the registered figure `r` whose standing is
`s` (see the module doc). -/
def figurePageData (r : FigureRecord) (s : Standing) : MetaM FigurePageData := do
  let env ← getEnv
  let roots := #[r.module.getRoot]
  let figure ← codeDecl r.decl 0
  let theorems ← s.theorems.mapM fun t => do
    let n := t.toName
    let statement ← try pure (capText (toString (← ppExpr (← getConstInfo n).type)))
      catch _ => pure ""
    let axioms := (← collectAxioms n).map (·.toString) |>.qsort (· < ·)
    return { decl := ← codeDecl n 0, statement, axioms : TheoremInfo }
  -- breadth first from the figure and the theorems' statements
  let start := (namedConstants env r.decl).map (·, r.decl) ++
    s.theorems.flatMap fun t => (namedConstants env t.toName).map (·, t.toName)
  let mut seen : Std.HashSet Name := (s.theorems.map (·.toName)).foldl (·.insert ·)
    (({} : Std.HashSet Name).insert r.decl)
  let mut found : Array (Name × Nat × Name) := #[]
  let mut external : Array ExternalName := #[]
  let mut externalAll := 0
  let mut frontier := start
  for depth in [1:codeDepth + 1] do
    let mut next : Array (Name × Name) := #[]
    for (c, via) in frontier do
      let some d := shownAs? env c | continue
      if seen.contains d then continue
      seen := seen.insert d
      if inProject env roots d then
        found := found.push (d, depth, via)
        next := next ++ (namedConstants env d).map (·, d)
      else if depth == 1 && listedExternal env d then
        externalAll := externalAll + 1
        if external.size < externalCap then
          external := external.push
            { name := d.toString, module := ((declModule? env d).getD .anonymous).toString }
    frontier := next
  let shown := found.extract 0 codeInlineCap
  let rest := found.extract codeInlineCap found.size
  let related ← shown.mapM fun (n, depth, via) => codeDecl n depth via.toString
  let more ← (rest.extract 0 codeMoreCap).mapM fun (n, depth, via) => do
    let mod := (declModule? env n).getD .anonymous
    let line := ((← findDeclarationRanges? n).map (·.range.pos.line)).getD 0
    return { name := n.toString, module := mod.toString, file := moduleFile mod, line,
             kind := declKind env n, depth, via := via.toString : CodeDecl }
  return { decl := r.decl.toString, roots := roots.map (·.toString), figure, theorems, related,
           more, moreOmitted := rest.size - more.size, external,
           externalOmitted := externalAll - external.size }

end PILeanVerso
