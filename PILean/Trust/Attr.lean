/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Lean
import PILean.Trust.Fingerprint

/-!
# The `@[figure]` attribute and `figures%`

`@[figure]` on a definition whose type has a `ToOutputs` instance records, in an environment
extension, the declaration's module, name, repository-relative file, line, column and the SHA-256
of its source text (taken from the file being elaborated). `figures%` is a term that, in the
module where it is used, becomes an `Array FigureEntry` of every registered declaration of the
environment (imported modules included), sorted by module and then declaration name.

`figure_proves fig thm` links a theorem to a figure, after checking that it is proved from the
standard axioms and that its statement names the figure itself.

`#assert_standard_axioms A` checks the axioms of every declaration of the modules whose names
start with `A`, by walking the modules rather than a list of names; `#assert_modules_imported A`
checks that every file below the folder `A` is among the modules such a check sees. A package
that builds on PILean can run both on its own modules.

This is the only part of `PILean` that imports `Lean`; the library proper does not.
-/

open Lean Elab Term Meta

namespace PILean.Trust

/-- What the attribute records about one declaration. -/
structure FigureRecord where
  /-- The declaration's name. -/
  decl : Name
  /-- The module it is declared in. -/
  module : Name
  /-- The file of the module, relative to the repository (`A/B.lean` for `A.B`). -/
  file : String
  /-- The line (from 1) and the column where the declaration starts. -/
  line : Nat
  /-- The column. -/
  column : Nat
  /-- The SHA-256 of the declaration's source text, in hexadecimal. -/
  sourceHash : String
deriving Inhabited

/-- The file of a module, relative to the repository root: its name with `/` for `.`, and
`.lean`. -/
def moduleFile (m : Name) : String :=
  "/".intercalate (m.components.map Name.toString) ++ ".lean"

/-- The registered declarations: the entries of this module and of every import. -/
initialize figureExt : SimplePersistentEnvExtension FigureRecord (Array FigureRecord) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s e => s.push e
    addImportedFn := fun es => es.foldl (· ++ ·) #[] }

/-- The records of every registered declaration in the environment. -/
def registeredFigures (env : Environment) : Array FigureRecord :=
  figureExt.getState env

/-- The declarations the attribute was applied to whose source positions are not yet known: Lean
records a declaration's range after the attributes are applied, so `figureCommand` completes the
records when the command is done. -/
initialize pendingExt : EnvExtension (Array Name) ← registerEnvExtension (pure #[])

/-- Records `decl`, whose range is known: the module, file, the start of the declaration's range,
and the hash of its source text. -/
def recordFigure (decl : Name) : Lean.Elab.Command.CommandElabM Unit := do
  let fm ← getFileMap
  match ← findDeclarationRanges? decl with
  | none => logError m!"@[figure]: no source position is known for {decl}"
  | some ranges =>
    let r := ranges.range
    let src := String.Pos.Raw.extract fm.source (fm.ofPosition r.pos) (fm.ofPosition r.endPos)
    modifyEnv fun env => figureExt.addEntry env
      { decl, module := env.mainModule, file := moduleFile env.mainModule,
        line := r.pos.line, column := r.pos.column,
        sourceHash := Sha256.hex (Sha256.hashString src) }

/-- Records the queued declarations (after the command that declared them). -/
def completeFigures : Lean.Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  let pending := pendingExt.getState env
  if pending.isEmpty then return
  setEnv (pendingExt.setState env #[])
  for decl in pending do
    if (← getEnv).contains decl then recordFigure decl

/-- Checks that the type of `decl` has a `ToOutputs` instance and queues the declaration. -/
def queueFigure (decl : Name) : AttrM Unit := do
  let env ← getEnv
  let some info := env.find? decl | throwError "unknown declaration {decl}"
  let ok ← (do
    let cls := mkApp (mkConst ``ToOutputs) info.type
    pure ((← synthInstance? cls).isSome) : MetaM Bool).run'
  if isPrivateName decl then throwError "@[figure] needs a declaration that is not private"
  unless ok do
    throwError "@[figure] needs a type with a ToOutputs instance, but {decl} has type {info.type}"
  modifyEnv fun env => pendingExt.modifyState env (·.push decl)

/-- Registers a definition as a figure the build renders. -/
initialize registerBuiltinAttribute {
  name := `figure
  descr := "registers a definition as a figure for pilean-build"
  applicationTime := .afterCompilation
  add := fun decl _ _ => queueFigure decl }

/-- The name of the (unregistered) option that is set while `withFigures` elaborates a command,
so that it does not wrap its own call. -/
def insideOption : Name := `pilean.figure.inside

/-- Whether the syntax has an attribute `figure`. -/
def mentionsFigure (stx : Syntax) : Bool :=
  (stx.find? fun s => s.isOfKind ``Lean.Parser.Attr.simple && s[0].getId == `figure).isSome

/-- Elaborates the command as usual and then records the figures queued by it, when Lean has
stored the range of its declarations. -/
def withFigures (stx : Syntax) : Lean.Elab.Command.CommandElabM Unit := do
  if (← getOptions).getBool insideOption || !mentionsFigure stx then throwUnsupportedSyntax
  Lean.Elab.Command.withScope (fun sc => { sc with opts := sc.opts.setBool insideOption true }) <|
    Lean.Elab.Command.elabCommand stx
  completeFigures

/-- A declaration with an attribute `figure`: elaborated as usual, then its figure is recorded;
any other declaration is passed on. -/
@[command_elab Lean.Parser.Command.declaration]
def figureDeclaration : Lean.Elab.Command.CommandElab := withFigures

/-- An `attribute [figure] decl` command, treated the same way. -/
@[command_elab Lean.Parser.Command.attribute]
def figureAttribute : Lean.Elab.Command.CommandElab := withFigures

/-! ### A theorem about a figure -/

/-- The axioms a theorem linked to a figure may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- One step of the reduction the rule applies to a statement, if `e` admits one: a `let` or
`have` is replaced by its body with the value put for the variable; `letFun v f` (the form
`have` took in earlier versions of Lean) becomes `f v`; an application of a `fun` to arguments is
beta-reduced. No constant is unfolded. -/
def ruleStep? (e : Expr) : Option Expr :=
  match e with
  | .letE _ _ v b _ => some (b.instantiate1 v)
  | _ =>
    if e.isAppOf ``letFun && e.getAppNumArgs ≥ 4 then
      let args := e.getAppArgs
      some (mkAppN (mkApp args[3]! args[2]!) (args.extract 4 args.size))
    else if e.isHeadBetaTarget then some e.headBeta
    else none

/-- The statement `type` as the rule reads it: every `let` and `have` replaced by its value and
every beta-redex reduced, everywhere in the term, until none is left (`ruleStep?`). A name that
occurs only in the value of a binding the statement does not use, or only as the argument of a
`fun` that discards it, is gone. Nothing is unfolded, and eta-reduction is not applied (it removes
a binder and a variable, never a constant, so it could not change which constants occur). The
statement of a declaration has no metavariables, so there are none to instantiate. -/
def ruleStatement (type : Expr) : CoreM Expr :=
  Core.transform type
    (pre := fun e => return match ruleStep? e with | some e' => .visit e' | none => .continue)
    (post := fun e => return match ruleStep? e with | some e' => .visit e' | none => .done e)

/-- Whether the statement of the declaration `thm` names the figure `fig`: the constant `fig`
occurs in the statement as it is elaborated, after its `let`s are replaced by their values and
its beta-redexes are reduced (`ruleStatement`). The fields of the figure are applications of
projections to `fig`, so a statement about `fig.panels`, `fig.edges` or `fig.frameSeq` names it.
Nothing is unfolded: a statement about a definition the figure is built from, or about a term
equal to the figure, does not name it. -/
def statementNamesFigure (fig thm : Name) : CoreM Bool := do
  let some info := (← getEnv).find? thm | return false
  return (← ruleStatement info.type).getUsedConstants.contains fig

/-- What prevents `thm` from being linked to the figure `fig` as a theorem about it, if anything:
`thm` must be a theorem, must not depend on `sorryAx` or on any axiom other than
`allowedAxioms`, and its statement must name the figure itself (`statementNamesFigure`): a
statement about a definition the figure is built from is refused, since the figure could change
and leave it true.

The rule is about names. It does not judge what the statement says: a statement that names the
figure and says nothing of substance about it (`fig = fig`, or the figure in a hypothesis that is
never used) passes. -/
def figureTheoremProblem? (fig thm : Name) : CoreM (Option MessageData) := do
  let env ← getEnv
  let some info := env.find? thm | return some m!"unknown declaration {thm}"
  unless info matches .thmInfo _ do
    return some m!"{thm} is not a theorem; a figure links only to a theorem about it"
  let axioms ← collectAxioms thm
  if axioms.contains ``sorryAx then
    return some m!"{thm} depends on `sorry`; a figure links only to a proved theorem"
  for a in axioms do
    unless allowedAxioms.contains a do
      return some m!"{thm} depends on the axiom {a}; a figure links only to theorems \
        that use propext, Classical.choice and Quot.sound at most"
  unless ← statementNamesFigure fig thm do
    return some m!"the statement of {thm} does not mention the figure {fig}. A theorem linked \
      to a figure must be a statement about the figure itself: state it of {fig} or of its \
      fields (for instance, begin with an equation that says which series, edges or frames \
      {fig} holds), not only of definitions it is built from"
  return none

/-- The links recorded by `figure_proves`: a figure and a theorem about it. -/
initialize figureTheoremExt : SimplePersistentEnvExtension (Name × Name) (Array (Name × Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s e => s.push e
    addImportedFn := fun es => es.foldl (· ++ ·) #[] }

/-- The theorems linked to the figure `fig` by `figure_proves`, in the environment. -/
def figureTheorems (env : Environment) (fig : Name) : Array Name :=
  (figureTheoremExt.getState env).filterMap fun (f, t) => if f == fig then some t else none

/-- `figure_proves fig thm` links the theorem `thm` to the figure `fig`, a declaration with the
attribute `@[figure]` (of this module or an imported one). The command fails, and with it the
build, unless `thm` is a theorem about the figure in the sense of `figureTheoremProblem?`: a
theorem, free of `sorry` and of axioms other than `propext`, `Classical.choice` and `Quot.sound`,
whose statement names the figure itself. -/
syntax (name := figureProves) "figure_proves " ident ppSpace ident : command

/-- The elaborator of `figure_proves`. -/
@[command_elab figureProves]
def elabFigureProves : Lean.Elab.Command.CommandElab := fun stx => do
  let fig : Ident := ⟨stx[1]⟩
  let thm : Ident := ⟨stx[2]⟩
  let (figName, thmName) ← Lean.Elab.Command.liftCoreM do
    let figName ← realizeGlobalConstNoOverloadWithInfo fig
    unless (registeredFigures (← getEnv)).any (·.decl == figName) do
      throwErrorAt fig "{figName} does not have the attribute @[figure]"
    let thmName ← realizeGlobalConstNoOverloadWithInfo thm
    if let some msg ← figureTheoremProblem? figName thmName then throwErrorAt thm msg
    return (figName, thmName)
  modifyEnv fun env => figureTheoremExt.addEntry env (figName, thmName)

/-! ### The axioms of a package -/

/-- The module of the declaration `n` in the environment: the current module for a declaration
of the file being elaborated. -/
def declModule (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => env.mainModule

/-- The declarations of the environment whose module (`declModule`, the current module
included) satisfies `inScope`, paired with each axiom outside `allowedAxioms` that they declare
or depend on: an `axiom` is reported with itself, whether anything uses it or not; a theorem,
definition or opaque constant with each axiom it depends on. -/
def nonStandardAxioms (inScope : Name → Bool) : CoreM (Array (Name × Name)) := do
  let env ← getEnv
  let decls := env.constants.fold (init := #[]) fun acc c info =>
    if inScope (declModule env c) then acc.push (c, info) else acc
  let mut bad := #[]
  for (c, info) in decls do
    match info with
    | .axiomInfo _ =>
      unless allowedAxioms.contains c do bad := bad.push (c, c)
    | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
      for a in ← collectAxioms c do
        unless allowedAxioms.contains a do bad := bad.push (c, a)
    | _ => pure ()
  return bad

/-- `#assert_standard_axioms A B …` fails unless no declaration of the imported modules (and of
this one) whose module names start with `A`, `B`, … is an axiom or depends on an axiom other than
those of `allowedAxioms`, and unless each prefix has at least one theorem. It walks the modules,
not a list of names, so a declaration added later is covered without anyone listing it, and an
`axiom` declared in one of them is reported whether anything uses it or not. -/
elab "#assert_standard_axioms " roots:(ppSpace ident)+ : command => do
  let env ← getEnv
  let roots := roots.map (·.getId)
  for r in roots do
    let found := env.constants.fold (init := false) fun acc c info =>
      acc || (info matches .thmInfo _ && r.isPrefixOf (declModule env c))
    unless found do
      throwError "no theorem found in the modules of {r}: nothing was checked"
  let bad ← Lean.Elab.Command.liftCoreM (nonStandardAxioms fun m => roots.any (·.isPrefixOf m))
  unless bad.isEmpty do
    let lines := bad.toList.map fun (c, a) =>
      if c == a then m!"the axiom {a} is declared" else m!"{c} depends on the axiom {a}"
    throwError "declarations with a non-standard axiom:{indentD (MessageData.joinSep lines "\n")}"

/-- The modules below the folder `dir`: one name for each `.lean` file, with `pre` as the first
component and the names of the folders and the file below `dir` after it. -/
partial def modulesBelow (dir : System.FilePath) (pre : Name) : IO (Array Name) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then
      out := out ++ (← modulesBelow e.path (pre.str e.fileName))
    else if e.fileName.endsWith ".lean" then
      out := out.push (pre.str (e.fileName.dropEnd 5).toString)
  return out

/-- The modules below the folder `dir` (named from `pre`, as in `modulesBelow`) that are not in
`known`. -/
def unknownModules (dir : System.FilePath) (pre : Name) (known : Array Name) :
    IO (Array Name) := do
  return (← modulesBelow dir pre).filter (!known.contains ·)

/-- The folder the module `m` is found from, given its source file `file`: `file` without its
last `n` components, where `n` is the number of components of `m` (`a/b/A/B.lean` for `A.B`
gives `a/b`, and a relative `A/B.lean` gives `.`). -/
def sourceRoot (file : System.FilePath) (m : Name) : System.FilePath :=
  m.components.foldl (init := file) fun p _ =>
    match p.parent with
    | some q => if q.toString.isEmpty then "." else q
    | none => "."

/-- `#assert_modules_imported A` fails unless every `.lean` file below the folder `A` is the
current module or a module it imports, directly or not, so that no module of the folder is
outside the checks that run in the current module, such as `#assert_standard_axioms A`. The
folder is found next to the current module's own source tree (`sourceRoot`), so the check does
not depend on the directory Lean runs in. -/
elab "#assert_modules_imported " root:ident : command => do
  let env ← getEnv
  let r := root.getId
  let dir := sourceRoot (← getFileName) env.mainModule / r.toString
  if (← modulesBelow dir r).isEmpty then throwError "no module found below the folder {dir}"
  let missing ← unknownModules dir r (env.header.moduleNames.push env.mainModule)
  unless missing.isEmpty do
    throwError "modules that are not imported, and so not checked: {missing}"

/-! ### `figures%` -/

/-- The records of the environment sorted by module and then declaration name, each once. -/
def sortedFigures (env : Environment) : Array FigureRecord :=
  let lt := fun (a b : FigureRecord) =>
    (Ordering.then (compare a.module.toString b.module.toString)
      (compare a.decl.toString b.decl.toString)) == .lt
  (registeredFigures env).qsort lt |>.foldl (init := #[]) fun out r =>
    match out.back? with
    | some p => if p.module == r.module && p.decl == r.decl then out else out.push r
    | none => out.push r

/-- `figures%` is the `Array PILean.Trust.FigureEntry` of every declaration with the attribute
`figure` in the imported modules and the current one so far, sorted by module and then name. -/
syntax (name := figuresTerm) "figures%" : term

/-- The elaborator of `figures%`. -/
@[term_elab figuresTerm]
def elabFigures : TermElab := fun _ expected? => do
  let env ← getEnv
  unless (pendingExt.getState env).isEmpty do
    throwError "figures%: the declaration {(pendingExt.getState env)[0]!} has no source position"
  let entries ← (sortedFigures env).mapM fun r => do
    let outputs := mkCIdent ``ToOutputs.outputs
    `(PILean.Trust.FigureEntry.mk
        (PILean.Trust.SourceData.mk $(quote r.module.toString) $(quote r.decl.toString)
          $(quote r.file) $(quote r.line) $(quote r.column) $(quote r.sourceHash))
        (fun _ => $outputs $(mkCIdent r.decl)))
  elabTerm (← `(show Array PILean.Trust.FigureEntry from #[$entries,*])) expected?

end PILean.Trust
