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

/-- The statement `type` with every `let` (and `have`) replaced by its value, so that a name
that occurs only in the value of a binding the statement does not use is gone. -/
def unfoldLets (type : Expr) : CoreM Expr :=
  Core.transform type (pre := fun e =>
    match e with
    | .letE _ _ v b _ => return .visit (b.instantiate1 v)
    | _ => return .continue)

/-- Whether the statement of the declaration `thm` names the figure `fig`: the constant `fig`
occurs in the statement as it is elaborated, after its `let`s are replaced by their values
(`unfoldLets`). The fields of the figure are applications of projections to `fig`, so a statement
about `fig.panels`, `fig.edges` or `fig.frameSeq` names it. Nothing is unfolded: a statement
about a definition the figure is built from, or about a term equal to the figure, does not name
it. -/
def statementNamesFigure (fig thm : Name) : CoreM Bool := do
  let some info := (← getEnv).find? thm | return false
  return (← unfoldLets info.type).getUsedConstants.contains fig

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
