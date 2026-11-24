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

`@[figure illustration]` registers the declaration the same way and marks it openly as an
illustration: a figure to which no theorem is linked.

`figure_links fig thm` links a theorem to a figure, after checking that it is proved from the
standard axioms and that its statement names the figure itself; it does not check what the
statement says. `figure_proves` is another name for the same command. `figures%` gives each
figure its standing (`Standing`): `linked` with the linked theorems that pass that check again
where `figures%` is elaborated, or `illustration`, marked or not.

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
  /-- Whether the declaration is marked as an illustration (`@[figure illustration]`). -/
  illustration : Bool := false
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
initialize pendingExt : EnvExtension (Array (Name × Bool)) ← registerEnvExtension (pure #[])

/-- Records `decl`, whose range is known: the module, file, the start of the declaration's range,
the hash of its source text, and whether it is marked as an illustration (`illustration`). -/
def recordFigure (decl : Name) (illustration : Bool) : Lean.Elab.Command.CommandElabM Unit := do
  let fm ← getFileMap
  match ← findDeclarationRanges? decl with
  | none => logError m!"@[figure]: no source position is known for {decl}"
  | some ranges =>
    let r := ranges.range
    let src := String.Pos.Raw.extract fm.source (fm.ofPosition r.pos) (fm.ofPosition r.endPos)
    modifyEnv fun env => figureExt.addEntry env
      { decl, module := env.mainModule, file := moduleFile env.mainModule,
        line := r.pos.line, column := r.pos.column,
        sourceHash := Sha256.hex (Sha256.hashString src), illustration }

/-- Records the queued declarations (after the command that declared them). -/
def completeFigures : Lean.Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  let pending := pendingExt.getState env
  if pending.isEmpty then return
  setEnv (pendingExt.setState env #[])
  for (decl, illustration) in pending do
    if (← getEnv).contains decl then recordFigure decl illustration

/-- Whether the attribute's syntax marks the figure as an illustration: `figure` alone is not
marked, `figure illustration` is, and any other argument is an error. -/
def illustrationArg (stx : Syntax) : AttrM Bool := do
  match stx[1].getOptional? with
  | none => return false
  | some a =>
    if a.isIdent && a.getId == `illustration then return true
    throwErrorAt a "@[figure] takes no argument other than `illustration`"

/-- Checks that the type of `decl` has a `ToOutputs` instance and queues the declaration, marked
as an illustration when `illustration`. -/
def queueFigure (decl : Name) (illustration : Bool := false) : AttrM Unit := do
  let env ← getEnv
  let some info := env.find? decl | throwError "unknown declaration {decl}"
  let ok ← (do
    let cls := mkApp (mkConst ``ToOutputs) info.type
    pure ((← synthInstance? cls).isSome) : MetaM Bool).run'
  if isPrivateName decl then throwError "@[figure] needs a declaration that is not private"
  unless ok do
    throwError "@[figure] needs a type with a ToOutputs instance, but {decl} has type {info.type}"
  modifyEnv fun env => pendingExt.modifyState env (·.push (decl, illustration))

/-- Registers a definition as a figure the build renders; `@[figure illustration]` also marks it
openly as an illustration. -/
initialize registerBuiltinAttribute {
  name := `figure
  descr := "registers a definition as a figure for pilean-build (`figure illustration`: marked \
    as an illustration, a figure to which no theorem is linked)"
  applicationTime := .afterCompilation
  add := fun decl stx _ => do queueFigure decl (← illustrationArg stx) }

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
    return some m!"{thm} is not a theorem; a figure is linked only to a theorem about it"
  let axioms ← collectAxioms thm
  if axioms.contains ``sorryAx then
    return some m!"{thm} depends on `sorry`; a figure is linked only to a proved theorem"
  for a in axioms do
    unless allowedAxioms.contains a do
      return some m!"{thm} depends on the axiom {a}; a figure is linked only to theorems \
        that use propext, Classical.choice and Quot.sound at most"
  unless ← statementNamesFigure fig thm do
    return some m!"the statement of {thm} does not mention the figure {fig}. A theorem linked \
      to a figure must be a statement about the figure itself: state it of {fig} or of its \
      fields (for instance, begin with an equation that says which series, edges or frames \
      {fig} holds), not only of definitions it is built from"
  return none

/-- The links recorded by `figure_links`: a figure and a theorem about it. -/
initialize figureTheoremExt : SimplePersistentEnvExtension (Name × Name) (Array (Name × Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s e => s.push e
    addImportedFn := fun es => es.foldl (· ++ ·) #[] }

/-- The theorems linked to the figure `fig` by `figure_links`, in the environment. -/
def figureTheorems (env : Environment) (fig : Name) : Array Name :=
  (figureTheoremExt.getState env).filterMap fun (f, t) => if f == fig then some t else none

/-- `figure_links fig thm` links the theorem `thm` to the figure `fig`, a declaration with the
attribute `@[figure]` (of this module or an imported one). The command fails, and with it the
build, unless `thm` is a theorem about the figure in the sense of `figureTheoremProblem?`: a
theorem, free of `sorry` and of axioms other than `propext`, `Classical.choice` and `Quot.sound`,
whose statement names the figure itself. What the statement says is not checked. -/
syntax (name := figureLinks) "figure_links " ident ppSpace ident : command

/-- `figure_proves fig thm` is the same command as `figure_links fig thm`. -/
syntax (name := figureProves) "figure_proves " ident ppSpace ident : command

/-- The elaborator of `figure_links` and `figure_proves`. -/
@[command_elab figureLinks, command_elab figureProves]
def elabFigureLinks : Lean.Elab.Command.CommandElab := fun stx => do
  let fig : Ident := ⟨stx[1]⟩
  let thm : Ident := ⟨stx[2]⟩
  let (figName, thmName) ← Lean.Elab.Command.liftCoreM do
    let figName ← realizeGlobalConstNoOverloadWithInfo fig
    unless (registeredFigures (← getEnv)).any (·.decl == figName) do
      throwErrorAt fig "{figName} does not have the attribute @[figure]"
    if (registeredFigures (← getEnv)).any (fun r => r.decl == figName && r.illustration) then
      throwErrorAt fig "{figName} is marked @[figure illustration]; a figure with a linked \
        theorem is not an illustration: remove the marking"
    let thmName ← realizeGlobalConstNoOverloadWithInfo thm
    if let some msg ← figureTheoremProblem? figName thmName then throwErrorAt thm msg
    return (figName, thmName)
  modifyEnv fun env => figureTheoremExt.addEntry env (figName, thmName)

/-- The module of the declaration `n` in the environment: the current module for a declaration
of the file being elaborated. -/
def declModule (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => env.mainModule

/-! ### A theorem that determines its figure -/

/-- The conjuncts of a statement: `a ∧ b` split into those of `a` and of `b`, anything else
itself. -/
partial def conjuncts (e : Expr) : List Expr :=
  match e.and? with
  | some (a, b) => conjuncts a ++ conjuncts b
  | none => [e]

/-- The pin a conjunct states, if it is one: `c = t`, or `∀ x₁ … xₙ, c x₁ … xₙ = t` with the
bound variables, in order, as the only arguments of the constant `c`. The result is `c` and the
value `t` as a function of `x₁ … xₙ` (`fun x₁ … xₙ => t`), provided that it mentions no free
variable, so no variable bound outside the conjunct. -/
def pinOf? (conj : Expr) : MetaM (Option (Name × Expr)) :=
  forallTelescope conj fun xs body => do
    let some (_, lhs, rhs) := body.eq? | return none
    let .const c _ := lhs.getAppFn | return none
    unless lhs.getAppArgs == xs do return none
    let v ← mkLambdaFVars xs rhs
    if v.hasFVar || v.hasMVar then return none
    return some (c, v)

/-- The pins a statement states (`pinOf?`): its leading universal quantifiers and hypotheses
opened, then each conjunct of what remains (`conjuncts`). A constant pinned twice keeps its
first pin. -/
def statementPins (type : Expr) : MetaM (Array (Name × Expr)) :=
  forallTelescope type fun _ body => do
    let mut out := #[]
    for c in conjuncts body do
      if let some p ← pinOf? c then
        unless out.any (·.1 == p.1) do out := out.push p
    return out

/-- Whether the constant `c` is one a pin must give the value of, when its module is local:
a definition, an opaque constant or an axiom whose type is not a proposition, and which is not a
matcher, an auxiliary recursor, a projection or a declaration with an internal name (such as an
auxiliary proof `_proof_1`). Inductive types, constructors and recursors are determined by their
declarations; a proof does not change a value. -/
def needsPin (c : Name) : MetaM Bool := do
  let env ← getEnv
  let some info := env.find? c | return false
  unless info matches .defnInfo _ || info matches .opaqueInfo _ || info matches .axiomInfo _ do
    return false
  if c.isInternalDetail || isAuxRecursor env c || env.isProjectionFn c then return false
  if (← isMatcher c) then return false
  return !(← isProp info.type)

/-- What prevents the statement of `thm` from determining the whole value of the figure `fig`,
if anything. The statement determines it when it pins the figure (`fig = t`, `pinOf?`) and pins
in turn every constant `t` mentions that is declared in a local module (`isLocal`) and is a value
(`needsPin`), and every such constant their values mention, and so on, with no pin that mentions
the constant it pins or leads back to it. The constants of the other modules are vocabulary, the
library whose definitions the statement relies on. Then, the statement being proved, the figure
is equal to a term built from vocabulary alone, which the statement writes out: a change to the
definitions of the local modules that changes the figure's value, in any of its fields, makes
the statement false, and the theorem fails to build. -/
def figurePinProblem? (isLocal : Name → Bool) (fig thm : Name) : MetaM (Option MessageData) := do
  let env ← getEnv
  let some info := env.find? thm | return some m!"unknown declaration {thm}"
  let pins ← statementPins (← ruleStatement info.type)
  let mut done : Array Name := #[]
  let mut todo : List (Name × List Name) := [(fig, [])]
  while true do
    let (c, path) :: rest := todo | break
    todo := rest
    if done.contains c then continue
    done := done.push c
    let some (_, v) := pins.find? (·.1 == c) |
      let via := if path.isEmpty then m!"" else m!" (used by {path})"
      return some m!"the statement of {thm} does not pin {c}{via}: it should state \
        `{c} = …` (or `∀ x, {c} x = …`) with a value that uses no other definition of these \
        modules unless that is pinned too"
    for d in v.getUsedConstants do
      if !isLocal (declModule env d) || !(← needsPin d) then continue
      if d == c || path.contains d then
        return some m!"the pin of {c} in {thm} mentions {d}, which is pinned through it"
      todo := todo ++ [(d, c :: path)]
  return none

/-- `#assert_figures_pinned A B … except M N …` fails unless, for every figure declared in a
module whose name starts with `A`, `B`, …, other than the modules `M`, `N`, …, every theorem
linked to it by `figure_links` determines its whole value (`figurePinProblem?`), the local modules
being those whose names start with `A`, `B`, …; and unless at least one such link is checked. It
walks the links of the environment, not a list of names. -/
syntax (name := assertFiguresPinned)
  "#assert_figures_pinned" (ppSpace ident)+ (" except" (ppSpace ident)+)? : command

/-- The elaborator of `#assert_figures_pinned`. -/
@[command_elab assertFiguresPinned]
def elabAssertFiguresPinned : Lean.Elab.Command.CommandElab := fun stx => do
  let roots := stx[1].getArgs.map (·.getId)
  let skip := if stx[2].getNumArgs == 0 then #[] else stx[2][1].getArgs.map (·.getId)
  let env ← getEnv
  let isLocal := fun (m : Name) => roots.any (·.isPrefixOf m)
  let mut checked := 0
  let mut bad : Array MessageData := #[]
  for (fig, thm) in figureTheoremExt.getState env do
    let m := declModule env fig
    if !isLocal m || skip.contains m then continue
    checked := checked + 1
    if let some msg ← Lean.Elab.Command.liftTermElabM (figurePinProblem? isLocal fig thm) then
      bad := bad.push m!"{fig}: {msg}"
  unless bad.isEmpty do
    throwError "linked theorems that do not determine their figure:\
      {indentD (MessageData.joinSep bad.toList "\n")}"
  if checked == 0 then throwError "no link from a figure of {roots} was checked"

/-! ### The axioms of a package -/

/-- The declarations of the environment whose module (`declModule`, the current module
included) satisfies `inScope`, paired with each axiom outside `allowedAxioms` that they declare
or depend on: an `axiom` is reported with itself, whether anything uses it or not; every other
declaration (a theorem, definition or opaque constant, an inductive type, a constructor, a
recursor, a quotient constant) with each axiom that `collectAxioms` finds it depends on. -/
def nonStandardAxioms (inScope : Name → Bool) : CoreM (Array (Name × Name)) := do
  let env ← getEnv
  let decls := env.constants.fold (init := #[]) fun acc c info =>
    if inScope (declModule env c) then acc.push (c, info) else acc
  let mut bad := #[]
  for (c, info) in decls do
    match info with
    | .axiomInfo _ =>
      unless allowedAxioms.contains c do bad := bad.push (c, c)
    | _ =>
      for a in ← collectAxioms c do
        unless allowedAxioms.contains a do bad := bad.push (c, a)
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

/-- The standing of a registered figure in the current environment: `linked` with the theorems
linked to it by `figure_links` (in the order of the links, each once) that pass
`figureTheoremProblem?` again now, or, if none does, an illustration, marked as the record says. -/
def figureStanding (r : FigureRecord) : CoreM Standing := do
  let mut ok : Array String := #[]
  for t in figureTheorems (← getEnv) r.decl do
    if (← figureTheoremProblem? r.decl t).isNone && !ok.contains t.toString then
      ok := ok.push t.toString
  return if ok.isEmpty then .illustration r.illustration else .linked ok

/-- The term that builds the standing `s`. -/
def quoteStanding (s : Standing) : TermElabM Term :=
  match s with
  | .linked ts => do
    let names := ts.map fun t => (quote t : Term)
    `(PILean.Trust.Standing.linked #[$names,*])
  | .illustration true => `(PILean.Trust.Standing.illustration true)
  | .illustration false => `(PILean.Trust.Standing.illustration false)

/-- `figures%` is the `Array PILean.Trust.FigureEntry` of every declaration with the attribute
`figure` in the imported modules and the current one so far, sorted by module and then name, the
outputs of each carrying its standing (`figureStanding`). -/
syntax (name := figuresTerm) "figures%" : term

/-- The elaborator of `figures%`. -/
@[term_elab figuresTerm]
def elabFigures : TermElab := fun _ expected? => do
  let env ← getEnv
  unless (pendingExt.getState env).isEmpty do
    throwError "figures%: the declaration {(pendingExt.getState env)[0]!} has no source position"
  let entries ← (sortedFigures env).mapM fun r => do
    let outputs := mkCIdent ``ToOutputs.outputs
    let standing ← quoteStanding (← figureStanding r)
    `(PILean.Trust.FigureEntry.mk
        (PILean.Trust.SourceData.mk $(quote r.module.toString) $(quote r.decl.toString)
          $(quote r.file) $(quote r.line) $(quote r.column) $(quote r.sourceHash))
        (fun _ => PILean.Trust.withStanding $standing ($outputs $(mkCIdent r.decl))))
  elabTerm (← `(show Array PILean.Trust.FigureEntry from #[$entries,*])) expected?

end PILean.Trust
