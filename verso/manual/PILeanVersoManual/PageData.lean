/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import Lean.Data.Json
import PILean.Trust.Fingerprint

/-!
# What a figure's page shows of its code

Every figure of a site has a page of its own (`PILeanVersoManual.Page`). What that page shows of
the Lean code is computed where the site's table of figures (`site_figures%`) is elaborated, from
the environment of the site's generator, and kept as data in the generator: the figure's
declaration, the theorems that tie it to its object with their statements and axioms, and the
declarations of the project that the figure's value and those statements use.

## Main definitions

* `CodeDecl`, `TheoremInfo`, `ExternalName`, `FigurePageData`: the data of one page
* `SiteFigures`: the table of figures with the page data, as `site_figures%` makes it
* `codeDepth`, `codeInlineCap`, `codeMoreCap`, `externalCap`, `codeLineCap`: the caps
-/

namespace PILeanVerso

open Lean PILean.Trust

/-- How far the code of a figure's page follows the declarations of the project from the figure's
value and its theorems' statements: the declarations they name (depth 1) and the declarations
those name (depth 2). -/
def codeDepth : Nat := 2

/-- The most declarations a figure's page shows in full besides the figure's own; the others the
search reaches are listed by name (`codeMoreCap`). -/
def codeInlineCap : Nat := 16

/-- The most declarations a figure's page lists by name beyond those it shows in full. -/
def codeMoreCap : Nat := 200

/-- The most declarations of other packages (Lean, Mathlib, PILean) a figure's page names. -/
def externalCap : Nat := 60

/-- The most lines of one declaration a figure's page shows; the rest is at its source link. -/
def codeLineCap : Nat := 200

/-- The most characters of a pretty-printed signature or statement a page keeps. -/
def signatureCap : Nat := 4000

/-- A declaration a figure's page shows. -/
structure CodeDecl where
  /-- Its full name. -/
  name : String
  /-- Its module. -/
  module : String
  /-- The module's file, relative to the package's source folder (`PILean.Trust.moduleFile`). -/
  file : String
  /-- The line where its declaration starts (from 1; 0 if unknown). -/
  line : Nat := 0
  /-- The column where it starts. -/
  column : Nat := 0
  /-- The line where it ends (0 if unknown). -/
  endLine : Nat := 0
  /-- Its kind: `def`, `theorem`, `instance`, `structure`, `inductive`, `opaque` or `axiom`. -/
  kind : String := "def"
  /-- Its signature as Lean prints it, at most `signatureCap` characters: shown when the
  module's highlighted source is not available. -/
  signature : String := ""
  /-- How far it is from the figure (0 for the figure, 1 for what the figure's value or a
  theorem's statement names, 2 beyond). -/
  depth : Nat := 0
  /-- The declaration through which the search reached it. -/
  via : String := ""
deriving ToJson, FromJson, Inhabited, Repr, BEq

/-- A theorem that ties a figure to its object. -/
structure TheoremInfo where
  /-- The theorem's declaration. -/
  decl : CodeDecl
  /-- Its statement as Lean prints it, at most `signatureCap` characters. -/
  statement : String
  /-- The axioms it rests on, by name, sorted. -/
  axioms : Array String
deriving ToJson, FromJson, Inhabited, Repr

/-- A declaration of another package that the figure or a theorem names: listed, not shown. -/
structure ExternalName where
  /-- Its full name. -/
  name : String
  /-- Its module. -/
  module : String
deriving ToJson, FromJson, Inhabited, Repr, BEq

/-- What a figure's page shows of the Lean code. -/
structure FigurePageData where
  /-- The figure's declaration. -/
  decl : String
  /-- The modules' first components that count as the project (the figure's module's). -/
  roots : Array String
  /-- The figure's own declaration. -/
  figure : CodeDecl
  /-- The theorems of the figure's standing, in its order. -/
  theorems : Array TheoremInfo := #[]
  /-- The declarations of the project shown in full, nearest first (at most `codeInlineCap`). -/
  related : Array CodeDecl := #[]
  /-- The declarations of the project the search reached beyond those (at most `codeMoreCap`). -/
  more : Array CodeDecl := #[]
  /-- How many more the search reached than `more` lists. -/
  moreOmitted : Nat := 0
  /-- Declarations of other packages named at depth 1 (at most `externalCap`). -/
  external : Array ExternalName := #[]
  /-- How many more there were than `external` lists. -/
  externalOmitted : Nat := 0
deriving ToJson, FromJson, Inhabited, Repr

/-- A site's table of figures: the entries `figures%` would make for the site's outputs, each with
its standing set, and what each figure's page shows of its code, as JSON text (an array of
`FigurePageData`). `site_figures%` makes it. -/
structure SiteFigures where
  /-- The entries, sorted by module and then name. -/
  entries : Array FigureEntry
  /-- The page data of the entries, as the JSON text of an array of `FigurePageData`. -/
  pagesJson : String := "[]"

/-- A table without page data: the pages of its figures show no code. -/
instance : Coe (Array FigureEntry) SiteFigures := ⟨fun es => { entries := es }⟩

/-- The page data of a table, by declaration name, or why it cannot be read. -/
def SiteFigures.pages (t : SiteFigures) : Except String (Std.HashMap String FigurePageData) := do
  let j ← Json.parse t.pagesJson
  let ps : Array FigurePageData ← fromJson? j
  return ps.foldl (init := {}) fun m p => m.insert p.decl p

end PILeanVerso
