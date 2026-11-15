/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanLeAnTeX.Outline

/-!
# LeAnTeX as a text engine

A `PILean.TextEngine` whose strings are LaTeX: a title, an axis label, a tick label or a legend
entry is typeset by LeAnTeX's text layer on one line at its natural width, with formulas in `$…$`
laid out by LeAnTeX's KaTeX-compatible math layout, and drawn as glyph outlines of New Computer
Modern (`PILeanLeAnTeX.outline`). PILean's SVG writer then writes the text as paths (the engine
is not `native`), so the picture needs no font and passes `PILean.Svg.isInert`; PNG output goes
through PILean's rasteriser.

* **Size.** A string at size `s` pixels is set in LaTeX's ten-point article setup and scaled so
  that its em is `s` pixels. A weight above 1.15 sets it in bold (`\bfseries`).
* **Deterministic.** The TeX-rule math layout is not used, because it reads metric files from a
  TeX installation where there is one: the picture is a function of the string, the LeAnTeX
  revision and the font files only. `engineId` names all three and is covered by the fingerprint.
* **Bounded.** Every string is typeset under `labelSettings`' caps (source length, tokens, macro
  expansions, nesting, line-breaking work); a string longer than `maxLabel` characters, or one
  LeAnTeX does not accept, is drawn literally by the built-in lettering instead, so a hostile
  label costs bounded work and still shows (cut to `maxLabel` characters).

## Main definitions

* `labelSettings`, `typesetLabel`, `Label`.
* `leantexRevision`, `engineId`.
* `engine`, `load`, `defaultFontDir`.
-/

namespace PILeanLeAnTeX

open PILean
open LeAnTeX LeAnTeX.Backend

/-- The LeAnTeX commit this package is built against: the revision `lakefile.lean` requires,
which the tests check against `lake-manifest.json`. -/
def leantexRevision : String := "45cae009ea2be14dc9c0fc850005dfcaebd70db4"

/-- The longest string, in characters, typeset by LeAnTeX; a longer one is drawn by the
lettering. -/
def maxLabel : Nat := 1000

/-- The caps on the work of typesetting one string: far above what a label needs, low enough that
a hostile one ends quickly. -/
def labelSettings : Text.Settings :=
  { maxSource := 4 * maxLabel, maxTokens := 20000, maxExpansions := 2000, maxDepth := 40,
    maxBreakWork := 200000, hyphenate := false,
    math := { maxExpand := 500, maxTokens := some 20000, maxSize := some 100 } }

/-- The em of the display lists, in sp (ten points). -/
def emSp : Int := 10 * 65536

/-- The longest line of a label, in sp: LaTeX's `\maxdimen`. -/
def maxdimen : Int := 1073741823

/-- A typeset label: its display list and its width in sp. -/
structure Label where
  /-- The display list, the first line's baseline origin at `(0, 0)`. -/
  list : DisplayList
  /-- The width: the widest line's indentation and natural width. -/
  width : Int

/-- The starting parameters of a label: no indentation, lines as long as TeX allows, so that a
label is one line at its natural width unless it breaks lines itself. -/
def labelVars : Text.Vars :=
  { parIndent := 0, p := { hsize := maxdimen } }

/-- A string typeset as a label (see the module docstring), or why not. -/
def typesetLabel (fonts : Fonts) (s : String) (bold : Bool) : Except String Label := do
  if s.length > maxLabel then throw s!"longer than {maxLabel} characters"
  let src := (if bold then "\\bfseries " else "") ++ s
  match Text.typeset src fonts.resolver labelSettings labelVars with
  | .error e => throw e.message
  | .ok d =>
    let w := d.lines.foldl (init := 0) fun m (l, _) => max m (l.indent + l.natural)
    return { list := d.toDisplayList, width := w }

/-- What the lettering draws for a string LeAnTeX does not set: the string, cut to `maxLabel`
characters and an ellipsis when it is longer. -/
def fallbackText (s : String) : String :=
  if s.length > maxLabel then (s.take maxLabel).toString ++ "…" else s

/-- Whether a weight sets a string in bold. -/
def isBold (weight : Float) : Bool := weight > 1.15

/-- The text engine of the fonts `fonts`, whose identity is `id` (`engineId`). -/
def engine (fonts : Fonts) (id : String) : TextEngine where
  measure s size :=
    match typesetLabel fonts s false with
    | .ok l => Float.ofInt l.width * size / Float.ofInt emSp
    | .error _ => TextEngine.lettering.measure (fallbackText s) size
  ascent := 0.75
  descent := 0.25
  shape s size weight :=
    match typesetLabel fonts s (isBold weight) with
    | .ok l => { fill := outline fonts.set l.list emSp (size / Float.ofInt emSp) }
    | .error _ => TextEngine.lettering.shape (fallbackText s) size weight
  id := id
  native := false

/-- The font files the engine reads: the text fonts and the math fonts of `Fonts.load`. -/
def fontFiles : List String :=
  Text.newComputerModernFiles.map (· ++ ".otf") ++ Backend.mathFiles

/-- The identity of the engine: the LeAnTeX revision and the SHA-256 of every font file, by
name, in a fixed order. -/
def engineId (fontBytes : List (String × ByteArray)) : String :=
  let fonts := fontBytes.map fun (n, b) => s!"{n} {Sha256.hex (Sha256.hash b)}"
  s!"LeAnTeX {leantexRevision}; New Computer Modern: " ++ ", ".intercalate fonts

/-- Where a project that requires this package finds New Computer Modern: LeAnTeX's copy in the
project's package folder, relative to the project's root. -/
def defaultFontDir : System.FilePath := ".lake" / "packages" / "leantex" / "fonts" /
  "newcomputermodern"

/-- The engine with the fonts of `dir`, or the files that are missing or do not read. -/
def load (dir : System.FilePath := defaultFontDir) : IO (Except String TextEngine) := do
  let (fonts, missing) ← Fonts.load dir
  if !missing.isEmpty then
    return .error s!"fonts in {dir}: {", ".intercalate missing.toList}"
  let mut bytes := #[]
  for n in fontFiles do
    bytes := bytes.push (n, ← IO.FS.readBinFile (dir / n))
  return .ok (engine fonts (engineId bytes.toList))

end PILeanLeAnTeX
