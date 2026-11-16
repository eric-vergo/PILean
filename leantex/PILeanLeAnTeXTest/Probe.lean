/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanLeAnTeX

/-!
# `pilean-leantex-probe`

`pilean-leantex-probe KIND` draws a figure whose title is the hostile label `hostile KIND` with
the LeAnTeX engine, as SVG and as PNG, and prints `ok` with the sizes and whether LeAnTeX set the
label (`set`) or the lettering drew it (`lettering`). The test driver runs it under CPU and
memory bounds (`PILeanLeAnTeXTest.Main`); it imports only the library, so what it costs is what
the engine costs.
-/

open PILean PILean.Plot PILeanLeAnTeX

/-- `s` repeated `n` times. -/
def rep (s : String) (n : Nat) : String := String.join (List.replicate n s)

/-- A hostile label of a kind. -/
def hostile : String → String
  | "recursive-macro" => "\\def\\a{\\a\\a}\\a"
  | "newcommand-bomb" =>
      "\\newcommand\\a{xxxxxxxxxx}\\newcommand\\b{\\a\\a\\a\\a\\a\\a\\a\\a\\a\\a}" ++
      "\\newcommand\\c{\\b\\b\\b\\b\\b\\b\\b\\b\\b\\b}" ++
      "\\newcommand\\d{\\c\\c\\c\\c\\c\\c\\c\\c\\c\\c}" ++
      "\\d\\d\\d\\d\\d\\d\\d\\d\\d\\d"
  | "math-macro" => "$\\def\\a{\\a\\a}\\a$"
  | "deep-groups" => rep "{" 900 ++ "x" ++ rep "}" 900
  | "deep-scripts" => "$" ++ rep "x^{" 300 ++ "x" ++ rep "}" 300 ++ "$"
  | "deep-fractions" => "$" ++ rep "\\frac{1}{" 200 ++ "x" ++ rep "}" 200 ++ "$"
  | "long" => rep "M" 999
  | "too-long" => rep "MW " 400000
  | "huge-rule" => "\\rule{16000pt}{16000pt}"
  | "huge-math-size" => "$\\rule{1000em}{1000em}\\kern1000em x$"
  | "unbalanced" => "$\\frac{1}{"
  | "controls" => String.ofList ((List.range 32).map Char.ofNat) ++ "\u202Ex\uFEFF"
  | "markup" => "<script>alert(1)</script> & \"x\" ' ]]> <!-- -->"
  | "many-formulas" => rep "$x_i^2$ " 120
  | _ => "x"

/-- Draws the figure and prints its sizes. -/
def main (args : List String) : IO UInt32 := do
  let [kind] := args | IO.eprintln "usage: pilean-leantex-probe KIND"; return 2
  let .ok e ← PILeanLeAnTeX.load | IO.eprintln "fonts missing"; return 2
  let (fonts, _) ← LeAnTeX.Backend.Fonts.load defaultFontDir
  let label := hostile kind
  let set := (typesetLabel fonts label false).isOk
  let st : Style := { Style.light with text := e }
  let panel : Panel := { series := #[.function "$y$" (fun x => x) 0 1] }
  let fig : Figure := { title := label, style := st, panels := #[panel] }
  let svg := fig.toSvg
  let png := (fig.toPng.map (·.size)).getD 0
  let how := if set then "set" else "lettering"
  IO.println s!"ok svg {svg.utf8ByteSize} png {png} {how} inert {Svg.isInert svg}"
  return 0
