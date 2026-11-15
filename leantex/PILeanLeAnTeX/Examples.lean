/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILeanLeAnTeX.Engine

/-!
# Gallery figures with LaTeX labels

Figures whose titles, axis labels, legend entries and node labels are LaTeX, typeset by
LeAnTeX through `PILeanLeAnTeX.engine`. They are functions of the engine, which is read from
font files at run time; `lake exe pilean-leantex-gallery` writes them to `examples/` and `lake
test` compares them with those files.
-/

namespace PILeanLeAnTeX.Examples

open PILean PILean.Plot

/-- The constant π. -/
def pi : Float := 3.141592653589793

/-- The normal density with mean `μ` and standard deviation `σ`. -/
def normalDensity (μ σ x : Float) : Float :=
  (-(x - μ) ^ 2 / (2 * σ ^ 2)).exp / (σ * (2 * pi).sqrt)

/-- Three normal densities, the formula in the title. -/
def densities : Figure where
  title := "Normal densities $\\varphi_{\\mu,\\sigma}(x) = \\frac{1}{\\sigma\\sqrt{2\\pi}}\\,\
    e^{-(x-\\mu)^2/2\\sigma^2}$"
  panels := #[{
      x := { label := "$x$", domain := some (-4, 4) },
      y := { label := "$\\varphi_{\\mu,\\sigma}(x)$", domain := some (0, 0.85) },
      series := #[.function "$\\mu = 0$, $\\sigma = 1$" (normalDensity 0 1) (-4) 4,
        .function "$\\mu = 1$, $\\sigma = \\frac12$" (normalDensity 1 0.5) (-4) 4,
        .function "$\\mu = -1$, $\\sigma = 2$" (normalDensity (-1) 2) (-4) 4 (dash := #[5, 4])] }]

/-- The partial sums of `∑ 1/k²` approaching `π²/6`. -/
def basel : Figure where
  title := "The Basel problem: $\\sum_{k=1}^{\\infty} k^{-2} = \\pi^2/6$"
  panels := #[{
      x := { label := "$n$" }, y := { label := "partial sum $S_n$" },
      series := #[.step "$S_n = \\sum_{k=1}^{n} \\frac{1}{k^2}$"
        ((List.range 30).toArray.map fun i =>
          ⟨(i + 1).toFloat, ((List.range (i + 1)).foldl
            (fun s k => s + 1 / ((k + 1).toFloat ^ 2)) 0)⟩),
        .function "$\\pi^2/6 \\approx 1.645$" (fun _ => pi ^ 2 / 6) 1 30 (dash := #[5, 4])] }]

/-- The subgroups of `ℤ/12ℤ` ordered by inclusion, each named by a generator. -/
def subgroups : Graph :=
  let ds := [1, 2, 3, 4, 6, 12]
  Graph.ofRelation ds (fun a b => b != a && b % a == 0 && ds.all fun c =>
      !(c != a && c != b && c % a == 0 && b % c == 0))
    fun d => if d == 12 then "$\\{0\\}$" else s!"$\\langle {d} \\rangle$"

/-- The figures with a style, each light and dark: file stem and figure. -/
def figures (e : TextEngine) : Array (String × Figure) :=
  let named := #[("leantex-densities", densities), ("leantex-basel", basel)]
  named.flatMap fun (n, f) =>
    #[(n, { f with style := { Style.light with text := e } }),
      (n ++ "-dark", { f with style := { Style.dark with text := e } })]

/-- The graphs with a style: file stem, graph and style. -/
def graphs (e : TextEngine) : Array (String × Graph × Style) :=
  #[("leantex-subgroups", subgroups, { Style.light with text := e }),
    ("leantex-subgroups-dark", subgroups, { Style.dark with text := e })]

/-- Every file of the gallery: name and bytes, in a fixed order. -/
def files (e : TextEngine) : Array (String × Except String ByteArray) := Id.run do
  let mut out := #[]
  for (n, f) in figures e do
    out := out.push (n ++ ".svg", .ok f.toSvg.toUTF8)
    out := out.push (n ++ ".png", match f.toPng with
      | some b => .ok b
      | none => .error "no pixels")
  for (n, g, st) in graphs e do
    out := out.push (n ++ ".svg", .ok (g.toSvg {} st).toUTF8)
    out := out.push (n ++ ".png", (g.toPng {} st).mapError toString)
  return out

end PILeanLeAnTeX.Examples
