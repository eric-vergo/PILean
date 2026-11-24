/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Trust.Attr

/-!
# Two proved explorers

Families of figures over a grid of two parameters (`Explorer.family₂`), each with a theorem
quantified over the grid that `figure_links` links to the explorer:

* `cayleyExplorer`: the Cayley graph of `ℤ/n` for one generator `a`, for `n = 5, …, 12` and
  `a = 1, …, 4` (32 frames, `a` played). `cayleyExplorer_spec`: every frame is the figure of its
  point of the grid, and the figure of `(n, a)` draws its diagram faithfully, with exactly the
  arrows `g → g + a mod n` for `g < n` (one line for each pair `{g, g + a}` when `2a ≡ 0 mod n`).
* `latticeExplorer`: the lattice `ℤ (1, 0) + ℤ ω₂` in the window `[-3, 3] × [-2, 2]` as its
  second period `ω₂ = (x, y)` moves over `x = 0, 1/4, 1/2, 3/4` and `y = 1/2, 3/4, 1` (12
  frames, `y` played). `latticeExplorer_spec`: every frame is the figure of its point of the grid,
  which draws its lattice (of that window) faithfully (the dots are exactly the points
  `m ω₁ + n ω₂` of the window
  among the candidates the bound allows, the fundamental parallelogram `0, ω₁, ω₁ + ω₂, ω₂`).
  That the candidates hold every lattice point of the window is proved in `pilean-mathlib`
  (`PILeanMathlib.Examples.latticeExplorer_span`), with Mathlib's `Submodule.span ℤ`; so is the
  Cayley graph's statement in `ZMod n` (`cayleyExplorer_zmod`).

`lake test` changes copies of this module (a value of the grid, a generator, a window, the title)
and requires each change to break its theorem (`PILeanTest.SpecMutations`).
-/

namespace PILeanTest.Explorers

open PILean PILean.Diagram

/-! ### Cayley graphs of `ℤ/n` -/

/-- Addition modulo `n` on `0, …, n - 1`, the elements named by their numbers. -/
def zmod (n : Nat) : FinMagma := { n, mul := fun a b => a + b }

/-- The generator `a mod n` as an element of `Fin n` (none for `n = 0`). -/
def generator (n a : Nat) : List (Fin n) := if h : 0 < n then [⟨a % n, Nat.mod_lt _ h⟩] else []

/-- The Cayley graph of `ℤ/n` for the generator `a`, the elements on a circle. -/
def cayleyData (n a : Nat) : CommDiagram :=
  (zmod n).cayley (generator n a) (FinMagma.circlePositions n)

/-- The figure of `(n, a)`: the Cayley graph, titled. -/
def cayleyDiagram (n a : Nat) : Diagram :=
  { (zmod n).cayleyFigure (generator n a) (FinMagma.circlePositions n) with
    title := s!"The Cayley graph of ℤ/{n} for the generator {a}", width := 300 }

/-- The moduli `n = 5, …, 12`. -/
def moduli : ExplorerParam Nat :=
  { name := "n", values := #[5, 6, 7, 8, 9, 10, 11, 12], label := toString }

/-- The generators `a = 1, …, 4`. -/
def generators : ExplorerParam Nat := { name := "a", values := #[1, 2, 3, 4], label := toString }

/-- The pairs `(g, g + a mod n)` for `g < n`; when `2a ≡ 0 mod n` (the generator is an involution)
only the pairs with `g < g + a mod n`, each pair once. -/
def cayleyPairs (n a : Nat) : List (Nat × Nat) :=
  (List.range n).filterMap fun g =>
    let t := (g + a) % n
    if (2 * a) % n == 0 && !(g < t) then none else some (g, t)

/-- The frame of `(n, a)`. -/
def cayleyFrame (n a : Nat) : ExplorerFrame := ExplorerFrame.ofPlane (cayleyDiagram n a).toPlane

/-- The Cayley graphs of `ℤ/n` for one generator, `n` on the slider and `a` played. -/
@[figure]
def cayleyExplorer : Explorer := Explorer.family₂ moduli generators cayleyFrame

/-- **The Cayley graphs, frame by frame.** The explorer is the family of the frames of
`cayleyDiagram n a` over the grid `n = 5, …, 12`, `a = 1, …, 4` (the parameters named `n` and
`a`), each value written as its number, the frame of `(n, a)` the plane figure of `cayleyDiagram n a`; at every point of the grid the
diagram draws the Cayley graph faithfully (`CommDiagram.Faithful`: arrows, labels, objects, every
mark), its title names `ℤ/n` and `a`, its elements are named by their numbers, and the drawn arrows join exactly the pairs
`(g, g + a mod n)` for `g < n` (each pair once for an involution).
The statement begins with the figure written out, with the definitions it is built from, so that it
determines the whole figure (`PILean.Trust.figurePinProblem?`). -/
theorem cayleyExplorer_spec :
    moduli = ({
      name := "n", values := #[5, 6, 7, 8, 9, 10, 11, 12],
      label := toString } : ExplorerParam Nat) ∧
    generators = ({ name := "a", values := #[1, 2, 3, 4], label := toString } : ExplorerParam Nat) ∧
    (∀ (n a : Nat), cayleyDiagram n a = (
      { (zmod n).cayleyFigure (generator n a) (FinMagma.circlePositions n) with
        title := s!"The Cayley graph of ℤ/{n} for the generator {a}", width := 300 } : Diagram)) ∧
    (∀ (n : Nat), zmod n = ({ n, mul := fun a b => a + b } : FinMagma)) ∧
    (∀ (n a : Nat), generator n a =
      (if h : 0 < n then [⟨a % n, Nat.mod_lt _ h⟩] else [] : List (Fin n))) ∧
    (cayleyExplorer = Explorer.family₂ moduli generators cayleyFrame ∧
    moduli.values = #[5, 6, 7, 8, 9, 10, 11, 12] ∧ generators.values = #[1, 2, 3, 4] ∧
    moduli.name = "n" ∧ generators.name = "a" ∧
    moduli.label = toString ∧ generators.label = toString ∧
    (∀ n a, cayleyFrame n a = ExplorerFrame.ofPlane (cayleyDiagram n a).toPlane) ∧
    ∀ n ∈ moduli.values, ∀ a ∈ generators.values,
      (cayleyData n a).Faithful (cayleyData n a).layout (cayleyDiagram n a) ∧
      (cayleyDiagram n a).title = s!"The Cayley graph of ℤ/{n} for the generator {a}" ∧
      (cayleyData n a).objects.toList = (List.range n).map toString ∧
      (cayleyDiagram n a).arrows.map (fun x => (x.2.1, x.2.2)) = cayleyPairs n a) := by
  refine ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, ?_⟩
  -- the caps and the arrows at every point of the grid, checked by the kernel
  have caps : ∀ n ∈ moduli.values, ∀ a ∈ generators.values,
      ((cayleyData n a).objects.size ≤ CommDiagram.maxObjects &&
        (cayleyData n a).arrows.length ≤ CommDiagram.maxArrows &&
        (cayleyData n a).twoCells.length ≤ CommDiagram.maxTwoCells && (cayleyData n a).Valid) =
        true ∧ ((zmod n).n ≤ FinMagma.maxElements && (generator n a).length ≤ 8) = true := by
    decide +kernel
  have pairs : ∀ n ∈ moduli.values, ∀ a ∈ generators.values,
      (cayleyData n a).arrowTriples.map (fun x => (x.2.1, x.2.2)) = cayleyPairs n a := by
    decide +kernel
  have names : ∀ n ∈ moduli.values, ∀ a ∈ generators.values,
      (cayleyData n a).objects.toList = (List.range n).map toString := by
    decide +kernel
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
  intro n hn a ha
  obtain ⟨cap, capF⟩ := caps n hn a ha
  have e : (cayleyDiagram n a).marks = (cayleyData n a).figure.marks := by
    simp only [cayleyDiagram, FinMagma.cayleyFigure]
    rw [Diagram.capped_of]
    · rfl
    · exact capF
  have h := CommDiagram.builder_faithful (cayleyData n a) cap
  have hf : (cayleyData n a).Faithful (cayleyData n a).layout (cayleyDiagram n a) := by
    unfold CommDiagram.Faithful Diagram.arrows Diagram.arrowTexts Diagram.marksWhere at h ⊢
    rw [e]; exact h
  refine ⟨hf, rfl, names n hn a ha, ?_⟩
  rw [hf.1]
  exact pairs n hn a ha

figure_links cayleyExplorer cayleyExplorer_spec

/-! ### A lattice whose second period moves -/

/-- The lattice of the periods `(1, 0)` and `(x, y)` in the window `[-3, 3] × [-2, 2]`. -/
def lattice (x y : Rat) : PlaneLattice :=
  { w1 := (1, 0), w2 := (x, y), lo := (-3, -2), hi := (3, 2) }

/-- The figure of `(x, y)`: the lattice, titled. -/
def latticeDiagram (x y : Rat) : Diagram :=
  { (lattice x y).figure with title := s!"The lattice ℤ(1, 0) + ℤ({x}, {y})" }

/-- The first coordinates of the second period. -/
def periodX : ExplorerParam Rat :=
  { name := "x", values := #[0, 1 / 4, 1 / 2, 3 / 4], label := toString }

/-- The second coordinates of the second period. -/
def periodY : ExplorerParam Rat :=
  { name := "y", values := #[1 / 2, 3 / 4, 1], label := toString }

/-- The frame of `(x, y)`. -/
def latticeFrame (x y : Rat) : ExplorerFrame := ExplorerFrame.ofPlane (latticeDiagram x y).toPlane

/-- The lattice `ℤ (1, 0) + ℤ (x, y)`, `x` on the slider and `y` played. -/
@[figure]
def latticeExplorer : Explorer := Explorer.family₂ periodX periodY latticeFrame

/-- **The lattices, frame by frame.** The explorer is the family of the frames of
`latticeDiagram x y` over the grid `x = 0, 1/4, 1/2, 3/4`, `y = 1/2, 3/4, 1` (the parameters
named `x` and `y`), each value written as its number, the frame of `(x, y)` the plane figure of `latticeDiagram x y`; at every point of
the grid the periods are independent, the diagram draws the lattice faithfully
(`PlaneLattice.Faithful`: the dots are the points `m ω₁ + n ω₂` of the window among the
candidates, in order, the parallelogram and the axes the builder's, nothing else) and its title
names the second period.
The statement begins with the figure written out, with the definitions it is built from, so that it
determines the whole figure (`PILean.Trust.figurePinProblem?`). -/
theorem latticeExplorer_spec :
    periodX = ({
      name := "x", values := #[0, 1 / 4, 1 / 2, 3 / 4], label := toString } : ExplorerParam Rat) ∧
    periodY = ({
      name := "y", values := #[1 / 2, 3 / 4, 1], label := toString } : ExplorerParam Rat) ∧
    (∀ (x y : Rat), latticeDiagram x y = ({ (lattice x y).figure with
      title := s!"The lattice ℤ(1, 0) + ℤ({x}, {y})" } : Diagram)) ∧
    (∀ (x y : Rat), lattice x y = ({
      w1 := (1, 0), w2 := (x, y), lo := (-3, -2), hi := (3, 2) } : PlaneLattice)) ∧
    (latticeExplorer = Explorer.family₂ periodX periodY latticeFrame ∧
    periodX.values = #[0, 1 / 4, 1 / 2, 3 / 4] ∧ periodY.values = #[1 / 2, 3 / 4, 1] ∧
    periodX.name = "x" ∧ periodY.name = "y" ∧
    periodX.label = toString ∧ periodY.label = toString ∧
    (∀ x y, latticeFrame x y = ExplorerFrame.ofPlane (latticeDiagram x y).toPlane) ∧
    ∀ x ∈ periodX.values, ∀ y ∈ periodY.values,
      lattice x y = { w1 := (1, 0), w2 := (x, y), lo := (-3, -2), hi := (3, 2) } ∧
      (lattice x y).det ≠ 0 ∧ (lattice x y).Faithful (latticeDiagram x y) ∧
      (latticeDiagram x y).title = s!"The lattice ℤ(1, 0) + ℤ({x}, {y})") := by
  refine ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  -- the periods are independent and the candidates within the cap at every point of the grid,
  -- checked by the kernel
  have caps : ∀ x ∈ periodX.values, ∀ y ∈ periodY.values,
      ((lattice x y).det ≠ 0 && (2 * (lattice x y).bound + 1) * (2 * (lattice x y).bound + 1) ≤
        PlaneLattice.maxCandidates) = true := by
    decide +kernel
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
  intro x hx y hy
  have cap := caps x hx y hy
  have h := (lattice x y).builder_faithful cap
  refine ⟨rfl, by simp only [Bool.and_eq_true, decide_eq_true_eq] at cap; exact cap.1, ?_, rfl⟩
  unfold PlaneLattice.Faithful Diagram.dots Diagram.marksWhere at h ⊢
  exact h

figure_links latticeExplorer latticeExplorer_spec

/-- The explorers of this module by name. -/
def explorers : Array (String × Explorer) :=
  #[("explorer-cayley", cayleyExplorer), ("explorer-lattice", latticeExplorer)]

/-- The checks of the explorers as a build renders them: each is well formed and within the caps,
with the frames' count its grid's, every output renders (the poster's SVG, PNG and PDF, the SVG of
every frame), every frame's SVG is inert and is the inline picture of the poster's frame set, the
frames have no layout problem, the page sees the second parameter's name, and the poster's PDF
passes the structural check. -/
def checks : Array (String × Bool) :=
  explorers.flatMap fun (name, x) =>
    let os := Trust.ToOutputs.outputs x
    let fs := (os[0]?.bind fun o => o.frames ()).getD default
    #[(s!"{name}: well formed, within the caps", x.valid && x.svgBytes ≤ Explorer.maxBytes),
      (s!"{name}: every output renders", os.all fun o => (o.bytes ()).isOk),
      (s!"{name}: the outputs are the poster's SVG, PNG and PDF and one SVG per frame",
        os.map (·.format.name) == #["svg", "png", "pdf"] ++ Array.replicate x.frames.size "svg"),
      (s!"{name}: every frame is inert and is its file", (os.extract 3 os.size).zipIdx.all
        fun (o, k) => match o.bytes (), fs.frames[k]? with
          | .ok b, some i => Svg.isInert i.document && b == i.document.toUTF8
          | _, _ => false),
      (s!"{name}: no frame has a layout problem", x.problems.isEmpty),
      (s!"{name}: the page names both parameters", fs.axisName != "" && fs.stepName != "" &&
        fs.stepCaptions.size * fs.axisValues.size == fs.frames.size),
      (s!"{name}: the poster's PDF passes the structural check",
        match (os[2]?.map (·.bytes ()) : Option (Except String ByteArray)) with
        | some (.ok b) => (Pdf.check b).isOk
        | _ => false)]

end PILeanTest.Explorers
