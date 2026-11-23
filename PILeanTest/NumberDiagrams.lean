/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean
import PILean.Trust.Attr
import PILeanTest.Diagrams

/-!
# The gallery of plots of sequences, grids of numbers and lattices, their specifications and checks

Figures of the kinds `SeqPlot`, `CellPlot` and `PlaneLattice`, each with the attribute `figure`
and a specification linked by `figure_proves`: the figure is drawn faithfully (every mark
accounted for by the kind's `Faithful`), and what it draws is written out and checked by the
kernel (the values of a sequence on its range, the numbers marked in a grid, the lattice points
drawn and those marked). Changing the data breaks the specification
(`PILeanTest.SpecMutations`). The package `pilean-mathlib` ties figures of these kinds to
Mathlib's functions and predicates.

`checks` holds what the theorems do not: each predicate refuses diagrams with a planted fault in
every class of mark (a point, its colour, a curve, an axis, a tick, a tick's label, a legend's
sample and name, a cell, its colour, its text, a heading, a lattice point, its colour, the
parallelogram), the figures pass the layout checks of plane figures in both themes (a plot's
points may stand closer than markers of a geometric figure, but their discs never overlap), and
hostile data is refused within the caps.
-/

namespace PILeanTest.NumberDiagrams

open PILean PILean.Diagram PILeanTest.Diagrams

/-! ### Euler's totient -/

/-- Euler's totient: the number of `a < n` with `gcd n a = 1`. -/
def phi (n : Nat) : Nat := ((List.range n).filter fun a => Nat.gcd n a == 1).length

/-- Euler's totient on `1, …, 100`. -/
def totientPlot : SeqPlot := { lo := 1, hi := 100, series := [("φ(n)", fun n => phi n)] }

/-- The plot of Euler's totient. -/
@[figure]
def totient : Diagram := { totientPlot.figure with title := "Euler's totient φ(n), 1 ≤ n ≤ 100" }

/-- The figure plots Euler's totient faithfully on `1, …, 100`: its points are exactly
`(n, φ(n))` (`SeqPlot.mem_data`), with the values written out, under the one name `φ(n)`, and it
draws no curve. -/
theorem totient_spec :
    totientPlot.Faithful totientPlot.layout totient ∧
    totientPlot.lo = 1 ∧ totientPlot.hi = 100 ∧ totientPlot.names = ["φ(n)"] ∧
    totientPlot.series.map (fun s => totientPlot.indices.map s.2) =
      [[1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4, 12, 6, 8, 8, 16, 6, 18, 8, 12, 10, 22, 8, 20, 12, 18,
        12, 28, 8, 30, 16, 20, 16, 24, 12, 36, 18, 24, 16, 40, 12, 42, 20, 24, 22, 46, 16, 42, 20,
        32, 24, 52, 18, 40, 24, 36, 28, 58, 16, 60, 30, 36, 32, 48, 20, 66, 32, 44, 24, 70, 24, 72,
        36, 40, 36, 60, 24, 78, 32, 54, 40, 82, 24, 64, 42, 56, 40, 88, 24, 72, 44, 60, 46, 72, 32,
        96, 42, 60, 40]] ∧
    totientPlot.curves.length = 0 := by
  exact ⟨totientPlot.builder_faithful (by decide +kernel), rfl, rfl, by decide +kernel,
    by decide +kernel, rfl⟩

figure_proves totient totient_spec

/-! ### A sieve of Eratosthenes -/

/-- Whether `n` is prime: at least 2 and no divisor among `2, …, n - 1`. -/
def isPrime (n : Nat) : Bool := 2 ≤ n && (List.range' 2 (n - 2)).all fun d => n % d != 0

/-- The numbers `1, …, 100` in ten rows of ten, `1` at the top left, each written in its cell,
the primes marked. -/
def sievePlot : CellPlot where
  cells := (List.range 100).map fun i =>
    { key := i + 1, pos := ((i % 10 : Nat), -((i / 10 : Nat) : Int)), marked := isPrime (i + 1),
      text := toString (i + 1) }

/-- The sieve. -/
@[figure]
def sieve : Diagram :=
  { sievePlot.figure with title := "The primes up to 100", width := 360 }

/-- The figure draws the hundred cells faithfully: their keys are `1, …, 100`, each written as
itself, in ten rows of ten, and the marked ones are exactly the 25 primes below 100 (written
out); it has no heading. -/
theorem sieve_spec :
    sievePlot.Faithful sieve ∧
    sievePlot.cells.map (·.key) = List.range' 1 100 ∧
    sievePlot.cells.all (fun c => c.text == toString c.key &&
      c.pos == ((((c.key - 1) % 10 : Nat) : Int), -(((c.key - 1) / 10 : Nat) : Int))) = true ∧
    (sievePlot.cells.filter (·.marked)).map (·.key) =
      [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
        97] ∧
    sievePlot.headings = [] ∧ sievePlot.solid = false := by
  exact ⟨sievePlot.builder_faithful (by decide +kernel), by decide +kernel, by decide +kernel,
    by decide +kernel, rfl, rfl⟩

figure_proves sieve sieve_spec

/-! ### The Gaussian primes -/

/-- Whether the Gaussian integer `a + b i` is a Gaussian prime: on an axis, `|a + b|` is a prime
`≡ 3 (mod 4)`; elsewhere `a² + b²` is prime. -/
def gaussianPrime (a b : Int) : Bool :=
  if a = 0 || b = 0 then
    let k := (a + b).natAbs
    isPrime k && k % 4 == 3
  else isPrime (a.natAbs ^ 2 + b.natAbs ^ 2)

/-- The Gaussian integers `a + b i` with `|a|, |b| ≤ 4`, the Gaussian primes marked. -/
def gaussianLattice : PlaneLattice :=
  { w1 := (1, 0), w2 := (0, 1), lo := (-4, -4), hi := (4, 4), marked := gaussianPrime,
    plainInk := .faint }

/-- The Gaussian primes. -/
@[figure]
def gaussian : Diagram :=
  { gaussianLattice.figure with title := "The Gaussian primes a + bi with |a|, |b| ≤ 4" }

/-- The figure draws the lattice `ℤ + ℤ i` faithfully in the window `[-4, 4]²`: its 81 points
are the `a + b i` with `|a|, |b| ≤ 4`, the marked ones (in accent 1, the others faint) exactly
the 32 Gaussian primes among them (written out). -/
theorem gaussian_spec :
    gaussianLattice.Faithful gaussian ∧
    gaussianLattice.w1 = (1, 0) ∧ gaussianLattice.w2 = (0, 1) ∧
    gaussianLattice.lo = (-4, -4) ∧ gaussianLattice.hi = (4, 4) ∧
    gaussianLattice.points = (List.range 9).flatMap (fun (a : Nat) => (List.range 9).map
      fun (b : Nat) => ((a : Int) - 4, (b : Int) - 4)) ∧
    gaussianLattice.plainInk = .faint ∧
    gaussianLattice.points.filter (fun (a, b) => gaussianLattice.marked a b) =
      [(-4, -1), (-4, 1), (-3, -2), (-3, 0), (-3, 2), (-2, -3), (-2, -1), (-2, 1), (-2, 3),
        (-1, -4), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 4), (0, -3), (0, 3), (1, -4),
        (1, -2), (1, -1), (1, 1), (1, 2), (1, 4), (2, -3), (2, -1), (2, 1), (2, 3), (3, -2),
        (3, 0), (3, 2), (4, -1), (4, 1)] := by
  exact ⟨gaussianLattice.builder_faithful (by decide +kernel), rfl, rfl, rfl, rfl,
    by decide +kernel, rfl, by decide +kernel⟩

figure_proves gaussian gaussian_spec

/-! ### A lattice with a skew basis -/

/-- The lattice `ℤ (3/2, 1/2) + ℤ (1/2, 3/2)` in the window `[-3, 3]²`. -/
def skewLattice : PlaneLattice :=
  { w1 := (3 / 2, 1 / 2), w2 := (1 / 2, 3 / 2), lo := (-3, -3), hi := (3, 3) }

/-- The skew lattice. -/
@[figure]
def skew : Diagram :=
  { skewLattice.figure with title := "The lattice ℤ(3/2, 1/2) + ℤ(1/2, 3/2)" }

/-- The figure draws the lattice `ℤ (3/2, 1/2) + ℤ (1/2, 3/2)` faithfully in `[-3, 3]²`: its
points are `m ω₁ + n ω₂` for the coefficients written out, none marked. -/
theorem skew_spec :
    skewLattice.Faithful skew ∧
    skewLattice.w1 = (3 / 2, 1 / 2) ∧ skewLattice.w2 = (1 / 2, 3 / 2) ∧
    skewLattice.lo = (-3, -3) ∧ skewLattice.hi = (3, 3) ∧
    skewLattice.points = [(-3, 3), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2),
      (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 0), (1, 1), (2, -2), (2, -1),
      (2, 0), (3, -3)] ∧
    skewLattice.points.all (fun (m, n) => !skewLattice.marked m n) = true ∧
    skewLattice.plainInk = .ink := by
  exact ⟨skewLattice.builder_faithful (by decide +kernel), rfl, rfl, rfl, rfl, by decide +kernel,
    by decide +kernel, rfl⟩

figure_proves skew skew_spec

/-! ### The gallery and the checks -/

/-- The figures by file stem. -/
def figures : Array (String × Diagram) :=
  #[("diagram-totient", totient), ("diagram-sieve", sieve), ("diagram-gaussian-primes", gaussian),
    ("diagram-skew-lattice", skew)]

/-- The gallery: each figure light and dark, as plane figures by file name. -/
def gallery : Array (String × Plane.Figure) :=
  figures.map (fun (n, d) => (n ++ ".svg", d.toPlane)) ++
    figures.map (fun (n, d) => (n ++ "-dark.svg", d.dark.toPlane))

/-- A plot of two sequences and a curve on `0, …, 12`, for the checks of faults. -/
def smallPlot : SeqPlot :=
  { lo := 0, hi := 12,
    series := [("n mod 3", fun n => (n % 3 : Nat)), ("3 + n mod 5", fun n => (3 + n % 5 : Nat))],
    curves := [("n / 3", fun n => (n : Rat) / 3)] }

/-- The small plot. -/
def small : Diagram := smallPlot.figure

/-- The position of the `k`-th mark (from 0) whose part satisfies `p`. -/
def posWhere (d : Diagram) (p : Part → Bool) (k : Nat := 0) : Nat :=
  ((d.marks.zipIdx.filter fun (m, _) => p m.part).map (·.2)).getD k 0

/-- The position of the first mark whose part is `p` and whose shape satisfies `q`. -/
def posShape (d : Diagram) (p : Part) (q : Shape → Bool) : Nat :=
  (d.marks.findIdx? fun m => m.part == p && q m.shape).getD 0

/-- Whether a shape is a text. -/
def isText : Shape → Bool
  | .text .. => true
  | _ => false

/-- Whether a shape is a dot. -/
def isDot : Shape → Bool
  | .dot _ => true
  | _ => false

/-- The text of a text mark replaced. -/
def retext (t : String) (m : Mark) : Mark :=
  match m.shape with
  | .text _ p sd => { m with shape := .text t p sd }
  | _ => m

/-- Each predicate holds of its figure and refuses planted faults in every class of mark. -/
def faultChecks : Array (String × Bool) :=
  let P := smallPlot
  let L := P.layout
  let ok := fun (d : Diagram) => decide (P.Faithful L d)
  let d0 := posOf small (.datum 0 4)
  let c0 := posOf small (.curve 0)
  let gl := gaussianLattice
  let okG := fun (d : Diagram) => decide (gl.Faithful d)
  let v0 := posOf gaussian (.vertex 0)
  let vp := posWhere gaussian (fun p => p == .vertex 1)
  let okS := fun (d : Diagram) => decide (sievePlot.Faithful d)
  let s1 := posOf sieve (.cell 2 0)
  #[("plot: faithful", ok small),
    ("plot: a point dropped is refused", !ok (dropMark small d0)),
    ("plot: a point moved to another value is refused", !ok (changeMark small d0 fun m =>
      { m with shape := .dot (SeqPlot.point L 4 2) })),
    ("plot: a point given to the other sequence is refused", !ok (changeMark small d0 fun m =>
      { m with part := .datum 1 4 })),
    ("plot: a point in the other sequence's colour is refused", !ok (changeMark small d0 fun m =>
      { m with ink := .series 1 false })),
    ("plot: an extra point is refused", !ok (addMark small
      { part := .datum 0 13, shape := .dot (SeqPlot.point L 13 1), ink := .series 0 false })),
    ("plot: a point drawn as a circle is refused", !ok (changeMark small d0 fun m =>
      { m with shape := .circle (SeqPlot.point L 4 1) (1 / 20) })),
    ("plot: the curve dropped is refused", !ok (dropMark small c0)),
    ("plot: the curve bent is refused", !ok (changeMark small c0 fun m =>
      { m with shape := .polyline [(0, 0), (3, 2)] })),
    ("plot: the curve in another colour is refused", !ok (changeMark small c0 fun m =>
      { m with ink := .series 0 false })),
    ("plot: the index axis dropped is refused", !ok (dropMark small (posOf small (.axis 0)))),
    ("plot: the value axis moved onto the first points is refused",
      !ok (changeMark small (posOf small (.axis 1)) fun m =>
        { m with shape := .segment (0, 0) (0, 2) })),
    ("plot: a tick dropped is refused", !ok (dropMark small (posOf small .guide))),
    ("plot: a tick's label changed is refused", !ok (changeMark small (posOf small (.note 0))
      (retext "7"))),
    ("plot: a value's label changed is refused", !ok (changeMark small (posOf small (.note 1))
      (retext "9"))),
    ("plot: a name of the legend changed is refused", !ok (changeMark small
      (posOf small (.note 2)) (retext "n mod 4"))),
    ("plot: the legend's sample in another colour is refused", !ok (changeMark small
      (posShape small .guide isDot) fun m => { m with ink := .series 1 false })),
    ("plot: the name of the index axis changed is refused", !ok (changeMark small
      (posOf small (.note 3)) (retext "k"))),
    ("plot: an extra guide is refused", !ok (addMark small
      { part := .guide, shape := .segment (0, 0) (3, 2), ink := .faint })),
    ("plot: an extra note is refused", !ok (addMark small
      { part := .note 4, shape := .text "a claim" (1, 1) .center })),
    ("plot: a mark of another kind is refused", !ok (addMark small
      { part := .vertex 0, shape := .dot (0, 0) })),
    ("plot: the totient figure is faithful", decide (totientPlot.Faithful totientPlot.layout totient)),
    ("grid: faithful", okS sieve),
    ("grid: a prime unmarked is refused", !okS (changeMark sieve s1 fun m => { m with ink := .faint })),
    ("grid: a cell marked solid instead of tinted is refused", !okS (changeMark sieve s1 fun m =>
      { m with ink := .solid 0 })),
    ("grid: a cell moved is refused", !okS (changeMark sieve s1 fun m =>
      { m with shape := .rect (5, 5) (6, 6) })),
    ("grid: a cell dropped is refused", !okS (dropMark sieve s1)),
    ("grid: a number changed is refused", !okS (changeMark sieve (s1 + 1) (retext "4"))),
    ("grid: an extra heading is refused", !okS (addMark sieve
      { part := .header 0 0, shape := .text "primes" (0, 2) .center })),
    ("grid: an extra cell is refused", !okS (addMark sieve
      { part := .cell 101 0, shape := .rect (0, 1) (1, 2), ink := .tint 0 })),
    ("lattice: faithful", okG gaussian),
    ("lattice: a point dropped is refused", !okG (dropMark gaussian v0)),
    ("lattice: a point moved is refused", !okG (changeMark gaussian v0 fun m =>
      { m with shape := .dot (1 / 2, 1 / 2) })),
    ("lattice: a point marked that is not is refused", !okG (changeMark gaussian v0 fun m =>
      { m with ink := .accent 1 })),
    ("lattice: a marked point drawn plain is refused", !okG (changeMark gaussian
      (posOf gaussian (.vertex 3)) fun m => { m with ink := .faint })),
    ("lattice: two points' parts exchanged is refused", !okG (changeMark (changeMark gaussian v0
      fun m => { m with part := .vertex 1 }) vp fun m => { m with part := .vertex 0 })),
    ("lattice: an extra point is refused", !okG (addMark gaussian
      { part := .vertex 81, shape := .dot (5, 5) })),
    ("lattice: the parallelogram changed is refused", !okG (changeMark gaussian
      (posOf gaussian (.note 0)) fun m => { m with shape := .polyline [(0, 0), (2, 0), (2, 1),
        (0, 1), (0, 0)] })),
    ("lattice: an axis dropped is refused", !okG (dropMark gaussian (posOf gaussian (.axis 1)))),
    ("lattice: a label added is refused", !okG (addMark gaussian
      { part := .note 1, shape := .text "1 + i" (1, 1) .aboveRight }))]

/-- The layouts have the properties they are drawn for. -/
def layoutChecks : Array (String × Bool) :=
  let L := totientPlot.layout
  #[("plot: the index axis of 1, …, 100 starts at 0 with ticks every 20",
      L.xlo == 0 && L.xstep == 20 && totientPlot.xticks L == [0, 20, 40, 60, 80, 100]),
    ("plot: the values 1, …, 96 are shown from 0 to 100 with ticks every 20",
      L.vlo == 0 && L.vhi == 100 && L.ystep == 20),
    ("plot: no point lies on an axis: the axes are a tenth of a unit outside the points",
      (totientPlot.dataTriples L).all fun (_, _, p) =>
        p.1 > SeqPlot.axisX L && p.2 > SeqPlot.axisY L),
    ("plot: the points of a plot of 100 indices are 1.8 pixels in radius, of 12 indices 3",
      SeqPlot.dotRadiusFor 100 == 1.8 && SeqPlot.dotRadiusFor 12 == 3),
    ("grid: the sieve's cells are distinct", (sievePlot.cells.map (·.pos)).eraseDups.length == 100),
    ("lattice: the bound of the skew lattice covers its window: every point m ω₁ + n ω₂ with \
      |m|, |n| ≤ 20 in the window has |m|, |n| ≤ bound",
      let Λ := skewLattice
      ((List.range 41).flatMap fun (a : Nat) => (List.range 41).map fun (b : Nat) =>
        ((a : Int) - 20, (b : Int) - 20)).all fun (m, n) =>
          !Λ.inWindow (Λ.at_ m n) || (m.natAbs ≤ Λ.bound && n.natAbs ≤ Λ.bound)),
    ("lattice: the points on the axes record that they are on them",
      let fig := gaussian.toPlane
      let onAxes := fig.leaves.filter fun lf => lf.info.title == "vertex 4" ||
        lf.info.title == "vertex 36"
      onAxes.size == 2 && onAxes.all fun lf => lf.look.incidences.any fun r =>
        r.2 == "axis 0" || r.2 == "axis 1")]

/-- Hostile data is refused within the caps, before any work that grows with it. -/
def boundChecks : Array (String × Bool) :=
  let note := fun (d : Diagram) => d.marks.length == 1 && d.data.isEmpty && d.cells.isEmpty &&
    d.dots.isEmpty
  #[("bounds: a plot of a billion indices is a note",
      note (SeqPlot.figure { lo := 0, hi := 1000000000, series := [("n", fun n => n)] })),
    ("bounds: a plot of seven sequences is a note",
      note (SeqPlot.figure { lo := 0, hi := 3, series := List.replicate 7 ("n", fun n => n) })),
    ("bounds: a plot whose range is empty is a note",
      note (SeqPlot.figure { lo := 5, hi := 3, series := [("n", fun n => n)] })),
    ("bounds: a plot with a name of 10000 characters is a note",
      let long := String.ofList (List.replicate 10000 'a')
      note (SeqPlot.figure { lo := 0, hi := 3, series := [(long, fun n => n)] })),
    ("bounds: a plot of values near 10^40 is a note",
      let big : Nat → Rat := fun n => (10 : Rat) ^ 40 * n
      note (SeqPlot.figure { lo := 0, hi := 3, series := [("big", big)] })),
    ("bounds: a grid of a million cells is a note",
      let c : NumberCell := { key := 0, pos := (0, 0), marked := false }
      note (CellPlot.figure { cells := List.replicate 1000000 c })),
    ("bounds: a grid with a text of 10000 characters is a note",
      let long := String.ofList (List.replicate 10000 'a')
      note (CellPlot.figure { cells := [{ key := 0, pos := (0, 0), marked := false, text := long }] })),
    ("bounds: a lattice in a window of a billion units is a note",
      let Λ : PlaneLattice := { w1 := (1, 0), w2 := (0, 1), lo := (-1000000000, 0), hi := (1000000000, 1) }
      note Λ.figure),
    ("bounds: a lattice of dependent periods is a note",
      note (PlaneLattice.figure { w1 := (1, 2), w2 := (2, 4), lo := (-1, -1), hi := (1, 1) }))]

/-- The figures pass the layout checks of plane figures in both themes (a plot's points by
`plotProblems`). -/
def planeChecks : Array (String × Bool) :=
  (gallery.push ("small-plot.svg", small.toPlane)).map fun (n, f) =>
    let ps := plotProblems f
    (s!"layout checks: {n} has no problems ({ps})", ps.isEmpty)

/-- Every check of this module. -/
def checks : Array (String × Bool) := faultChecks ++ layoutChecks ++ boundChecks ++ planeChecks

end PILeanTest.NumberDiagrams
