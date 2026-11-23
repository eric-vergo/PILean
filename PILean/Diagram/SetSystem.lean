/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Diagram.Graph

/-!
# Set systems: Venn diagrams and incidence drawings

A `SetSystem` has the elements `0, …, n - 1` and a list of sets of them. With one, two or three
sets it is drawn as a Venn diagram (`venn`): set `s` is a circle with exact rational centre and
radius, and each element's name is written at a point of its region: the region of the sets that
contain it. `venn_inside` proves that the point an element is written at lies inside circle `s`
(by exact rational arithmetic, `|p - c|² < r²`) exactly when the element belongs to set `s`, for
every element and every set. A region holds at most `regionCap` names (the elements in no set at
most `outsideCap`), which `venn` checks.

Any number of sets is drawn as an incidence drawing (`incidence`): the elements in a row at the
bottom, the sets in a row above, an edge from element `x` to set `s` exactly when `x ∈ s`, a
`FinGraph` whose faithfulness carries over (`incidence_edges`).

## Main definitions

* `SetSystem`, `SetSystem.mem`, `SetSystem.mask`, `vennCentres`, `vennRadius`, `slot`, `inside`
* `SetSystem.venn`, `SetSystem.FaithfulVenn`, `Diagram.members`
* `SetSystem.toFinGraph`, `SetSystem.incidence`

## Main results

* `slots_correct`: each place of each region is inside exactly the region's circles (checked by
  the kernel in exact arithmetic).
* `SetSystem.venn_faithful`, `SetSystem.venn_inside`.
* `SetSystem.incidence_edges`: an edge `(x, n + s)` is drawn exactly when `x ∈ s`.
-/

namespace PILean.Diagram

/-- The members a diagram writes: `(x, mask, p)` for each mark of the part `member x mask` that is
a text at `p`, in order. -/
def Diagram.members (d : Diagram) : List (Nat × Nat × QPoint) :=
  d.marks.filterMap fun m => match m.part, m.shape with
    | .member x k, .text _ p _ => some (x, k, p)
    | _, _ => none

/-- The radius of the circles of a Venn diagram. -/
def vennRadius : Rat := 4 / 5

/-- The centres of the circles of a Venn diagram of `k` sets (1, 2 or 3). -/
def vennCentres : Nat → List QPoint
  | 1 => [(0, 0)]
  | 2 => [(-9 / 20, 0), (9 / 20, 0)]
  | _ => [(-1 / 2, 2 / 7), (1 / 2, 2 / 7), (0, -4 / 7)]

/-- Whether `p` is inside the circle with centre `c` and radius `vennRadius`, exactly. -/
def inside (c p : QPoint) : Bool :=
  decide ((p.1 - c.1) * (p.1 - c.1) + (p.2 - c.2) * (p.2 - c.2) < vennRadius * vennRadius)

/-- The most names a region inside some circle holds. -/
def regionCap : Nat := 3

/-- The most names the region outside every circle holds. -/
def outsideCap : Nat := 6

/-- The anchor of the region `mask` (bit `s` set for the sets it is inside) in a diagram of `k`
sets. -/
def anchor : Nat → Nat → QPoint
  | 1, 1 => (0, 0)
  | 2, 1 => (-4 / 5, 0)
  | 2, 2 => (4 / 5, 0)
  | 2, 3 => (0, 0)
  | 3, 1 => (-17 / 20, 9 / 20)
  | 3, 2 => (17 / 20, 9 / 20)
  | 3, 3 => (0, 3 / 5)
  | 3, 4 => (0, -19 / 20)
  | 3, 5 => (-13 / 25, -3 / 10)
  | 3, 6 => (13 / 25, -3 / 10)
  | 3, 7 => (0, 0)
  | _, _ => (8 / 5, 3 / 5)

/-- Place `t` of the region `mask` in a diagram of `k` sets: the anchor and, below and above it,
steps of `4/25`; outside every circle a column going down by `1/5`. -/
def slot (k mask t : Nat) : QPoint :=
  let a := anchor k mask
  if mask = 0 then (a.1, a.2 - t / 5)
  else (a.1, a.2 + (if t % 2 = 1 then -1 else 1) * ((t + 1) / 2 : Nat) * (4 / 25))

/-- The number of places of a region: `outsideCap` outside every circle, `regionCap` inside. -/
def capOf (mask : Nat) : Nat := if mask = 0 then outsideCap else regionCap

/-- Whether every place of every region of the diagrams of 1, 2 and 3 sets is inside exactly the
circles of its region. -/
def slotsOk : Bool :=
  [1, 2, 3].all fun k => (List.range (2 ^ k)).all fun mask => (List.range (capOf mask)).all
    fun t => (List.range k).all fun s =>
      inside ((vennCentres k).getD s (0, 0)) (slot k mask t) == mask.testBit s

/-- Every place of every region is inside exactly the circles of its region (decided by the
kernel in exact arithmetic). -/
theorem slots_correct : slotsOk = true := by decide +kernel

/-- Place `t < capOf mask` of the region `mask < 2 ^ k` of a diagram of `k ∈ {1, 2, 3}` sets is
inside circle `s < k` exactly when bit `s` of `mask` is set. -/
theorem inside_slot {k mask t s : Nat} (hk : k = 1 ∨ k = 2 ∨ k = 3) (hm : mask < 2 ^ k)
    (ht : t < capOf mask) (hs : s < k) :
    inside ((vennCentres k).getD s (0, 0)) (slot k mask t) = mask.testBit s := by
  have h := slots_correct
  simp only [slotsOk, List.all_eq_true, List.mem_cons, List.mem_range, beq_iff_eq] at h
  exact h k (by omega) mask hm t ht s hs

/-- A set system: the elements `0, …, n - 1` with their names, and the sets with theirs. -/
structure SetSystem where
  /-- The number of elements. -/
  n : Nat
  /-- The sets, each a list of elements. -/
  sets : List (List Nat)
  /-- The elements' names. -/
  names : Array String := #[]
  /-- The sets' names. -/
  setNames : Array String := #[]

namespace SetSystem

/-- Whether `x` belongs to set `s`. -/
def mem (S : SetSystem) (x s : Nat) : Bool := (S.sets.getD s []).contains x

/-- The region of `x` among the first three sets: bit `s` set when `x` belongs to set `s`. -/
def mask (S : SetSystem) (x : Nat) : Nat :=
  (if S.mem x 0 then 1 else 0) + (if S.mem x 1 then 2 else 0) + (if S.mem x 2 then 4 else 0)

/-- Bit `s < 3` of the region of `x` is set exactly when `x` belongs to set `s`. -/
theorem testBit_mask (S : SetSystem) (x s : Nat) (hs : s < 3) :
    (S.mask x).testBit s = S.mem x s := by
  unfold mask
  have : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  rcases this with rfl | rfl | rfl <;>
    cases S.mem x 0 <;> cases S.mem x 1 <;> cases S.mem x 2 <;> decide

/-- The region of `x` is below `2 ^ k` when `x` belongs to no set beyond the first `k`. -/
theorem mask_lt (S : SetSystem) (x : Nat) (hk : S.sets.length ≤ 3) :
    S.mask x < 2 ^ S.sets.length := by
  have h : ∀ s, S.sets.length ≤ s → S.mem x s = false := fun s hs => by
    simp [mem, List.getD_eq_getElem?_getD, List.getElem?_eq_none hs]
  unfold mask
  have : S.sets.length = 0 ∨ S.sets.length = 1 ∨ S.sets.length = 2 ∨ S.sets.length = 3 := by
    omega
  rcases this with h0 | h0 | h0 | h0 <;> rw [h0]
  · rw [h 0 (by omega), h 1 (by omega), h 2 (by omega)]; decide
  · rw [h 1 (by omega), h 2 (by omega)]; cases S.mem x 0 <;> decide
  · rw [h 2 (by omega)]; cases S.mem x 0 <;> cases S.mem x 1 <;> decide
  · cases S.mem x 0 <;> cases S.mem x 1 <;> cases S.mem x 2 <;> decide

/-- The place of `x` in its region: the number of elements before it in the same region. -/
def rank (S : SetSystem) (x : Nat) : Nat :=
  ((List.range x).filter fun y => S.mask y == S.mask x).length

/-- Whether every region holds at most its number of places. -/
def fits (S : SetSystem) : Bool := (List.range S.n).all fun x => S.rank x < capOf (S.mask x)

/-- The name of element `x`. -/
def name (S : SetSystem) (x : Nat) : String := S.names.getD x (toString x)

/-- The members as the Venn diagram writes them: `(x, region, place)` for each element. -/
def memberList (S : SetSystem) : List (Nat × Nat × QPoint) :=
  (List.range S.n).map fun x => (x, S.mask x, slot S.sets.length (S.mask x) (S.rank x))

/-- The Venn diagram: a tinted circle for each set, the sets' names beyond the circles, then each
element's name at its place. -/
def venn (S : SetSystem) : Diagram where
  marks := (List.range S.sets.length).map (fun s =>
      { part := .set s, shape := .circle ((vennCentres S.sets.length).getD s (0, 0)) vennRadius,
        ink := .tint s }) ++
    (List.range S.sets.length).map (fun s =>
      let c := (vennCentres S.sets.length).getD s (0, 0)
      { part := .note s, ink := .accent s,
        shape := .text (S.setNames.getD s s!"S{s}")
          (c.1 * (3 / 2), c.2 + (if c.2 < 0 then -1 else 1) * (17 / 20)) .center }) ++
    S.memberList.map fun (x, k, p) => { part := .member x k, shape := .text (S.name x) p .center }
  width := 400

/-- The Venn diagram is faithful: the elements it writes, with their regions and places, are
exactly `memberList`, in order, and its circles are the sets' circles, in order. -/
def FaithfulVenn (S : SetSystem) (d : Diagram) : Prop :=
  d.members = S.memberList ∧
    (d.marks.filterMap fun m => match m.part, m.shape with
      | .set s, .circle c r => some (s, c, r)
      | _, _ => none) =
    (List.range S.sets.length).map fun s => (s, (vennCentres S.sets.length).getD s (0, 0), vennRadius)

instance (S : SetSystem) (d : Diagram) : Decidable (S.FaithfulVenn d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The Venn diagram is faithful. -/
theorem venn_faithful (S : SetSystem) : S.FaithfulVenn S.venn := by
  refine ⟨?_, ?_⟩
  · simp [Diagram.members, venn, List.filterMap_append, List.filterMap_map,
      Function.comp_def, memberList]
  · simp [venn, List.filterMap_append, List.filterMap_map,
      Function.comp_def, memberList]

/-- In the Venn diagram of one to three sets whose regions fit (`fits`), the name of every
element `x` is written at a point inside the circle of set `s` exactly when `x` belongs to `s`,
for every set `s`. -/
theorem venn_inside (S : SetSystem) (hk : 1 ≤ S.sets.length ∧ S.sets.length ≤ 3)
    (hfit : S.fits = true) {x k : Nat} {p : QPoint} (hx : (x, k, p) ∈ S.venn.members) {s : Nat}
    (hs : s < S.sets.length) :
    inside ((vennCentres S.sets.length).getD s (0, 0)) p = S.mem x s := by
  rw [(S.venn_faithful).1, memberList, List.mem_map] at hx
  obtain ⟨y, hy, he⟩ := hx
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, -, rfl⟩ := he
  have hr : S.rank y < capOf (S.mask y) := by
    simp only [fits, List.all_eq_true, decide_eq_true_eq] at hfit
    exact hfit y hy
  rw [inside_slot (by omega) (S.mask_lt y hk.2) hr hs, S.testBit_mask y s (by omega)]

/-- The most elements a Venn figure places (finding each element's place takes `n²` steps). -/
def maxVennElements : Nat := 64

/-- The Venn figure: the Venn diagram of one to three sets of at most `maxVennElements` elements
whose regions fit, or a note. -/
def vennFigure (S : SetSystem) : Diagram :=
  Diagram.capped (decide (1 ≤ S.sets.length ∧ S.sets.length ≤ 3 ∧ S.n ≤ maxVennElements) &&
    S.fits) "a Venn diagram needs one to three sets and regions that fit" S.venn

/-- The incidence graph: the elements `0, …, n - 1` and the sets `n, …, n + m - 1`, an edge
`(x, n + s)` exactly when `x ∈ s`. -/
def toFinGraph (S : SetSystem) : FinGraph where
  n := S.n + S.sets.length
  adj x y := x.val < S.n && S.n ≤ y.val && S.mem x.val (y.val - S.n)
  directed := true
  arrowheads := false
  names := ((List.range S.n).map S.name ++
    (List.range S.sets.length).map fun s => S.setNames.getD s s!"S{s}").toArray

/-- The incidence layout: the elements in a row at height 0, the sets in a row at height 1, each
row centred. -/
def incidenceLayout (S : SetSystem) : Layout where
  pos i :=
    if i < S.n then ((i : Rat) - ((S.n : Rat) - 1) / 2, 0)
    else (((i - S.n : Nat) : Rat) * 2 - ((S.sets.length : Rat) - 1), 2)

/-- The incidence drawing. -/
def incidence (S : SetSystem) : Diagram :=
  { S.toFinGraph.draw S.incidenceLayout with
    width := min 560 (36 * (max S.n (2 * S.sets.length)).toFloat + 24) }

/-- The incidence figure: the incidence drawing, or a note for more than `FinGraph.maxVertices`
elements and sets together. -/
def incidenceFigure (S : SetSystem) : Diagram :=
  Diagram.capped (decide (S.n + S.sets.length ≤ FinGraph.maxVertices))
    "too many elements and sets to draw" S.incidence

/-- An edge `(x, y)` is drawn in the incidence drawing exactly when `x` is an element, `y = n + s`
for a set `s`, and `x ∈ s`. -/
theorem incidence_edges (S : SetSystem) (x y : Nat) :
    (x, y) ∈ S.incidence.edges ↔
      x < S.n ∧ S.n ≤ y ∧ y < S.n + S.sets.length ∧ S.mem x (y - S.n) = true := by
  rw [incidence, show ({ S.toFinGraph.draw S.incidenceLayout with
      width := min 560 (36 * (max S.n (2 * S.sets.length)).toFloat + 24) } : Diagram).edges =
      (S.toFinGraph.draw S.incidenceLayout).edges from rfl,
    (S.toFinGraph.draw_faithful _).1, FinGraph.mem_edgePairs]
  simp only [toFinGraph, FinGraph.drawn, ite_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hx, hy, ⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, hy, h3⟩
  · rintro ⟨h1, h2, hy, h3⟩
    exact ⟨by omega, hy, ⟨h1, h2⟩, h3⟩

end SetSystem

/-- The hypotheses can be met: two sets `{0, 1}` and `{1, 2}` of three elements fit, and element
1 is in the middle region. -/
example : (SetSystem.mk 3 [[0, 1], [1, 2]] #[] #[]).fits = true ∧
    (SetSystem.mk 3 [[0, 1], [1, 2]] #[] #[]).mask 1 = 3 := by decide

end PILean.Diagram
