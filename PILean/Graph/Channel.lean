/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Geometry
import PILean.Sort
import Std.Data.HashMap

/-!
# Tracks of the horizontal runs in a routing channel

Between two layers of a bundled drawing (`Routing.bundled`) lies a *channel*: a band across the
drawing in which every edge that changes its position across the layers does so on a horizontal
*run*, and every run has a *track* of its own height. A run has two ends; the vertical piece at
an end reaches the channel's upper side (`Reach.up`: it comes from the layer above) or its lower
side (`Reach.down`). This is the channel routing problem of circuit layout with two-terminal
nets, and the method is that of its classics:

* **Vertical constraints** (Hashimoto and Stevens): where an end reaching up and an end reaching
  down stand at one column (closer than `laneGap`), the run of the first must lie above that of
  the second, or their vertical pieces would overlap. The constraints are kept through one *hub*
  per pair of such columns, so their number is linear in the runs.
* **Nesting of the runs that turn the same way** (crossing minimisation between lanes): a run
  from an end reaching up at `a` to one reaching down at `b` goes right when `b > a`. Of two
  overlapping runs going right, the one whose ends lie further right (larger `a`, then larger
  `b`) is placed above the other: then they do not cross, where the other order makes them cross
  twice; two runs whose order across the layers changes cross once in either order. The runs
  going left are nested the same way, mirrored. So two runs of one channel cross at most once,
  and only when their ends' order requires it.
* **Doglegs** (Deutsch): when the constraints form a cycle (two runs that swap two columns
  between them), one run is split at a free column into two parts on two tracks, joined by a
  vertical jog.
* **Tracks** (`tracksInOrder`, the left-edge rule): the runs are placed in an order that every
  constraint keeps (Kahn's algorithm: the next run is one whose runs that must lie above it are
  placed; among those, the earliest of its turning direction's nesting order, the two directions
  in step), and each gets the track below the lowest of the runs placed before it that it overlaps
  (within `trackGap`), so the number of tracks is the longest chain of overlapping runs in that
  order. Two overlapping runs never share a track (`tracksInOrder_ne`, proved), and every
  constraint is kept, because two constrained runs overlap and the first is placed first.

Work, for `k` runs in the channel: `O(k²)` comparisons (the nesting order and the tracks compare
the runs pairwise; the constraints are linear through the hubs), and at most `k` doglegs, each
`O(k)` to find its column.

## References

* Hashimoto, Stevens, *Wire routing by optimizing channel assignment within large apertures*,
  Design Automation Workshop 1971.
* Deutsch, *A "dogleg" channel router*, Design Automation Conference 1976.
* Kahn, *Topological sorting of large networks*, Communications of the ACM 5 (1962).

## Main definitions

* `Reach`, `RunEnd`, `RunSpec`, `Placed`: a run and where it was placed.
* `overlaps`, `tracksInOrder`: the tracks of runs in a given order; `tracksInOrder_ne`.
* `placeRuns`: the order, the doglegs and the tracks of a channel.
-/

namespace PILean.Graph

/-- The side of the channel that the vertical piece at an end of a run reaches. -/
inductive Reach where
  /-- The upper side: the piece comes from the layer above. -/
  | up
  /-- The lower side: the piece goes on to the layer below. -/
  | down
  deriving BEq, Inhabited, Repr

/-- One end of a run: its position across the layers, the side its vertical piece reaches, and
the vertical piece it belongs to (`owner`: a node's exit or entry trunk, the lane of a long edge,
a corridor beside a node; `none` for the end of a jog, whose column is free). Ends with one
owner share their vertical piece; ends of two owners never stand at one column on the same
side. -/
structure RunEnd where
  /-- The position across the layers. -/
  x : Float
  /-- The side the vertical piece reaches. -/
  reach : Reach
  /-- The vertical piece. -/
  owner : Option Nat
  deriving Inhabited, Repr

/-- A run of a route through a channel: its ends in the order the route travels. -/
structure RunSpec where
  /-- The end the route comes from. -/
  start : RunEnd
  /-- The end the route goes on from. -/
  finish : RunEnd
  deriving Inhabited, Repr

/-- Where a run was placed (tracks counted from the channel's upper side). -/
inductive Placed where
  /-- On one track. -/
  | track (t : Nat)
  /-- Split at the free column `x`: the part from the start on track `t₁`, a vertical jog at
  `x`, and the part to the finish on track `t₂`. -/
  | jog (t₁ : Nat) (x : Float) (t₂ : Nat)
  deriving Inhabited, Repr

/-- The stretch across the layers that a run covers. -/
def RunSpec.span (r : RunSpec) : Float × Float :=
  (min r.start.x r.finish.x, max r.start.x r.finish.x)

/-- Whether two stretches `p` and `q` overlap or come closer than `gap`. Symmetric
(`overlaps_comm`). -/
def overlaps (gap : Float) (p q : Float × Float) : Bool :=
  p.1 < q.2 + gap && q.1 < p.2 + gap

theorem overlaps_comm (gap : Float) (p q : Float × Float) :
    overlaps gap p q = overlaps gap q p := by
  simp only [overlaps, Bool.and_comm]

section Tracks

variable {α : Type}

/-- The track of an item placed after the items `placed` (each with its track): one below the
lowest track among those it is in conflict with (`c q p`), or `0`. -/
def trackAfter (c : α → α → Bool) (placed : List (α × Nat)) (p : α) : Nat :=
  placed.foldl (fun t q => if c q.1 p then max t (q.2 + 1) else t) 0

/-- `tracksInOrder` with the items placed so far (`placed`, the last placed first). -/
def tracksAux (c : α → α → Bool) : List (α × Nat) → List α → List Nat
  | _, [] => []
  | placed, p :: ps =>
    let t := trackAfter c placed p
    t :: tracksAux c ((p, t) :: placed) ps

/-- The tracks of items placed in the order given (the left-edge rule): each gets the track
below the lowest of the earlier items it is in conflict with (`c`), or the first. -/
def tracksInOrder (c : α → α → Bool) (ps : List α) : List Nat :=
  tracksAux c [] ps

theorem foldl_max_ge (c : α → α → Bool) (p : α) :
    ∀ (placed : List (α × Nat)) (t : Nat),
      t ≤ placed.foldl (fun t q => if c q.1 p then max t (q.2 + 1) else t) t
  | [], _ => Nat.le_refl _
  | q :: qs, t => by
    simp only [List.foldl_cons]
    refine Nat.le_trans ?_ (foldl_max_ge c p qs _)
    split
    · exact Nat.le_max_left _ _
    · exact Nat.le_refl _

theorem foldl_max_member (c : α → α → Bool) (p : α) :
    ∀ (placed : List (α × Nat)) (t : Nat) (q : α × Nat),
      q ∈ placed → c q.1 p = true →
      q.2 + 1 ≤ placed.foldl (fun t q => if c q.1 p then max t (q.2 + 1) else t) t
  | [], _, _, h, _ => by simp at h
  | r :: rs, t, q, h, hc => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · refine Nat.le_trans ?_ (foldl_max_ge c p rs _)
      simp only [hc, ite_true]
      exact Nat.le_max_right _ _
    · exact foldl_max_member c p rs _ q h hc

/-- An item placed after one it is in conflict with gets a deeper track. -/
theorem trackAfter_gt (c : α → α → Bool) (placed : List (α × Nat)) (p : α) (q : α × Nat)
    (h : q ∈ placed) (hc : c q.1 p = true) : q.2 < trackAfter c placed p :=
  foldl_max_member c p placed 0 q h hc

theorem tracksAux_length (c : α → α → Bool) :
    ∀ (placed : List (α × Nat)) (ps : List α), (tracksAux c placed ps).length = ps.length
  | _, [] => rfl
  | placed, p :: ps => by
    simp only [tracksAux, List.length_cons]
    rw [tracksAux_length]

/-- When `ps[j]` is placed, every item of `placed` and every `ps[i]` with `i < j` is among the
placed items with its track. -/
theorem tracksAux_gt (c : α → α → Bool) :
    ∀ (placed : List (α × Nat)) (ps : List α) (j : Nat) (hj : j < ps.length),
      (∀ q ∈ placed, c q.1 ps[j] = true →
        q.2 < (tracksAux c placed ps)[j]'(by rw [tracksAux_length]; exact hj)) ∧
      (∀ (i : Nat) (hij : i < j), c ps[i] ps[j] = true →
        (tracksAux c placed ps)[i]'(by rw [tracksAux_length]; omega) <
          (tracksAux c placed ps)[j]'(by rw [tracksAux_length]; exact hj))
  | _, [], j, hj => by simp at hj
  | placed, p :: ps, 0, _ => by
    refine ⟨fun q hq hc => ?_, fun i hij _ => by omega⟩
    simp only [tracksAux, List.getElem_cons_zero]
    exact trackAfter_gt c placed p q hq hc
  | placed, p :: ps, j + 1, hj => by
    have hj' : j < ps.length := by simp at hj; omega
    have ih := tracksAux_gt c ((p, trackAfter c placed p) :: placed) ps j hj'
    refine ⟨fun q hq hc => ?_, fun i hij hc => ?_⟩
    · simp only [tracksAux, List.getElem_cons_succ]
      exact ih.1 q (List.mem_cons_of_mem _ hq) hc
    · cases i with
      | zero =>
        simp only [tracksAux, List.getElem_cons_zero, List.getElem_cons_succ]
        exact ih.1 _ (List.mem_cons_self) hc
      | succ i =>
        simp only [tracksAux, List.getElem_cons_succ]
        exact ih.2 i (by omega) hc

/-- Of two items in conflict, the one placed later gets a deeper track. -/
theorem tracksInOrder_lt (c : α → α → Bool) (ps : List α) (i j : Nat) (hij : i < j)
    (hj : j < ps.length) (hc : c ps[i] ps[j] = true) :
    (tracksInOrder c ps)[i]'(by unfold tracksInOrder; rw [tracksAux_length]; omega) <
      (tracksInOrder c ps)[j]'(by unfold tracksInOrder; rw [tracksAux_length]; exact hj) :=
  (tracksAux_gt c [] ps j hj).2 i hij hc

/-- Two different items in conflict never share a track, for a symmetric conflict. -/
theorem tracksInOrder_ne (c : α → α → Bool) (hsymm : ∀ a b, c a b = c b a) (ps : List α)
    (i j : Nat) (hij : i ≠ j) (hi : i < ps.length) (hj : j < ps.length)
    (hc : c ps[i] ps[j] = true) :
    (tracksInOrder c ps)[i]'(by unfold tracksInOrder; rw [tracksAux_length]; exact hi) ≠
      (tracksInOrder c ps)[j]'(by unfold tracksInOrder; rw [tracksAux_length]; exact hj) := by
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact Nat.ne_of_lt (tracksInOrder_lt c ps i j h hj hc)
  · rw [hsymm] at hc
    exact Nat.ne_of_gt (tracksInOrder_lt c ps j i h hi hc)

end Tracks

/-- The kind of a run for the nesting order: going right or left from an end reaching up to an
end reaching down (`a` the first, `b` the second), or neither (both ends reach the same side). -/
inductive RunKind where
  /-- From an end reaching up at `a` to an end reaching down at `b > a`. -/
  | right (a b : Float)
  /-- From an end reaching up at `a` to an end reaching down at `b < a`. -/
  | left (a b : Float)
  /-- Both ends reach up (the route turns back up beside a node). -/
  | cup
  /-- Both ends reach down. -/
  | cap
  deriving Inhabited

/-- The kind of a run (see `RunKind`). -/
def RunSpec.kind (r : RunSpec) : RunKind :=
  match r.start.reach, r.finish.reach with
  | .up, .down => if r.finish.x > r.start.x then .right r.start.x r.finish.x
    else .left r.start.x r.finish.x
  | .down, .up => if r.start.x > r.finish.x then .right r.finish.x r.start.x
    else .left r.finish.x r.start.x
  | .up, .up => .cup
  | .down, .down => .cap

/-- Whether the run `p` comes before `q` in the nesting order of their direction: of two runs
going right the one with the larger `a`, then the larger `b`; mirrored for runs going left.
Runs of different kinds, and runs with equal ends, are not ordered. -/
def nestsAbove (p q : RunKind) : Bool :=
  match p, q with
  | .right a b, .right a' b' => a > a' || (a == a' && b > b')
  | .left a b, .left a' b' => a < a' || (a == a' && b < b')
  | _, _ => false

/-- A part of a run during the placement: its ends, the run it belongs to, and whether it
takes part in the nesting order (a run's part that a dogleg split off does not). -/
structure RunPart where
  /-- The ends, in the order of travel. -/
  spec : RunSpec
  /-- The run it belongs to. -/
  run : Nat
  /-- `0` for a whole run, `1` for the part from its start, `2` for the part to its finish. -/
  role : Nat := 0
  /-- Whether the part takes part in the nesting order. -/
  nested : Bool := true
  /-- The kind of the whole run, which places it in the nesting order. -/
  kind : RunKind
  /-- The stretch of the whole run, by which the nesting order compares it. -/
  nestSpan : Float × Float
  /-- The place in the nesting order of its direction, which decides between ready parts. -/
  rank : Nat
  deriving Inhabited

/-- A column free for a jog near the middle of the stretch `(lo, hi)`: a whole number at least
`tol` from every column of `cols` (sorted), the nearest such number to the middle, in the gaps
between the columns or beyond them. -/
def freeColumn (cols : Array Float) (lo hi tol : Float) : Float := Id.run do
  let mid := ((lo + hi) / 2).round
  if cols.isEmpty then return mid
  let left := ((cols.getD 0 0) - tol).floor
  let right := ((cols.getD (cols.size - 1) 0) + tol).ceil
  let mut best := if (left - mid).abs ≤ (right - mid).abs then left else right
  for i in [1:cols.size] do
    let a := (cols.getD (i - 1) 0 + tol).ceil
    let b := (cols.getD i 0 - tol).floor
    if a ≤ b then
      let p := max a (min b mid)
      if (p - mid).abs < (best - mid).abs then best := p
  return best

/-- The sorted array with `x` inserted. -/
def insertSorted (xs : Array Float) (x : Float) : Array Float := Id.run do
  let mut i := xs.size
  for j in [0:xs.size] do
    if xs.getD j 0 > x then
      i := j
      break
  return (xs.extract 0 i).push x ++ xs.extract i xs.size

/-- Whether part `p` must come before part `q` by the nesting order (both nested, `p` above
`q` in their direction's order, and overlapping within `gap`). -/
def RunPart.nestsBefore (gap : Float) (p q : RunPart) : Bool :=
  p.nested && q.nested && nestsAbove p.kind q.kind && overlaps gap p.nestSpan q.nestSpan

/-- Whether two parts leave one trunk (or join one) on its two sides: an end of each with one
owner, reaching the same side at one column, one part wholly on the left of that column and the
other wholly on the right. Such parts may share a track: the trunk forks there. -/
def RunPart.tee (p q : RunPart) : Bool :=
  [p.spec.start, p.spec.finish].any fun e => [q.spec.start, q.spec.finish].any fun f =>
    e.owner.isSome && e.owner == f.owner && e.reach == f.reach && e.x == f.x &&
      ((p.spec.span.2 ≤ e.x && e.x ≤ q.spec.span.1) || (q.spec.span.2 ≤ e.x && e.x ≤ p.spec.span.1))

/-- Whether an end of `p` reaching up and an end of `q` reaching down, of two owners, stand at
one column (closer than `laneGap`): then `p` must lie above `q`. -/
def RunPart.stacked (laneGap : Float) (p q : RunPart) : Bool :=
  [p.spec.start, p.spec.finish].any fun e => [q.spec.start, q.spec.finish].any fun f =>
    e.reach == .up && f.reach == .down && e.owner.isSome && f.owner.isSome &&
      e.owner != f.owner && (e.x - f.x).abs < laneGap

/-- Whether two parts may not share a track: their stretches overlap or come closer than `gap`
and they do not fork from one trunk (`RunPart.tee`), or one must lie above the other at a column
(`RunPart.stacked`). Symmetric (`RunPart.conflicts_comm`). -/
def RunPart.conflicts (laneGap gap : Float) (p q : RunPart) : Bool :=
  (overlaps gap p.spec.span q.spec.span && !(p.tee q || q.tee p)) ||
    (p.stacked laneGap q || q.stacked laneGap p)

theorem RunPart.conflicts_comm (laneGap gap : Float) (p q : RunPart) :
    RunPart.conflicts laneGap gap p q = RunPart.conflicts laneGap gap q p := by
  simp only [RunPart.conflicts, overlaps_comm gap p.spec.span, Bool.or_comm]

/-- The parts of a run split at the column `x`: the part with the end that reaches up (placed
first and so above) and the part with the end that reaches down, each with its role. Expects a
run whose ends reach opposite sides. -/
def splitAt (p : RunPart) (x : Float) : RunPart × RunPart :=
  let r := p.spec
  let jogDown : RunEnd := { x, reach := .down, owner := none }
  let jogUp : RunEnd := { x, reach := .up, owner := none }
  if r.start.reach == .up then
    ({ p with spec := ⟨r.start, jogDown⟩, role := 1 },
      { p with spec := ⟨jogUp, r.finish⟩, role := 2, nested := false })
  else
    ({ p with spec := ⟨jogDown, r.finish⟩, role := 2 },
      { p with spec := ⟨r.start, jogUp⟩, role := 1, nested := false })

/-- Whether the part `p` (number `k`) comes before the part `q` (number `l`) among ready parts:
by rank, then the runs going right before those going left before the others, then by number. -/
def RunPart.readyBefore (p : RunPart) (k : Nat) (q : RunPart) (l : Nat) : Bool :=
  let tag := fun (r : RunPart) => match r.kind with
    | .right _ _ => 0 | .left _ _ => 1 | .cup => 0 | .cap => 2
  p.rank < q.rank || (p.rank == q.rank && (tag p < tag q || (tag p == tag q && k < l)))

/-- The runs of a channel placed (see the module docstring): for every run, its track or its
dogleg, and the number of tracks. `laneGap` is the distance under which an end reaching up and
one reaching down count as one column, and that a jog keeps from every column; `trackGap` the
least distance between two runs on one track; `blocked` the columns of the vertical pieces that
cross the channel without a run. A run whose ends reach opposite sides at one column (an edge
that repeats a straight one) is split at once at a free column. -/
def placeRuns (runs : Array RunSpec) (laneGap trackGap : Float) (blocked : Array Float := #[]) :
    Array Placed × Nat := Id.run do
  let n := runs.size
  if n == 0 then return (#[], 0)
  -- the nesting ranks, by direction
  let kinds := runs.map (·.kind)
  let sel := fun (right : Bool) (k : RunKind) => match k with
    | .right _ _ => right
    | .left _ _ => !right
    | _ => false
  let sortBy := fun (right : Bool) =>
    ((Array.range n).filter (fun i => sel right (kinds.getD i .cup))).sortStable fun i j =>
      nestsAbove (kinds.getD i .cup) (kinds.getD j .cup)
  let mut rank : Array Nat := Array.replicate n 0
  for i in sortBy true, r in [0:n] do rank := rank.setIfInBounds i r
  for i in sortBy false, r in [0:n] do rank := rank.setIfInBounds i r
  for i in [0:n] do
    if let .cap := kinds.getD i .cup then rank := rank.setIfInBounds i n
  let mut parts : Array RunPart := (Array.range n).map fun i =>
    { spec := runs.getD i default, run := i, kind := kinds.getD i .cup,
      nestSpan := (runs.getD i default).span, rank := rank.getD i 0 }
  -- the columns of every end and every blocked column, sorted
  let mut cols : Array Float :=
    (runs.foldl (fun acc r => (acc.push r.start.x).push r.finish.x) blocked).qsort (· < ·)
  -- the parts that must be placed after each part (the second part of a split run, and the
  -- parts that wait for it at a column where they also stand)
  let mut after : Array (Array Nat) := Array.replicate n #[]
  -- runs whose ends reach opposite sides at one column are split at once
  for i in [0:n] do
    let r := runs.getD i default
    if r.start.reach != r.finish.reach && (r.start.x - r.finish.x).abs < 0.5 then
      let x := freeColumn cols r.start.x r.start.x (max laneGap trackGap)
      cols := insertSorted cols x
      let (first, second) := splitAt (parts.getD i default) x
      parts := parts.setIfInBounds i { second with nested := false }
      after := after.push #[i]
      parts := parts.push { first with nested := false }
  -- owners of ends reaching up and down, with the parts that have such an end
  let mut ups : Std.HashMap Nat (Float × Array Nat) := {}
  let mut downs : Std.HashMap Nat (Float × Array Nat) := {}
  for p in parts, k in [0:parts.size] do
    for e in [p.spec.start, p.spec.finish] do
      if let some o := e.owner then
        match e.reach with
        | .up => ups := ups.insert o ((ups.getD o (e.x, #[])).1, (ups.getD o (e.x, #[])).2.push k)
        | .down =>
          downs := downs.insert o ((downs.getD o (e.x, #[])).1, (downs.getD o (e.x, #[])).2.push k)
  -- a hub for every owner reaching up near an owner reaching down
  let upSorted := (ups.toArray.map fun (o, (x, _)) => (x, o)).qsort fun a b =>
    a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)
  let mut hubs : Array (Nat × Nat) := #[]
  for (d, (xd, _)) in downs.toArray.qsort (fun a b => a.1 < b.1) do
    -- the first owner reaching up at or after `xd - laneGap`, by bisection
    let mut lo := 0
    let mut hi := upSorted.size
    for _ in [0:64] do
      if lo ≥ hi then break
      let mid := (lo + hi) / 2
      if (upSorted.getD mid (0, 0)).1 ≤ xd - laneGap then lo := mid + 1 else hi := mid
    for j in [lo:upSorted.size] do
      let (xu, u) := upSorted.getD j (0, 0)
      if xu ≥ xd + laneGap then break
      hubs := hubs.push (u, d)
  let mut hubsOf : Std.HashMap Nat (Array Nat) := {}
  let mut hubLeft : Array Nat := Array.replicate hubs.size 0
  let mut hardIn : Array Nat := Array.replicate parts.size 0
  -- the parts that wait for each hub
  let mut hubDown : Array (Array Nat) := Array.replicate hubs.size #[]
  for (u, d) in hubs, h in [0:hubs.size] do
    hubsOf := hubsOf.insert u ((hubsOf.getD u #[]).push h)
    let upParts := (ups.getD u (0, #[])).2
    hubLeft := hubLeft.setIfInBounds h upParts.size
    -- a part with ends at both columns waits for the other parts of the upper column only
    for m in (downs.getD d (0, #[])).2 do
      if upParts.contains m then
        for q in upParts do
          if q != m then after := after.modify q (·.push m)
      else
        hardIn := hardIn.modify m (· + 1)
        hubDown := hubDown.modify h (·.push m)
  for a in after do
    for s in a do hardIn := hardIn.modify s (· + 1)
  -- the nesting order: how many parts must come before each
  let mut softIn : Array Nat := Array.replicate parts.size 0
  for q in parts, k in [0:parts.size] do
    if !q.nested then continue
    for p in parts do
      if p.nestsBefore trackGap q then softIn := softIn.modify k (· + 1)
  let mut placed : Array Bool := Array.replicate parts.size false
  let mut order : Array Nat := #[]
  let mut ready : Array Nat :=
    (Array.range parts.size).filter fun k => softIn.getD k 0 == 0 && hardIn.getD k 0 == 0
  for _ in [0:4 * parts.size + 8] do
    if order.size ≥ parts.size then break
    if ready.isEmpty then
      -- a cycle of constraints: the first unplaced nested run with nothing above it in the
      -- nesting order is split at a free column; its part with the end reaching up is ready
      let mut cand : Option Nat := none
      for p in parts, k in [0:parts.size] do
        if placed.getD k true || !p.nested || softIn.getD k 1 != 0 || p.role != 0 then continue
        match p.kind with
        | .right _ _ | .left _ _ =>
          match cand with
          | some c => if p.readyBefore k (parts.getD c default) c then cand := some k
          | none => cand := some k
        | _ => pure ()
      match cand with
      | none =>
        -- not reached when the constraints are as built above; every part left is placed
        for k in [0:parts.size] do
          if !placed.getD k true then
            placed := placed.setIfInBounds k true
            order := order.push k
        break
      | some c =>
        let p := parts.getD c default
        let (lo, hi) := p.spec.span
        let x := freeColumn cols lo hi (max laneGap trackGap)
        cols := insertSorted cols x
        let (first, second) := splitAt p x
        let s := parts.size
        parts := (parts.setIfInBounds c first).push second
        -- the second part waits for what the run waited for, and for the first part
        hardIn := (hardIn.setIfInBounds c 0).push (hardIn.getD c 0 + 1)
        softIn := softIn.push 0
        placed := placed.push false
        -- what waited for the run waits for its second part
        after := (after.map fun a => a.map fun m => if m == c then s else m).modify c (·.push s)
          |>.push #[]
        -- the end reaching down now belongs to the second part
        hubDown := hubDown.map fun a => a.map fun m => if m == c then s else m
        ready := ready.push c
    -- the ready part that comes first
    let mut bi := 0
    for i in [1:ready.size] do
      let a := ready.getD i 0
      let b := ready.getD bi 0
      if (parts.getD a default).readyBefore a (parts.getD b default) b then bi := i
    let k := ready.getD bi 0
    ready := (ready.swapIfInBounds bi (ready.size - 1)).pop
    if placed.getD k true then continue
    placed := placed.setIfInBounds k true
    order := order.push k
    let p := parts.getD k default
    let mut woken : Array Nat := #[]
    -- the hubs of its ends reaching up
    for e in [p.spec.start, p.spec.finish] do
      if let (some o, .up) := (e.owner, e.reach) then
        for h in hubsOf.getD o #[] do
          hubLeft := hubLeft.modify h (· - 1)
          if hubLeft.getD h 1 == 0 then
            for m in hubDown.getD h #[] do
              hardIn := hardIn.modify m (· - 1)
              woken := woken.push m
    for s in after.getD k #[] do
      hardIn := hardIn.modify s (· - 1)
      woken := woken.push s
    -- the parts it came before in the nesting order
    if p.nested then
      for q in parts, m in [0:parts.size] do
        if !placed.getD m true && p.nestsBefore trackGap q then
          softIn := softIn.modify m (· - 1)
          woken := woken.push m
    for m in woken do
      if !placed.getD m true && softIn.getD m 1 == 0 && hardIn.getD m 1 == 0 &&
          !ready.contains m then
        ready := ready.push m
  -- every part left (not reached when the constraints are as built) in its own order
  for k in [0:parts.size] do
    if !placed.getD k true then order := order.push k
  let tracks :=
    (tracksInOrder (RunPart.conflicts laneGap trackGap)
      (order.toList.map (parts.getD · default))).toArray
  let mut trackOf : Array Nat := Array.replicate parts.size 0
  for k in order, t in tracks do trackOf := trackOf.setIfInBounds k t
  let depth := tracks.foldl (fun m t => max m (t + 1)) 0
  -- each run's place, from its parts
  let mut startPart : Array (Option Nat) := Array.replicate n none
  let mut finishPart : Array (Option Nat) := Array.replicate n none
  let mut whole : Array (Option Nat) := Array.replicate n none
  for p in parts, k in [0:parts.size] do
    match p.role with
    | 1 => startPart := startPart.setIfInBounds p.run (some k)
    | 2 => finishPart := finishPart.setIfInBounds p.run (some k)
    | _ => whole := whole.setIfInBounds p.run (some k)
  let out := (Array.range n).map fun i =>
    match whole.getD i none, startPart.getD i none, finishPart.getD i none with
    | some k, _, _ => Placed.track (trackOf.getD k 0)
    | none, some a, some b =>
      -- the jog's column is where the two parts meet
      let pa := parts.getD a default
      let x := if pa.spec.start.owner.isNone then pa.spec.start.x else pa.spec.finish.x
      Placed.jog (trackOf.getD a 0) x (trackOf.getD b 0)
    | _, _, _ => Placed.track 0
  return (out, depth)

end PILean.Graph
