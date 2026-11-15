/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# Network simplex layering

The layer assignment of Gansner, Koutsofios, North and Vo: the layers of an acyclic graph that
minimise the total span of the edges (every edge of length at least one, each edge counting
once), found by the network simplex method on a spanning tree of tight edges.

* A start (`start`, any assignment in which every edge points to a deeper layer) is turned into
  a *feasible tree* (`feasibleTree`): a spanning tree of the component whose edges are tight
  (span exactly one), by growing a tree along tight edges and, when it cannot grow, shifting it
  by the least slack of an edge that leaves it.
* The *cut value* of a tree edge is the number of edges that cross the cut it defines in its own
  direction minus those that cross against it. It is the change of the total span per unit that
  the subtree below the edge moves up; a tree edge with a negative cut value can be exchanged
  for a non-tree edge (`entering`: the edge of least slack that crosses the cut against the
  tree edge) and the total span does not grow.
* The cut values come from sums over the subtrees (`Σ out-degree - in-degree`), recomputed from
  the tree after every exchange, so no pivot depends on stale values.

Each component of the graph is solved separately and shifted so that its top layer is `0`.
The number of exchanges is bounded (`8 V + 50`): if the bound is reached, the layering found so
far, which is feasible, is returned. Ties are decided by node and edge numbers, so the result is
deterministic. Work: `O(V + E)` per exchange and `O(V E)` at most for the feasible tree.

## References

* Gansner, Koutsofios, North, Vo, *A technique for drawing directed graphs*, IEEE Transactions
  on Software Engineering 19 (1993), section 4.
-/

namespace PILean.Graph

/-- The state of the search: the spanning tree as adjacency lists of edge numbers. -/
structure SimplexWalk where
  /-- The nodes in a depth-first preorder from node `0`. -/
  order : Array Nat
  /-- The place of every node in `order`. -/
  pre : Array Nat
  /-- The number of nodes in the subtree of every node. -/
  size : Array Nat
  /-- The tree edge above every node (`noEdge` for the root). -/
  up : Array Nat
  /-- The sum over the subtree of every node of out-degree minus in-degree. -/
  net : Array Int

/-- A depth-first walk of the tree of edges `tadj` (adjacency by edge number, `tails` and `heads`
the ends of the edges, `out`/`inn` the degrees) over `m` nodes, with the subtree sums. The
walk stops after `2 m + 2` steps, so it ends even on a malformed tree. -/
def simplexWalk (m : Nat) (tadj : Array (Array Nat)) (tails heads : Array Nat)
    (deg : Array Int) : SimplexWalk := Id.run do
  let noEdge := tails.size
  let mut order : Array Nat := Array.mkEmpty m
  let mut seen : Array Bool := Array.replicate m false
  let mut up : Array Nat := Array.replicate m noEdge
  let mut stack : Array Nat := #[0]
  seen := seen.setIfInBounds 0 true
  for _ in [0:2 * m + 2] do
    match stack.back? with
    | none => break
    | some v =>
      stack := stack.pop
      order := order.push v
      for e in tadj.getD v #[] do
        let w := if tails.getD e 0 == v then heads.getD e 0 else tails.getD e 0
        if !seen.getD w true then
          seen := seen.setIfInBounds w true
          up := up.setIfInBounds w e
          stack := stack.push w
  let mut pre : Array Nat := Array.replicate m 0
  for i in [0:order.size] do
    pre := pre.setIfInBounds (order.getD i 0) i
  let mut size : Array Nat := Array.replicate m 1
  let mut net : Array Int := deg
  for k in [0:order.size] do
    let v := order.getD (order.size - 1 - k) 0
    let e := up.getD v noEdge
    if e < noEdge then
      let p := if tails.getD e 0 == v then heads.getD e 0 else tails.getD e 0
      let sv := size.getD v 0
      let nv := net.getD v 0
      size := size.modify p (· + sv)
      net := net.modify p (· + nv)
  return { order, pre, size, up, net }

/-- The layers of a connected acyclic graph of `m` nodes and the edges `tails[k] → heads[k]`
that minimise the total span, from the feasible layers `start` (every edge points to a deeper
layer). The result is shifted so that the least layer is `0`, and every edge still points to a
deeper layer. Runs at most `8 m + 50` exchanges. -/
def simplexComponent (m : Nat) (tails heads : Array Nat) (start : Array Nat) (limit : Nat := 8 * m + 50) :
    Array Nat × Nat := Id.run do
  let ne := tails.size
  let mut rank : Array Int := start.map (Int.ofNat ·)
  let mut adj : Array (Array Nat) := Array.replicate m #[]
  let mut deg : Array Int := Array.replicate m 0
  for e in [0:ne] do
    let a := tails.getD e 0
    let b := heads.getD e 0
    adj := (adj.modify a (·.push e)).modify b (·.push e)
    deg := (deg.modify a (· + 1)).modify b (· - 1)
  let slack := fun (r : Array Int) (e : Nat) =>
    r.getD (heads.getD e 0) 0 - r.getD (tails.getD e 0) 0 - 1
  -- the feasible tree
  let mut inTree : Array Bool := Array.replicate m false
  let mut tadj : Array (Array Nat) := Array.replicate m #[]
  let mut members : Array Nat := #[0]
  inTree := inTree.setIfInBounds 0 true
  let mut work : Array Nat := #[0]
  for _ in [0:m + 1] do
    -- grow along tight edges from the nodes in `work`
    for _ in [0:m * 2 + 2] do
      match work.back? with
      | none => break
      | some v =>
        work := work.pop
        for e in adj.getD v #[] do
          let w := if tails.getD e 0 == v then heads.getD e 0 else tails.getD e 0
          if !inTree.getD w true && slack rank e == 0 then
            inTree := inTree.setIfInBounds w true
            tadj := (tadj.modify v (·.push e)).modify w (·.push e)
            members := members.push w
            work := work.push w
    if members.size ≥ m then break
    -- the edges with one end in the tree, of least slack
    let mut best : Int := 0
    let mut found := false
    let mut cands : Array Nat := #[]
    for e in [0:ne] do
      let a := inTree.getD (tails.getD e 0) true
      let b := inTree.getD (heads.getD e 0) true
      if a != b then
        let s := slack rank e
        if !found || s < best then
          best := s
          found := true
          cands := #[e]
        else if s == best then cands := cands.push e
    if !found then break
    -- shift the tree so that the edges at the same end as the first are tight: down when the
    -- tree holds their upper ends
    let e0 := cands.getD 0 0
    let upper := inTree.getD (tails.getD e0 0) true
    let delta : Int := if upper then best else -best
    for v in members do rank := rank.modify v (· + delta)
    for e in cands.filter fun e => inTree.getD (tails.getD e 0) true == upper do
      let a := tails.getD e 0
      let b := heads.getD e 0
      let (v, w) := if inTree.getD a true then (a, b) else (b, a)
      if !inTree.getD w true then
        inTree := inTree.setIfInBounds w true
        tadj := (tadj.modify v (·.push e)).modify w (·.push e)
        members := members.push w
        work := work.push w
  -- exchanges
  let mut isTree : Array Bool := Array.replicate ne false
  for v in [0:m] do
    for e in tadj.getD v #[] do isTree := isTree.setIfInBounds e true
  let mut pivots := 0
  if members.size ≥ m then
    for _ in [0:limit] do
      let w := simplexWalk m tadj tails heads deg
      -- the tree edge of least (negative) cut value
      let mut leave := m
      let mut cut : Int := 0
      for v in w.order do
        let e := w.up.getD v ne
        if e < ne then
          let c := if tails.getD e 0 == v then w.net.getD v 0 else - w.net.getD v 0
          if c < cut then
            cut := c
            leave := v
      if leave == m then break
      let e := w.up.getD leave ne
      let lo := w.pre.getD leave 0
      let hi := lo + w.size.getD leave 0
      let childIsTail := tails.getD e 0 == leave
      let inSub := fun (x : Nat) => lo ≤ w.pre.getD x 0 && w.pre.getD x 0 < hi
      -- the entering edge: crosses the cut against the tree edge, least slack
      let mut enter := ne
      let mut es : Int := 0
      for f in [0:ne] do
        if !isTree.getD f true then
          let a := inSub (tails.getD f 0)
          let b := inSub (heads.getD f 0)
          if (if childIsTail then !a && b else a && !b) then
            let s := slack rank f
            if enter == ne || s < es then
              enter := f
              es := s
      if enter == ne then break
      pivots := pivots + 1
      -- the subtree moves so that the entering edge is tight
      let fa := tails.getD enter 0
      let delta : Int := if inSub fa then es else -es
      for i in [lo:hi] do
        rank := rank.modify (w.order.getD i 0) (· + delta)
      isTree := (isTree.setIfInBounds e false).setIfInBounds enter true
      let ea := tails.getD e 0
      let eb := heads.getD e 0
      tadj := ((tadj.modify ea (·.erase e)).modify eb (·.erase e))
      tadj := (tadj.modify fa (·.push enter)).modify (heads.getD enter 0) (·.push enter)
  let low := rank.foldl min (rank.getD 0 0)
  return (rank.map fun r => (r - low).toNat, pivots)

/-- The layers of the `n` nodes for the acyclic edges `es` (pairs of node numbers below `n`,
each with a larger layer for its target) from feasible layers `start`: each connected component
is solved by `simplexComponent` and put at layer `0` at its top. -/
def simplexLayers (n : Nat) (es : List (Nat × Nat)) (start : Array Nat) : Array Nat := Id.run do
  -- components by union-find with path halving
  let mut parent : Array Nat := Array.range n
  for (a, b) in es do
    if a < n && b < n then
      let mut x := a
      for _ in [0:n + 1] do
        let p := parent.getD x x
        if p == x then break
        parent := parent.setIfInBounds x (parent.getD p p)
        x := parent.getD x x
      let mut y := b
      for _ in [0:n + 1] do
        let p := parent.getD y y
        if p == y then break
        parent := parent.setIfInBounds y (parent.getD p p)
        y := parent.getD y y
      if x != y then parent := parent.setIfInBounds (max x y) (min x y)
  let mut root : Array Nat := Array.range n
  for v in [0:n] do
    let mut x := v
    for _ in [0:n + 1] do
      let p := parent.getD x x
      if p == x then break
      x := p
    root := root.setIfInBounds v x
  let mut nodes : Array (Array Nat) := Array.replicate n #[]
  for v in [0:n] do nodes := nodes.modify (root.getD v v) (·.push v)
  let mut loc : Array Nat := Array.replicate n 0
  for c in nodes do
    for i in [0:c.size] do loc := loc.setIfInBounds (c.getD i 0) i
  let mut ts : Array (Array Nat) := Array.replicate n #[]
  let mut hs : Array (Array Nat) := Array.replicate n #[]
  for (a, b) in es do
    if a < n && b < n && a != b then
      let r := root.getD a a
      ts := ts.modify r (·.push (loc.getD a 0))
      hs := hs.modify r (·.push (loc.getD b 0))
  let mut out : Array Nat := Array.replicate n 0
  for r in [0:n] do
    let c := nodes.getD r #[]
    if c.size ≥ 2 then
      let (sol, _) := simplexComponent c.size (ts.getD r #[]) (hs.getD r #[])
        (c.map fun v => start.getD v 0)
      if sol.size == c.size then
        for i in [0:c.size] do out := out.setIfInBounds (c.getD i 0) (sol.getD i 0)
      else
        for v in c do out := out.setIfInBounds v (start.getD v 0)
  return out

end PILean.Graph
