/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# Network simplex

The network simplex method of Gansner, Koutsofios, North and Vo for ranking the nodes of a
directed graph: integer ranks in which every edge `u → v` is at least `minlen` long
(`rank v - rank u ≥ minlen`) and the total weighted length is least. With length `1` and weight
`1` this is the layer assignment that minimises the total span of the edges (`simplexLayers`);
with other lengths and weights it assigns coordinates (`simplexBreadth` in
`PILean.Graph.Coordinates`). The graph need not be connected (`simplexSolve` solves each
component), and the start must be feasible.

* A start is turned into a *feasible tree* (`simplexComponent`): a spanning tree of tight edges
  (edges of exactly their least length). The tight edges give a forest; its components are
  joined smallest first, each moved by the least slack of an edge that leaves it, so that a node
  moves `O(log V)` times.
* The *cut value* of a tree edge is the weight of the edges that cross the cut it defines in its
  own direction minus those that cross against it. A tree edge with a negative cut value can be
  exchanged for the non-tree edge of least slack that crosses the cut against it, and the total
  weighted length does not grow; the edge of the most negative cut value leaves.
* The cut values come from sums over the subtrees (`simplexWalk`) once, and are then updated
  along the cycle of each exchange by the rule of the paper. The smaller side of the cut is
  searched for the entering edge and moved.

The number of exchanges is bounded (`rounds V + 50`, and by a budget of work): when a bound is
reached, the ranks found so far, which are feasible and no worse than the start, are returned.
Each component is shifted so that its least rank is `0`. Ties are decided by node and edge
numbers, so the result is deterministic. Work: `O(E log V)` for the feasible tree and `O(V + E)`
per exchange at worst, usually the smaller side of a cut.

## References

* Gansner, Koutsofios, North, Vo, *A technique for drawing directed graphs*, IEEE Transactions
  on Software Engineering 19 (1993), sections 2.3 and 4.
-/

namespace PILean.Graph

/-- What a walk of the tree finds. -/
structure SimplexWalk where
  /-- The nodes in a depth-first preorder from node `0`. -/
  order : Array Nat
  /-- The tree edge above every node (the number of edges for the root). -/
  up : Array Nat
  /-- The sum over the subtree of every node of the weight of the edges out of a node minus
  the weight of those into it. -/
  net : Array Int

/-- A depth-first walk of the tree of edges `tadj` (adjacency by edge number, `tails` and `heads`
the ends of the edges, `deg` the weighted out-degree minus in-degree of every node) over `m`
nodes, with the subtree sums. The walk stops after `2 m + 2` steps, so it ends even on a
malformed tree. -/
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
  let mut net : Array Int := deg
  for k in [0:order.size] do
    let v := order.getD (order.size - 1 - k) 0
    let e := up.getD v noEdge
    if e < noEdge then
      let p := if tails.getD e 0 == v then heads.getD e 0 else tails.getD e 0
      let nv := net.getD v 0
      net := net.modify p (· + nv)
  return { order, up, net }

/-- Inserts `x` into the binary min-heap `h`. -/
def heapPush (h : Array Nat) (x : Nat) : Array Nat := Id.run do
  let mut h := h.push x
  let mut i := h.size - 1
  for _ in [0:h.size] do
    if i == 0 then break
    let p := (i - 1) / 2
    if h.getD p 0 > h.getD i 0 then
      h := h.swapIfInBounds p i
      i := p
    else break
  return h

/-- The least element of the binary min-heap `h` and the heap without it. -/
def heapPop (h : Array Nat) : Option Nat × Array Nat := Id.run do
  match h.back? with
  | none => return (none, h)
  | some last =>
    let top := h.getD 0 0
    let mut h := h.pop
    if h.isEmpty then return (some top, h)
    h := h.setIfInBounds 0 last
    let mut i := 0
    for _ in [0:h.size + 1] do
      let l := 2 * i + 1
      let r := l + 1
      let mut m := i
      if l < h.size && h.getD l 0 < h.getD m 0 then m := l
      if r < h.size && h.getD r 0 < h.getD m 0 then m := r
      if m == i then break
      h := h.swapIfInBounds i m
      i := m
    return (some top, h)

/-- The ranks of a connected graph of `m` nodes and the edges `tails[k] → heads[k]` (each of
length at least `minlen[k]`, and weight `weight[k] ≥ 0`) that minimise the total weighted length,
from feasible ranks `start`, and the number of exchanges made. The result is shifted so that the
least rank is `0`, and every edge still has its length. Runs at most `rounds m + 50` exchanges,
and at most `budget / (m + e) + 1` where `e` is the number of
edges (each exchange costs `O(m + e)` at worst, usually the smaller side of a cut). -/
def simplexComponent (m : Nat) (tails heads : Array Nat) (minlen weight : Array Int)
    (start : Array Int) (rounds : Nat := 8) (budget : Nat := 1000000000000) : Array Int × Nat :=
  Id.run do
  let ne := tails.size
  let mut rank : Array Int := start
  let mut adj : Array (Array Nat) := Array.replicate m #[]
  let mut deg : Array Int := Array.replicate m 0
  for e in [0:ne] do
    let a := tails.getD e 0
    let b := heads.getD e 0
    let w := weight.getD e 0
    adj := (adj.modify a (·.push e)).modify b (·.push e)
    deg := (deg.modify a (· + w)).modify b (· - w)
  let slack := fun (r : Array Int) (e : Nat) =>
    r.getD (heads.getD e 0) 0 - r.getD (tails.getD e 0) 0 - minlen.getD e 0
  -- the feasible tree: the tight edges form a forest; its components are joined smallest first,
  -- each moved by the least slack of an edge that leaves it (so every node moves `O(log m)`
  -- times)
  let mut isTree : Array Bool := Array.replicate ne false
  let mut tadj : Array (Array Nat) := Array.replicate m #[]
  let mut comp : Array Nat := Array.replicate m m
  let mut cmem : Array (Array Nat) := Array.replicate m #[]
  let mut heap : Array Nat := #[]
  for r in [0:m] do
    if comp.getD r m == m then
      comp := comp.setIfInBounds r r
      let mut mem : Array Nat := #[r]
      let mut stack : Array Nat := #[r]
      for _ in [0:m + 1] do
        match stack.back? with
        | none => break
        | some v =>
          stack := stack.pop
          for e in adj.getD v #[] do
            let w := if tails.getD e 0 == v then heads.getD e 0 else tails.getD e 0
            if comp.getD w m == m && slack rank e == 0 then
              comp := comp.setIfInBounds w r
              isTree := isTree.setIfInBounds e true
              tadj := (tadj.modify v (·.push e)).modify w (·.push e)
              mem := mem.push w
              stack := stack.push w
      heap := heapPush heap (mem.size * (m + 1) + r)
      cmem := cmem.setIfInBounds r mem
  let mut left := (Array.range m).foldl (fun c r => if comp.getD r m == r then c + 1 else c) 0
  let mut connected := true
  for _ in [0:2 * m + 2] do
    if left ≤ 1 then break
    let (top, h') := heapPop heap
    heap := h'
    match top with
    | none => connected := false; break
    | some key =>
      let c := key % (m + 1)
      let cm := cmem.getD c #[]
      if cm.size * (m + 1) + c == key && !cm.isEmpty then
        -- the edge of least slack that leaves the component
        let mut bestE := ne
        let mut bestS : Int := 0
        for x in cm do
          for g in adj.getD x #[] do
            let y := if tails.getD g 0 == x then heads.getD g 0 else tails.getD g 0
            if comp.getD y m != c then
              let sl := slack rank g
              if bestE == ne || sl < bestS || (sl == bestS && g < bestE) then
                bestE := g
                bestS := sl
        if bestE == ne then
          connected := false
          break
        let g := bestE
        let ownsTail := comp.getD (tails.getD g 0) m == c
        let delta : Int := if ownsTail then bestS else -bestS
        for x in cm do rank := rank.modify x (· + delta)
        let a := tails.getD g 0
        let b := heads.getD g 0
        let d := comp.getD (if ownsTail then b else a) m
        isTree := isTree.setIfInBounds g true
        tadj := (tadj.modify a (·.push g)).modify b (·.push g)
        cmem := cmem.setIfInBounds c #[]
        for x in cm do comp := comp.setIfInBounds x d
        let merged := (cmem.getD d #[]) ++ cm
        cmem := cmem.setIfInBounds d merged
        heap := heapPush heap (merged.size * (m + 1) + d)
        left := left - 1
  -- exchanges
  let mut pivots := 0
  if connected && left ≤ 1 then
    -- the rooted tree, parent edges and cut values
    let w0 := simplexWalk m tadj tails heads deg
    let mut pe : Array Nat := w0.up
    let mut cutv : Array Int := Array.replicate ne 0
    for v in [0:m] do
      let e := pe.getD v ne
      if e < ne then
        cutv := cutv.setIfInBounds e
          (if tails.getD e 0 == v then w0.net.getD v 0 else - w0.net.getD v 0)
    let other := fun (e x : Nat) => if tails.getD e 0 == x then heads.getD e 0 else tails.getD e 0
    -- the tree edges that may have a negative cut value
    let mut inNeg : Array Bool := Array.replicate ne false
    let mut neg : Array Nat := #[]
    for e in [0:ne] do
      if isTree.getD e false && cutv.getD e 0 < 0 then
        neg := neg.push e
        inNeg := inNeg.setIfInBounds e true
    let mut mk : Array Nat := Array.replicate m 0
    let mut anc : Array Nat := Array.replicate m 0
    for step in [0:min (rounds * m + 50) (budget / (m + ne) + 1)] do
      -- the tree edge of least (negative) cut value, among the candidates
      let mut leave := ne
      let mut cut : Int := 0
      let mut kept : Array Nat := #[]
      for e in neg do
        if isTree.getD e false && cutv.getD e 0 < 0 then
          kept := kept.push e
          if cutv.getD e 0 < cut || (cutv.getD e 0 == cut && e < leave) then
            leave := e
            cut := cutv.getD e 0
        else inNeg := inNeg.setIfInBounds e false
      neg := kept
      if leave == ne then break
      let e := leave
      let ea := tails.getD e 0
      let eb := heads.getD e 0
      let child := if pe.getD eb ne == e then eb else ea
      let par := other e child
      -- the two sides of the cut, searched alternately until one is complete
      let stamp := step + 1
      let cm := 2 * stamp
      let pm := 2 * stamp + 1
      mk := (mk.setIfInBounds child cm).setIfInBounds par pm
      let mut ca : Array Nat := #[child]
      let mut cs : Array Nat := #[child]
      let mut pa : Array Nat := #[par]
      let mut ps : Array Nat := #[par]
      for _ in [0:m + 1] do
        if cs.isEmpty || ps.isEmpty then break
        match cs.back? with
        | none => pure ()
        | some x =>
          cs := cs.pop
          for g in tadj.getD x #[] do
            if g != e then
              let y := other g x
              if mk.getD y 0 != cm then
                mk := mk.setIfInBounds y cm
                cs := cs.push y
                ca := ca.push y
        match ps.back? with
        | none => pure ()
        | some x =>
          ps := ps.pop
          for g in tadj.getD x #[] do
            if g != e then
              let y := other g x
              if mk.getD y 0 != pm then
                mk := mk.setIfInBounds y pm
                ps := ps.push y
                pa := pa.push y
      let smallIsChild := cs.isEmpty
      let small := if smallIsChild then ca else pa
      let sm := if smallIsChild then cm else pm
      -- the entering edge: crosses the cut against the tree edge, least slack
      let smallIsTail := mk.getD ea 0 == sm
      let mut enter := ne
      let mut es : Int := 0
      for x in small do
        for g in adj.getD x #[] do
          if !isTree.getD g true then
            let y := other g x
            let towards := if smallIsTail then heads.getD g 0 == x else tails.getD g 0 == x
            if mk.getD y 0 != sm && towards then
              let s := slack rank g
              if enter == ne || s < es || (s == es && g < enter) then
                enter := g
                es := s
      if enter == ne then break
      pivots := pivots + 1
      let f := enter
      let fa := tails.getD f 0
      let fb := heads.getD f 0
      -- the smaller side moves so that the entering edge is tight
      let delta : Int := if mk.getD fa 0 == sm then es else -es
      for x in small do rank := rank.modify x (· + delta)
      -- cut values along the cycle
      anc := (anc.setIfInBounds fa cm).setIfInBounds fb pm
      let mut x := fa
      let mut z := fb
      let mut lca := ne + m
      for _ in [0:m + 1] do
        let gx := pe.getD x ne
        if gx < ne then
          x := other gx x
          if anc.getD x 0 == pm then
            lca := x
            break
          anc := anc.setIfInBounds x cm
        let gz := pe.getD z ne
        if gz < ne then
          z := other gz z
          if anc.getD z 0 == cm then
            lca := z
            break
          anc := anc.setIfInBounds z pm
        if gx == ne && gz == ne then break
      let mut y := fa
      for _ in [0:m + 1] do
        if y == lca then break
        let g := pe.getD y ne
        if g == ne then break
        cutv := cutv.modify g (if tails.getD g 0 == y then (· + cut) else (· - cut))
        if cutv.getD g 0 < 0 && !inNeg.getD g true then
          inNeg := inNeg.setIfInBounds g true
          neg := neg.push g
        y := other g y
      y := fb
      for _ in [0:m + 1] do
        if y == lca then break
        let g := pe.getD y ne
        if g == ne then break
        cutv := cutv.modify g (if tails.getD g 0 == y then (· - cut) else (· + cut))
        if cutv.getD g 0 < 0 && !inNeg.getD g true then
          inNeg := inNeg.setIfInBounds g true
          neg := neg.push g
        y := other g y
      cutv := (cutv.setIfInBounds f (- cut)).setIfInBounds e 0
      -- the child side hangs from the other end of the entering edge, re-rooted
      let inChildSide := fun (z : Nat) => (mk.getD z 0 == sm) == smallIsChild
      let sEnd := if inChildSide fa then fa else fb
      let mut cur := sEnd
      let mut newPe := f
      for _ in [0:m + 1] do
        let old := pe.getD cur ne
        pe := pe.setIfInBounds cur newPe
        if cur == child then break
        newPe := old
        cur := other old cur
      isTree := (isTree.setIfInBounds e false).setIfInBounds f true
      tadj := ((tadj.modify ea (·.erase e)).modify eb (·.erase e))
      tadj := (tadj.modify fa (·.push f)).modify fb (·.push f)
  let low := rank.foldl min (rank.getD 0 0)
  return (rank.map (· - low), pivots)

/-- The ranks of `n` nodes for the edges `tails[k] → heads[k]` (node numbers below `n`) of length
at least `minlen[k]` and weight `weight[k]`, from feasible ranks `start`, minimising the total
weighted length: each connected component is solved by `simplexComponent` and put at rank `0` at
its least. Nodes without edges get `0`. Returns the ranks and the largest number of exchanges
made in one component. -/
def simplexSolve (n : Nat) (tails heads : Array Nat) (minlen weight : Array Int)
    (start : Array Int) (rounds : Nat := 8) (budget : Nat := 1000000000000) : Array Int × Nat :=
  Id.run do
  -- components by union-find with path halving
  let mut parent : Array Nat := Array.range n
  for k in [0:tails.size] do
    let a := tails.getD k 0
    let b := heads.getD k 0
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
  let mut ls : Array (Array Int) := Array.replicate n #[]
  let mut ws : Array (Array Int) := Array.replicate n #[]
  for k in [0:tails.size] do
    let a := tails.getD k 0
    let b := heads.getD k 0
    if a < n && b < n && a != b then
      let r := root.getD a a
      ts := ts.modify r (·.push (loc.getD a 0))
      hs := hs.modify r (·.push (loc.getD b 0))
      ls := ls.modify r (·.push (minlen.getD k 0))
      ws := ws.modify r (·.push (weight.getD k 0))
  let mut out : Array Int := Array.replicate n 0
  let mut most := 0
  for r in [0:n] do
    let c := nodes.getD r #[]
    if c.size ≥ 2 then
      let (sol, pivots) := simplexComponent c.size (ts.getD r #[]) (hs.getD r #[])
        (ls.getD r #[]) (ws.getD r #[]) (c.map fun v => start.getD v 0) rounds budget
      most := max most pivots
      if sol.size == c.size then
        for i in [0:c.size] do out := out.setIfInBounds (c.getD i 0) (sol.getD i 0)
      else
        for v in c do out := out.setIfInBounds v (start.getD v 0)
  return (out, most)

/-- The layers of the `n` nodes for the acyclic edges `es` (pairs of node numbers below `n`,
each with a larger layer for its target) from feasible layers `start`: the total span of the
edges is minimal (`simplexSolve` with length `1` and weight `1`), each component with its top at
layer `0`. -/
def simplexLayers (n : Nat) (es : List (Nat × Nat)) (start : Array Nat) : Array Nat :=
  let ea := es.toArray
  (simplexSolve n (ea.map (·.1)) (ea.map (·.2)) (Array.replicate ea.size 1)
    (Array.replicate ea.size 1) (start.map (Int.ofNat ·))).1.map (·.toNat)

end PILean.Graph
