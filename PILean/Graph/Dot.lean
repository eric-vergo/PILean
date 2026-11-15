/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean.Graph.Layered

/-!
# Graphviz DOT in and out

A reader for the part of the DOT language that describes graphs to lay out, and a writer of laid
out DOT, so that a program that hands a graph to Graphviz's `dot -Tdot` can hand it to PILean
instead (`layoutDot`) and read back the positions in the same form.

**Read** (`Dot.parse`): `graph` or `digraph` (optionally `strict`, optionally named), node
statements `a [k=v, …]`, edge statements `a -> b -> c [k=v]` (or `--`), `node`, `edge` and `graph`
default attributes, graph attributes `k=v`, and `subgraph` blocks (a subgraph whose name starts
with `cluster` is a cluster, nested as written; other subgraphs only group statements). IDs are
names (letters, digits, `_`, and characters above ASCII), numerals, or double-quoted strings
with `\"` escapes (other backslashes kept, a backslash before a line break joins the lines).
Comments (`//`, `/* */`, `#` at the start of a line) are skipped. An edge's subgraph ends
(`a -> {b c}`), ports (`a:n`) and HTML strings (`<…>`) are refused with a message. The attributes
read: a node's `label`, `shape` (`box`, `rect`, `rectangle`, `square` give a box, `ellipse`,
`oval`, `circle` an ellipse; `style=rounded` a round box; anything else the default),
`fillcolor` and `color` as `#rrggbb` or `#rrggbbaa`; an edge's `label`; a cluster's `label`;
the graph's `rankdir` (`LR` for left to right). Other attributes are kept with their item so
that the writer can give them back.

The input is untrusted: it is at most `Limits.maxBytes` bytes, at most `maxItems` nodes and
edges, `maxDepth` nested blocks, `maxAttrs` attributes per item and `maxString` characters per
ID; anything beyond is an error, never a partial graph. The reader is a single pass over the
characters with an explicit stack, so its work is linear in the input.

**Write** (`Dot.write`): the graph with its laid out positions, in Graphviz's conventions: points
(1/72 inch) with the origin at the bottom left, the graph's `bb`, every node's `pos`, `width`
and `height` (inches), every edge's `pos` (cubic Bézier control points, `e,x,y` first for the
arrowhead's tip when the edge is directed) and `lp` for a label, every cluster's `bb` and `lp`;
the attributes read are written back, IDs quoted where needed.

## Main definitions

* `Dot.Limits`, `Dot.Item`, `Dot.Doc`, `Dot.parse`, `Dot.Doc.toGraph`, `Dot.write`, `layoutDot`.
-/

namespace PILean.Graph.Dot

/-- The bounds on an untrusted DOT input. -/
structure Limits where
  /-- The most bytes of input. -/
  maxBytes : Nat := 16 * 1024 * 1024
  /-- The most nodes, and the most edges. -/
  maxItems : Nat := 200000
  /-- The most nested `{ }` blocks. -/
  maxDepth : Nat := 64
  /-- The most attributes of one item. -/
  maxAttrs : Nat := 128
  /-- The most characters of one ID or attribute value. -/
  maxString : Nat := 65536
  deriving Inhabited

/-- Attributes, in the order written (a later value of a key replaces an earlier one). -/
abbrev Attrs := Array (String × String)

/-- The value of key `k`. -/
def Attrs.get? (a : Attrs) (k : String) : Option String :=
  (a.findRev? (·.1 == k)).map (·.2)

/-- `a` with `k = v` (replacing an earlier value). -/
def Attrs.set (a : Attrs) (k v : String) : Attrs :=
  (a.filter (·.1 != k)).push (k, v)

/-- A cluster read from the input. -/
structure Cluster where
  /-- The subgraph's name (`cluster…`). -/
  name : String
  /-- The enclosing cluster, by number. -/
  parent : Option Nat
  /-- Its attributes. -/
  attrs : Attrs
  deriving Inhabited

/-- What the reader returns: the nodes by first mention, their attributes, the edges, the clusters
and the graph's attributes. -/
structure Doc where
  /-- Whether the graph is a `digraph`. -/
  directed : Bool := true
  /-- Whether the graph is `strict`. -/
  strict : Bool := false
  /-- The graph's name (empty for none). -/
  name : String := ""
  /-- The graph's attributes. -/
  attrs : Attrs := #[]
  /-- The node IDs, in the order of first mention. -/
  nodes : Array String := #[]
  /-- The attributes of every node. -/
  nodeAttrs : Array Attrs := #[]
  /-- The innermost cluster every node was first declared in. -/
  nodeCluster : Array (Option Nat) := #[]
  /-- The edges: tail, head (node numbers), attributes. -/
  edges : Array (Nat × Nat × Attrs) := #[]
  /-- The clusters. -/
  clusters : Array Cluster := #[]
  deriving Inhabited

/-- A token. -/
inductive Tok where
  /-- An ID (name, numeral or quoted string), with whether it was quoted. -/
  | id (s : String) (quoted : Bool)
  /-- One of `{ } [ ] ; , = :`. -/
  | punct (c : Char)
  /-- `->` or `--`. -/
  | arrow
  deriving BEq, Inhabited, Repr

/-- Whether `c` may appear in an unquoted name. -/
def nameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c.toNat ≥ 128

/-- The tokens of the input, or an error naming the problem and its character offset. -/
def tokenize (s : String) (lim : Limits) : Except String (Array Tok) := Id.run do
  if s.utf8ByteSize > lim.maxBytes then return .error s!"input larger than {lim.maxBytes} bytes"
  let cs := s.toList.toArray
  let n := cs.size
  let mut out : Array Tok := #[]
  let mut i := 0
  let mut lineStart := true
  for _ in [0:n + 1] do
    if i ≥ n then break
    let c := cs.getD i ' '
    if c == '\n' then
      lineStart := true
      i := i + 1
    else if c == ' ' || c == '\t' || c == '\r' then i := i + 1
    else if c == '#' && lineStart then
      while i < n && cs.getD i ' ' != '\n' do i := i + 1
    else if c == '/' && cs.getD (i + 1) ' ' == '/' then
      while i < n && cs.getD i ' ' != '\n' do i := i + 1
    else if c == '/' && cs.getD (i + 1) ' ' == '*' then
      let mut j := i + 2
      let mut closed := false
      while j + 1 < n do
        if cs.getD j ' ' == '*' && cs.getD (j + 1) ' ' == '/' then
          closed := true
          break
        j := j + 1
      if !closed then return .error s!"unterminated comment at {i}"
      i := j + 2
    else
      lineStart := false
      if c == '-' && (cs.getD (i + 1) ' ' == '>' || cs.getD (i + 1) ' ' == '-') then
        out := out.push .arrow
        i := i + 2
      else if "{}[];,=:".contains c then
        out := out.push (.punct c)
        i := i + 1
      else if c == '<' then return .error s!"HTML strings are not supported (at {i})"
      else if c == '"' then
        let mut j := i + 1
        let mut acc : Array Char := #[]
        let mut closed := false
        while j < n do
          let d := cs.getD j ' '
          if d == '"' then
            closed := true
            break
          if d == '\\' && j + 1 < n then
            let e := cs.getD (j + 1) ' '
            if e == '"' then acc := acc.push '"'; j := j + 2
            else if e == '\n' then j := j + 2
            else if e == '\r' && cs.getD (j + 2) ' ' == '\n' then j := j + 3
            else acc := (acc.push '\\').push e; j := j + 2
          else
            acc := acc.push d
            j := j + 1
          if acc.size > lim.maxString then return .error s!"string longer than {lim.maxString} at {i}"
        if !closed then return .error s!"unterminated string at {i}"
        out := out.push (.id (String.ofList acc.toList) true)
        i := j + 1
      else if nameChar c || c == '-' || c == '.' then
        let mut j := i
        if c == '-' || c == '.' || c.isDigit then
          -- a numeral: [-]?(.[0-9]+ | [0-9]+(.[0-9]*)?)
          if c == '-' then j := j + 1
          while j < n && ((cs.getD j ' ').isDigit || cs.getD j ' ' == '.') do j := j + 1
          if j == i || (j == i + 1 && c == '-') then return .error s!"unexpected '-' at {i}"
        else
          while j < n && nameChar (cs.getD j ' ') do j := j + 1
        if j - i > lim.maxString then return .error s!"name longer than {lim.maxString} at {i}"
        out := out.push (.id (String.ofList (cs.extract i j).toList) false)
        i := j
      else return .error s!"unexpected character '{c}' at {i}"
  return .ok out

/-- The reader's state. -/
structure ReadState where
  /-- The document so far. -/
  doc : Doc := {}
  /-- Node numbers by ID. -/
  index : Std.HashMap String Nat := {}
  /-- The open blocks: the node and edge defaults in force and the cluster of the block. -/
  stack : Array (Attrs × Attrs × Option Nat) := #[]

/-- The node of ID `s`, added (with the defaults in force and the current cluster) if new. -/
def ReadState.node (st : ReadState) (s : String) (lim : Limits) :
    Except String (ReadState × Nat) :=
  match st.index.get? s with
  | some i => .ok (st, i)
  | none =>
    if st.doc.nodes.size ≥ lim.maxItems then .error s!"more than {lim.maxItems} nodes"
    else
      let (nd, _, cl) := st.stack.back?.getD (#[], #[], none)
      let i := st.doc.nodes.size
      .ok ({ st with index := st.index.insert s i,
                     doc := { st.doc with nodes := st.doc.nodes.push s,
                                          nodeAttrs := st.doc.nodeAttrs.push nd,
                                          nodeCluster := st.doc.nodeCluster.push cl } }, i)

/-- Reads an attribute list `[k=v, k=v; …]` (several lists may follow one another) at token `i`;
returns the attributes and the position after them. -/
def readAttrs (ts : Array Tok) (i : Nat) (lim : Limits) : Except String (Attrs × Nat) := Id.run do
  let mut i := i
  let mut out : Attrs := #[]
  for _ in [0:ts.size + 1] do
    if ts.getD i (.punct ' ') != .punct '[' then break
    i := i + 1
    for _ in [0:ts.size + 1] do
      match ts.getD i (.punct ' ') with
      | .punct ']' => i := i + 1; break
      | .punct ',' | .punct ';' => i := i + 1
      | .id k _ =>
        match ts.getD (i + 1) (.punct ' '), ts.getD (i + 2) (.punct ' ') with
        | .punct '=', .id v _ =>
          out := out.set k v
          if out.size > lim.maxAttrs then return .error s!"more than {lim.maxAttrs} attributes"
          i := i + 3
        | _, _ => return .error s!"expected '{k}=value' in an attribute list"
      | _ => return .error "malformed attribute list"
  return .ok (out, i)

/-- Reads a DOT graph (see the module docstring). -/
def parse (s : String) (lim : Limits := {}) : Except String Doc := do
  let ts ← tokenize s lim
  let mut i := 0
  let mut st : ReadState := {}
  -- header
  if ts.getD i (.punct ' ') == .id "strict" false then
    st := { st with doc := { st.doc with strict := true } }
    i := i + 1
  match ts.getD i (.punct ' ') with
  | .id "digraph" false => st := { st with doc := { st.doc with directed := true } }
  | .id "graph" false => st := { st with doc := { st.doc with directed := false } }
  | _ => throw "expected 'graph' or 'digraph'"
  i := i + 1
  if let .id nm _ := ts.getD i (.punct ' ') then
    st := { st with doc := { st.doc with name := nm } }
    i := i + 1
  if ts.getD i (.punct ' ') != .punct '{' then throw "expected '{'"
  i := i + 1
  st := { st with stack := #[(#[], #[], none)] }
  let keyword := fun (t : Tok) (k : String) => t == .id k false
  for _ in [0:ts.size + 1] do
    if st.stack.isEmpty then break
    let t := ts.getD i (.punct '$')
    match t with
    | .punct '}' =>
      st := { st with stack := st.stack.pop }
      i := i + 1
    | .punct ';' | .punct ',' => i := i + 1
    | .punct '$' => throw "unexpected end of input (a '}' is missing)"
    | .id _ _ =>
      if keyword t "subgraph" then
        let mut nm := ""
        let mut j := i + 1
        if let .id x _ := ts.getD j (.punct ' ') then
          nm := x
          j := j + 1
        if ts.getD j (.punct ' ') != .punct '{' then throw "expected '{' after 'subgraph'"
        if st.stack.size ≥ lim.maxDepth then throw s!"blocks nested more than {lim.maxDepth} deep"
        let (nd, ed, cl) := st.stack.back?.getD (#[], #[], none)
        let mut cl' := cl
        if nm.startsWith "cluster" then
          cl' := some st.doc.clusters.size
          let cs := st.doc.clusters.push (Cluster.mk nm cl #[])
          st := { st with doc := { st.doc with clusters := cs } }
        st := { st with stack := st.stack.push (nd, ed, cl') }
        i := j + 1
      else if keyword t "node" || keyword t "edge" || keyword t "graph" then
        let (a, j) ← readAttrs ts (i + 1) lim
        let (nd, ed, cl) := st.stack.back?.getD (#[], #[], none)
        if keyword t "node" then
          let nd' := a.foldl (fun x (k, v) => x.set k v) nd
          st := { st with stack := st.stack.pop.push (nd', ed, cl) }
        else if keyword t "edge" then
          let ed' := a.foldl (fun x (k, v) => x.set k v) ed
          st := { st with stack := st.stack.pop.push (nd, ed', cl) }
        else
          match cl with
          | some c =>
            let cs := st.doc.clusters.modify c fun k =>
              { k with attrs := a.foldl (fun x (k, v) => x.set k v) k.attrs }
            st := { st with doc := { st.doc with clusters := cs } }
          | none =>
            if st.stack.size == 1 then
              let ga := a.foldl (fun x (k, v) => x.set k v) st.doc.attrs
              st := { st with doc := { st.doc with attrs := ga } }
        i := j
      else
        let .id x _ := t | throw "unreachable"
        -- `k = v`: an attribute of the block
        if ts.getD (i + 1) (.punct ' ') == .punct '=' then
          let .id v _ := ts.getD (i + 2) (.punct ' ') | throw s!"expected a value after '{x}='"
          let (_, _, cl) := st.stack.back?.getD (#[], #[], none)
          match cl with
          | some c =>
            let cs := st.doc.clusters.modify c fun k => { k with attrs := k.attrs.set x v }
            st := { st with doc := { st.doc with clusters := cs } }
          | none =>
            if st.stack.size == 1 then
              let ga := st.doc.attrs.set x v
              st := { st with doc := { st.doc with attrs := ga } }
          i := i + 3
        else
          if ts.getD (i + 1) (.punct ' ') == .punct ':' then throw "ports are not supported"
          -- a node, or a chain of edges
          let mut ids : Array String := #[x]
          let mut j := i + 1
          for _ in [0:ts.size + 1] do
            if ts.getD j (.punct ' ') != .arrow then break
            match ts.getD (j + 1) (.punct ' ') with
            | .id y _ =>
              if ts.getD (j + 2) (.punct ' ') == .punct ':' then throw "ports are not supported"
              ids := ids.push y
              j := j + 2
            | .punct '{' => throw "subgraphs as edge ends are not supported"
            | _ => throw "expected a node after an edge operator"
          let (a, j') ← readAttrs ts j lim
          if ids.size == 1 then
            let (st', v) ← st.node x lim
            st := st'
            let na := st.doc.nodeAttrs.modify v fun old => a.foldl (fun o (k, w) => o.set k w) old
            st := { st with doc := { st.doc with nodeAttrs := na } }
          else
            let (_, ed, _) := st.stack.back?.getD (#[], #[], none)
            let ea := a.foldl (fun o (k, w) => o.set k w) ed
            for k in [1:ids.size] do
              let (st1, u) ← st.node (ids.getD (k - 1) "") lim
              let (st2, v) ← st1.node (ids.getD k "") lim
              st := st2
              if st.doc.edges.size ≥ lim.maxItems then throw s!"more than {lim.maxItems} edges"
              let es := st.doc.edges.push (u, v, ea)
              st := { st with doc := { st.doc with edges := es } }
          i := j'
    | .punct '{' =>
      if st.stack.size ≥ lim.maxDepth then throw s!"blocks nested more than {lim.maxDepth} deep"
      st := { st with stack := st.stack.push (st.stack.back?.getD (#[], #[], none)) }
      i := i + 1
    | _ => throw s!"unexpected token at {i}"
  if i < ts.size then throw "text after the end of the graph"
  return st.doc

/-- A colour attribute as `#rrggbb` or `#rrggbbaa`. -/
def colour? (v : Option String) : Option Rgba := v.bind Rgba.ofHex?

/-- The graph to lay out: a node per ID labelled by its `label` (its ID when it has none or the
label is Graphviz's `\N`), its shape and colours, an edge per edge with its label, a cluster per
cluster with its label (its name without `cluster` when it has none), nested as in the input. -/
def Doc.toGraph (d : Doc) : Graph :=
  let nodes := d.nodes.mapIdx fun i id =>
    let a := d.nodeAttrs.getD i #[]
    let label := match a.get? "label" with
      | some l => if l == "\\N" then id else l
      | none => id
    let rounded := (a.get? "style").any (fun s => (s.splitOn ",").any (·.trimAscii == "rounded"))
    let shape : Option NodeShape := match a.get? "shape" with
      | some "box" | some "rect" | some "rectangle" | some "square" =>
        some (if rounded then .round else .box)
      | some "ellipse" | some "oval" | some "circle" => some .ellipse
      | _ => if rounded then some .round else none
    ({ label, style := { fill := colour? (a.get? "fillcolor"), stroke := colour? (a.get? "color"),
                         shape } } : Graph.Node)
  let edges := d.edges.map fun (u, v, a) =>
    ({ src := u, dst := v, label := (a.get? "label").getD "", directed := d.directed } : Graph.Edge)
  let clusters := d.clusters.mapIdx fun c k =>
    ({ name := (k.attrs.get? "label").getD ((k.name.drop 7).toString.trimAscii.toString),
       members := (Array.range d.nodes.size).filter (d.nodeCluster.getD · none == some c),
       parent := k.parent } : Graph.Cluster)
  { nodes, edges, clusters, directed := d.directed }

/-- The options a document asks for: `rankdir=LR` gives left to right. -/
def Doc.options (d : Doc) : LayeredOptions :=
  if (d.attrs.get? "rankdir").any (· == "LR") then { direction := .leftToRight } else {}

/-- An ID as DOT writes it: bare when it is a name or a numeral that is not a keyword, quoted
otherwise (with `"` and line breaks escaped, other backslashes kept). -/
def quote (s : String) : String :=
  let keywords := ["graph", "digraph", "subgraph", "node", "edge", "strict"]
  let plain := !s.isEmpty && s.all nameChar && !s.front.isDigit &&
    !keywords.contains s.toLower
  let numeral := !s.isEmpty && s.all (fun c => c.isDigit || c == '.') && (s.splitOn ".").length ≤ 2
  if plain || numeral then s
  else
    -- backslashes stay as they are (DOT reads them so), except one at the very end, which
    -- would escape the closing quote
    let body := String.join (s.toList.map fun c =>
      if c == '"' then "\\\"" else if c == '\n' then "\\n" else c.toString)
    "\"" ++ body ++ (if s.endsWith "\\" then "\\" else "") ++ "\""

/-- A number of points with at most two decimals. -/
def num (f : Float) : String :=
  let r := (f * 100).round / 100
  if r == r.round then toString r.round.toInt64 else
    let s := toString r
    -- `toString` gives six decimals; drop the trailing zeros
    (s.toList.reverse.dropWhile (· == '0')).reverse |> String.ofList

/-- A length in pixels as inches with at most four decimals. -/
def inches (f : Float) : String :=
  let r := (f / 72 * 10000).round
  let whole := (r / 10000).floor
  let frac := (r - whole * 10000).toUInt64.toNat
  let digits := ((toString (frac + 10000)).drop 1).toString
  let digits := (digits.toList.reverse.dropWhile (· == '0')).reverse
  s!"{whole.toUInt64}" ++ (if digits.isEmpty then "" else "." ++ String.ofList digits)

/-- Attributes as DOT writes them. -/
def attrText (a : Attrs) : String :=
  if a.isEmpty then "" else
    " [" ++ ", ".intercalate (a.toList.map fun (k, v) => s!"{quote k}={quote v}") ++ "]"

/-- The control points of a path as cubic pieces (lines become cubics), the first point first. -/
def cubicPoints (p : Path) : Array Point := Id.run do
  let mut out : Array Point := #[]
  let mut cur : Point := ⟨0, 0⟩
  for c in p.cmds do
    match c with
    | .move q => if out.isEmpty then out := out.push q
                 cur := q
    | .line q =>
      out := out ++ #[⟨cur.x + (q.x - cur.x) / 3, cur.y + (q.y - cur.y) / 3⟩,
        ⟨cur.x + 2 * (q.x - cur.x) / 3, cur.y + 2 * (q.y - cur.y) / 3⟩, q]
      cur := q
    | .quad k q =>
      out := out ++ #[⟨cur.x + 2 * (k.x - cur.x) / 3, cur.y + 2 * (k.y - cur.y) / 3⟩,
        ⟨q.x + 2 * (k.x - q.x) / 3, q.y + 2 * (k.y - q.y) / 3⟩, q]
      cur := q
    | .cubic a b q =>
      out := out ++ #[a, b, q]
      cur := q
    | .close => pure ()
  return out

/-- The laid out DOT of a document and the layout of its graph (`l`, with the size of the
picture): see the module docstring. Coordinates are points with the origin at the bottom left. -/
def write (d : Doc) (l : Layout) : String := Id.run do
  let h := l.height
  let pt := fun (p : Point) => s!"{num p.x},{num (h - p.y)}"
  let box := fun (b : Box) => s!"{num b.x0},{num (h - b.y1)},{num b.x1},{num (h - b.y0)}"
  let kw := if d.directed then "digraph" else "graph"
  let op := if d.directed then "->" else "--"
  let mut out := (if d.strict then "strict " else "") ++ kw ++
    (if d.name.isEmpty then "" else " " ++ quote d.name) ++ " {\n"
  let ga := d.attrs.set "bb" s!"0,0,{num l.width},{num h}"
  out := out ++ "  graph" ++ attrText ga ++ ";\n"
  -- clusters as nested subgraphs, each with the nodes declared in it
  let nodeLine := fun (i : Nat) =>
    let id := d.nodes.getD i ""
    let a := d.nodeAttrs.getD i #[]
    match l.nodes[i]? with
    | some nb =>
      let c : Point := ⟨(nb.box.x0 + nb.box.x1) / 2, (nb.box.y0 + nb.box.y1) / 2⟩
      let a := ((a.set "pos" (pt c)).set "width" (inches nb.box.width)).set "height"
        (inches nb.box.height)
      s!"{quote id}{attrText a};\n"
    | none => s!"{quote id}{attrText a};\n"
  let k := d.clusters.size
  let rec block (fuel c : Nat) (indent : String) : String :=
    match fuel with
    | 0 => ""
    | f + 1 =>
      let cl := d.clusters.getD c default
      let a := match l.clusters.find? (·.index == c) with
        | some cb => (cl.attrs.set "bb" (box cb.box)).set "lp"
            (pt ⟨cb.box.x0 + 12 + 30, cb.box.y0 + 16⟩)
        | none => cl.attrs
      let own := (Array.range d.nodes.size).filter (d.nodeCluster.getD · none == some c)
      let kids := (Array.range k).filter fun j => (d.clusters.getD j default).parent == some c
      indent ++ s!"subgraph {quote cl.name} \{\n" ++ indent ++ "  graph" ++ attrText a ++ ";\n" ++
        String.join (own.toList.map fun i => indent ++ "  " ++ nodeLine i) ++
        String.join (kids.toList.map fun j => block f j (indent ++ "  ")) ++ indent ++ "}\n"
  for c in [0:k] do
    if (d.clusters.getD c default).parent.isNone then out := out ++ block (k + 1) c "  "
  for i in [0:d.nodes.size] do
    if (d.nodeCluster.getD i none).isNone then out := out ++ "  " ++ nodeLine i
  for j in [0:d.edges.size] do
    let (u, v, a) := d.edges.getD j (0, 0, #[])
    let a := match l.edges.find? (·.index == j) with
      | some e =>
        let cps := cubicPoints e.path
        let tip := e.head.bind fun hd => (hd.cmds.findSome? fun c => match c with
          | .move q => some q | _ => none)
        let posText := (match tip, d.directed with
          | some tp, true => s!"e,{pt tp} "
          | _, _ => "") ++ " ".intercalate (cps.toList.map pt)
        let a := a.set "pos" posText
        match e.label with
        | some lb => a.set "lp" (pt ⟨(lb.box.x0 + lb.box.x1) / 2, (lb.box.y0 + lb.box.y1) / 2⟩)
        | none => a
      | none => a
    out := out ++ s!"  {quote (d.nodes.getD u "")} {op} {quote (d.nodes.getD v "")}{attrText a};\n"
  return out ++ "}\n"

end PILean.Graph.Dot

namespace PILean.Graph

/-- Lays out a DOT graph: reads it (`Dot.parse`, with `lim`), lays out its graph with PILean's
layered layout (`Graph.layout`, the options the document asks for and `st`), and writes the laid
out DOT (`Dot.write`), or the reader's error. -/
def layoutDot (input : String) (st : Style := {}) (lim : Dot.Limits := {}) :
    Except String String := do
  let d ← Dot.parse input lim
  let g := d.toGraph
  return Dot.write d (g.layout d.options st)

end PILean.Graph
