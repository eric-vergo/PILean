/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/
import PILean

/-!
# `pilean-probe`

`pilean-probe png|gif|apng|zlib FILE` decodes the file with the reader's default limits (zlib:
an output cap of 256 MiB) and prints `ok` with the size of what was decoded, or `error` with the
reason. The test driver runs it on hostile inputs under limits (`PILeanTest.Bounds`); it imports
only the library, so what it costs is what the reader costs.
-/

open PILean

/-- A hostile graph of the given kind and size: `fan` (a chain with an edge from its first node
to every other, so edges span up to `n` layers), `dense` (every pair `i < j`), `loops` (`n` nodes
with ten self-loops each), `multi` (`n` parallel edges and `n` reversed ones between two nodes),
`sparse` (`n` nodes, `2 n` pseudo-random edges). -/
def hostileGraph (kind : String) (n : Nat) : Graph := Id.run do
  let mut es : Array (Nat × Nat) := #[]
  match kind with
  | "fan" =>
    for i in [1:n] do es := es.push (i - 1, i) |>.push (0, i)
  | "dense" =>
    for i in [0:n] do
      for j in [i + 1:n] do es := es.push (i, j)
  | "loops" =>
    for i in [0:n] do
      for _ in [0:10] do es := es.push (i, i)
  | "multi" =>
    for _ in [0:n] do es := es.push (0, 1) |>.push (1, 0)
  | _ =>
    let mut s : Nat := 12345
    for _ in [0:2 * n] do
      s := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
      let a := (s >>> 33) % n
      s := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
      let b := (s >>> 33) % n
      es := es.push (a, b)
  let g := Graph.ofPairs es.toList
  return if g.nodes.size < n then { g with nodes := g.nodes ++
    (Array.replicate (n - g.nodes.size) ({ label := "x" } : Graph.Node)) } else g

/-- Decodes the file named by the second argument as the first says, or with `graph KIND N`
lays out and draws a hostile graph (`hostileGraph`) and prints its size. -/
def main (args : List String) : IO UInt32 := do
  if let "graph" :: kind :: n :: rest := args then
    let g := hostileGraph kind n.toNat!
    let o : Graph.LayeredOptions := match rest with
      | [sw, cw] => { sweeps := sw.toNat!, coordinateWork := cw.toNat! }
      | _ => {}
    let l := Graph.layout g o
    IO.println s!"ok {l.nodes.size} nodes {l.edges.size} routes {l.width}x{l.height}"
    return 0
  let [kind, file] := args | do
    IO.eprintln "usage: pilean-probe png|gif|apng|zlib FILE"
    return 2
  let bytes ← IO.FS.readBinFile file
  let line := match kind with
    | "png" => match Png.decode bytes with
      | .ok d => s!"ok {d.image.width}x{d.image.height} {d.image.data.size}"
      | .error e => s!"error {e}"
    | "gif" => match Anim.readGif bytes with
      | .ok s => s!"ok {s.width}x{s.height} frames {s.frames.size}"
      | .error e => s!"error {repr e}"
    | "apng" => match Anim.readApng bytes with
      | .ok s => s!"ok {s.width}x{s.height} frames {s.frames.size}"
      | .error e => s!"error {repr e}"
    | _ => match Png.zlibDecompress bytes (1 <<< 28) with
      | .ok o => s!"ok {o.size}"
      | .error e => s!"error {e}"
  IO.println line
  return 0
