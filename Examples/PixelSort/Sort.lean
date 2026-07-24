/-!
# Verified pixel sort — the algorithm

One bubble pass over a keyed list, formulated for clean structural
recursion: `pass` hands the current element to `go`, which walks the rest
of the list swapping adjacent out-of-order pairs. `passes k` iterates.

**This is the exact function the animation renders** — each GIF frame is
one application of `pass` to every pixel column — and the exact function
`Examples.PixelSort.Proofs` proves theorems about. No parallel
implementation exists; the proof and the pixels share this code.

Keys are `Nat` (the pixel's luma); payloads `α` ride along untouched.
-/

namespace Examples.PixelSort

/-- Walk the list with `cur` in hand: emit the smaller of `cur` and the
next element, keep the larger in hand. One rightward bubble sweep. -/
def go (cur : Nat × α) : List (Nat × α) → List (Nat × α)
  | [] => [cur]
  | b :: rest =>
    if cur.1 ≤ b.1 then cur :: go b rest else b :: go cur rest

/-- One bubble pass: adjacent out-of-order pairs swap; a maximal element
reaches the end (`Proofs.pass_max_split`). -/
def pass : List (Nat × α) → List (Nat × α)
  | [] => []
  | a :: rest => go a rest

/-- `k` bubble passes. `passes l.length l` is fully sorted
(`Proofs.sorted_passes`). -/
def passes : Nat → List (Nat × α) → List (Nat × α)
  | 0, l => l
  | k + 1, l => passes k (pass l)

/-- Sorted by key (non-decreasing luma). -/
def SortedKeys (l : List (Nat × α)) : Prop :=
  l.Pairwise (fun a b => a.1 ≤ b.1)

end Examples.PixelSort
