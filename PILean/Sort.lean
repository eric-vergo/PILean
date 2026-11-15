/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo (Two-Circle Solutions), Claude (Anthropic)
-/

/-!
# Sorting in `O(n log n)` comparisons whatever the input

`sortStable` is the sort the library uses. `Array.qsort` takes a quadratic number of comparisons
on an array with many equal elements (its partition puts every element equal to the pivot on
one side), and the arrays the library sorts come from its callers' data (positions of nodes,
neighbours of a node with many parallel edges, data values, colours), so a sort whose work does
not depend on the order or the repetitions of its input is part of keeping that work bounded.

## Main definitions

* `PILean.sortStable`: a stable merge sort of an array.
-/

namespace PILean

/-- The elements of `a` sorted by the strict order `lt`, equal elements in their original order
(a merge sort, `List.mergeSort`): `O(n log n)` comparisons for every input. When `lt` is a strict
total order the result is the one every correct sort gives. -/
def sortStable {α : Type} (a : Array α) (lt : α → α → Bool) : Array α :=
  (a.toList.mergeSort fun x y => !lt y x).toArray

end PILean

/-- `a.sortStable lt` is `PILean.sortStable a lt`. -/
def Array.sortStable {α : Type} (a : Array α) (lt : α → α → Bool) : Array α :=
  PILean.sortStable a lt
