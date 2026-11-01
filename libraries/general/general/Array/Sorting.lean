import general.Array.Aggregation

namespace Array

/-! ### Flatten and sort — flatten an array of lists and sort by a relation -/

/-- Flatten an array of lists (by folding `++`) and sort the result by the given relation.
This is the composition of concatenating all inner lists and then applying `insertionSort`. -/
def flattenThenSort (r : α → α → Prop) [DecidableRel r] (lists : Array (List α)) : List α :=
  (lists.foldl (fun acc lst => acc ++ lst) []).insertionSort r

/-- The result of `flattenThenSort` is `List.Sorted r` for any total, transitive relation `r`. -/
lemma flattenThenSort_sorted (r : α → α → Prop) [DecidableRel r] [IsTotal α r] [IsTrans α r]
    (lists : Array (List α)) :
    List.Sorted r (flattenThenSort r lists) := by
  unfold flattenThenSort
  exact List.sorted_insertionSort r (lists.foldl (fun acc lst => acc ++ lst) [])

/-! ### Sort array via `List.mergeSort` — array wrapper for merge sort -/

/-- Sort an array using `List.mergeSort` with a custom comparison function `le : α → α → Bool`.
Returns a new `Array α` with elements reordered according to the total preorder induced by `le`.
This is a general helper, not tied to any specific precondition.
For sorting with the standard `≤` order on a `LinearOrder α`, use
`Array.mergeSort arr (fun a b => decide (a ≤ b))`. -/
def mergeSortArray {α : Type} (arr : Array α) (le : α → α → Bool) : Array α :=
  (List.mergeSort arr.toList le).toArray

end Array
