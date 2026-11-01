import Mathlib.Data.List.Sort

namespace Specific

open _root_.List

namespace List

/-! ## Sorting by descending `Nat` score -/

/-- Sort a list by descending `Nat` score. -/
def sortByDescending {α : Type} (score : α → Nat) (l : List α) : List α :=
  insertionSort (fun a b : α => score b ≤ score a) l

/-- Sort a list of natural numbers in descending order. -/
def sortDesc (l : List Nat) : List Nat :=
  sortByDescending id l

/-- The result of `sortByDescending` is sorted by the descending score. -/
theorem sortByDescending_sorted {α : Type} (score : α → Nat) (l : List α) :
    Sorted (fun a b : α => score b ≤ score a) (sortByDescending score l) := by
  let rel : α → α → Prop := fun a b => score b ≤ score a
  haveI : IsTotal α rel := ⟨fun a b => Nat.le_total (score b) (score a)⟩
  haveI : IsTrans α rel := ⟨fun _ _ _ hab hbc => Nat.le_trans hbc hab⟩
  simpa [sortByDescending] using
    sorted_insertionSort rel l

/-- Membership is preserved by `sortByDescending`. -/
theorem mem_sortByDescending_of_mem {α : Type} (score : α → Nat) {x : α} {l : List α}
    (h : x ∈ l) : x ∈ sortByDescending score l := by
  simpa [sortByDescending] using
    ((mem_insertionSort (fun a b : α => score b ≤ score a)).2 h)

/-- `sortByDescending` preserves list length. -/
theorem length_sortByDescending {α : Type} (score : α → Nat) (l : List α) :
    (sortByDescending score l).length = l.length := by
  simp [sortByDescending]

/-- In a sorted list, the score of any element is ≤ the score of the head. -/
theorem score_le_head_score_of_mem_sorted_desc {α : Type} {score : α → Nat}
    {head x : α} {tail : List α}
    (hSorted : Sorted (fun a b : α => score b ≤ score a) (head :: tail))
    (hMem : x ∈ head :: tail) : score x ≤ score head := by
  cases hMem with
  | head => exact Nat.le_refl (score head)
  | tail _ hTail => exact rel_of_sorted_cons hSorted x hTail

/-! ## Sorting by a relation `r` using merge sort -/

/-- Sort a list by a relation `r`, using merge sort. -/
def sortByRel {α : Type u} (r : α → α → Prop) [DecidableRel r] (xs : List α) : List α :=
  xs.mergeSort (fun x y => decide (r x y))

end List

end Specific
