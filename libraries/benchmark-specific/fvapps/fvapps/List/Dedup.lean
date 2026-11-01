import Mathlib.Data.List.Dedup

namespace Specific

open _root_.List

namespace List

/-! ## `dedupFromRight` and `dedupKeepingLast`

These are variants of `List.dedup` that keep the first occurrence counting from
the right (`dedupFromRight`) and the last occurrence counting from the left
(`dedupKeepingLast`). -/

/-- `dedupFromRight xs` removes duplicates from `xs`, keeping the first occurrence
from the right (which is the last occurrence when reading left-to-right).

`dedupFromRight xs = xs.reverse.dedup`. -/
def dedupFromRight {α : Type _} [DecidableEq α] (xs : List α) : List α :=
  xs.reverse.dedup

/-- `dedupKeepingLast xs` removes duplicates from `xs`, keeping the last occurrence
of each element (reading left-to-right).

`dedupKeepingLast xs = (dedupFromRight xs).reverse`. -/
def dedupKeepingLast {α : Type _} [DecidableEq α] (xs : List α) : List α :=
  (dedupFromRight xs).reverse

/-! ## Theorems about `dedupFromRight` -/

/-- The result of `dedupFromRight` has no duplicates. -/
theorem dedupFromRight_nodup {α : Type _} [DecidableEq α] (xs : List α) :
    (dedupFromRight xs).Nodup := by
  exact List.nodup_dedup xs.reverse

/-- `dedupFromRight xs` is a sublist of `xs.reverse`. -/
theorem dedupFromRight_sublist_reverse {α : Type _} [DecidableEq α] (xs : List α) :
    (dedupFromRight xs).Sublist xs.reverse := by
  exact List.dedup_sublist xs.reverse

/-! ## Theorems about `dedupKeepingLast` -/

/-- The result of `dedupKeepingLast` has no duplicates. -/
theorem dedupKeepingLast_nodup {α : Type _} [DecidableEq α] (xs : List α) :
    (dedupKeepingLast xs).Nodup := by
  exact List.nodup_reverse.mpr (dedupFromRight_nodup xs)

/-- An element is in `dedupKeepingLast xs` iff it is in `xs`. -/
@[simp]
theorem mem_dedupKeepingLast {α : Type _} [DecidableEq α] {x : α} {xs : List α} :
    x ∈ dedupKeepingLast xs ↔ x ∈ xs := by
  simp [dedupKeepingLast, dedupFromRight]

/-- For every element `x` in `dedupKeepingLast xs`, the count of `x` in the
result is exactly 1, and `x` is in the original list `xs`. -/
theorem forall_mem_dedupKeepingLast_count_and_mem {α : Type _} [DecidableEq α]
    (xs : List α) :
    ∀ x ∈ dedupKeepingLast xs, (dedupKeepingLast xs).count x = 1 ∧ x ∈ xs := by
  intro x hx
  exact ⟨List.count_eq_one_of_mem (dedupKeepingLast_nodup xs) hx,
    (mem_dedupKeepingLast.mp hx)⟩

/-- `dedupKeepingLast` collapses duplicates: `dedupKeepingLast [x, x] = [x]`. -/
@[simp]
theorem dedupKeepingLast_pair_eq {α : Type _} [DecidableEq α] (x : α) :
    dedupKeepingLast [x, x] = [x] := by
  simp [dedupKeepingLast, dedupFromRight]

end List

end Specific
