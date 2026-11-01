import Mathlib.Data.List.Basic

namespace Specific

open _root_.List

namespace List

/-! ## Removing elements from lists -/

/-- Remove the first occurrence of `x` from the list. If `x` is not present,
the list is returned unchanged. -/
def eraseFirst [DecidableEq α] (x : α) : List α → List α
  | [] => []
  | y :: ys => if y = x then ys else y :: eraseFirst x ys

@[simp]
theorem eraseFirst_nil [DecidableEq α] (x : α) : eraseFirst x [] = [] := rfl

@[simp]
theorem eraseFirst_cons_self [DecidableEq α] (x : α) (xs : List α) :
    eraseFirst x (x :: xs) = xs := by
  simp [eraseFirst]

theorem eraseFirst_cons_ne [DecidableEq α] {x y : α} (h : y ≠ x) (xs : List α) :
    eraseFirst x (y :: xs) = y :: eraseFirst x xs := by
  simp [eraseFirst, h]

end List

end Specific
