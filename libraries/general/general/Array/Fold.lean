import Mathlib
import general.List.Sort
import general.Finite.Core

namespace Array


/-! ### General foldl lemmas -/

/-- `foldl` distributes over `push`: folding over `arr.push x` is equivalent to
applying `f` to the result of folding `arr` and the new element `x`. -/

theorem foldl_push (f : α → β → α) (init : α) (arr : Array β) (x : β) :
    (arr.push x).foldl f init = f (arr.foldl f init) x := by
  rw [Array.push_eq_append, Array.foldl_append]
  simp



/-! ### Except-self fold — fold over all elements except one at a given index -/

/-- Fold `f` over all array elements except the one at index `i`.
Starting from `init`, for each index `j ≠ i` we apply `f acc arr[j]!`;
when `j = i`, the accumulator passes through unchanged.

This is the "except self" fold pattern, used in problems where you need to
compute `f` over all elements except each one in turn (e.g., product except self,
sum except self). The index `i` is given as a `Fin arr.size` to guarantee it is
in bounds. -/
def foldlExceptIdx {α β : Type} [Inhabited α] (arr : Array α) (i : Fin arr.size) (f : β → α → β) (init : β) : β :=
  (List.range arr.size).foldl
    (fun (acc : β) (j : Nat) =>
      if j = (i : Nat) then acc else f acc arr[j]!)
    init

/-- Product of all array elements except the one at a given index.
Specialization of `foldlExceptIdx` with multiplication and `1` as the identity element. -/
def productExceptIdx {α : Type} [Mul α] [One α] [Inhabited α] (arr : Array α) (i : Fin arr.size) : α :=
  foldlExceptIdx arr i (· * ·) 1


end Array
