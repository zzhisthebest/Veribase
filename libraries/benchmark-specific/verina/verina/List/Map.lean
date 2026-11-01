import Mathlib

namespace Specific

open _root_.List

namespace List

/-!
# `map` theorems

Properties of `List.map` relating to element access and other operations.
-/

/--
`getElem!` on a mapped list equals applying `f` to the `getElem!` of the original list,
provided the index is within bounds of the original list.
-/
theorem getElem!_map {α : Type u} {β : Type v} [Inhabited α] [Inhabited β]
    (f : α → β) (values : List α) {i : Nat} (h : i < values.length) :
    (values.map f)[i]! = f values[i]! := by
  induction values generalizing i with
  | nil =>
      simp at h
  | cons value values ih =>
      cases i with
      | zero =>
          simp
      | succ i =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
          simpa using ih h

end List

end Specific
