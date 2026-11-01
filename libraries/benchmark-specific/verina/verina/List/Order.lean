import Mathlib.Data.List.Basic

namespace Specific

open _root_.List

namespace List

/-! ## Index-based ordering predicate -/

/-- `OrderedByIndex rel xs` asserts that for any two indices `i < j` in `xs`,
the relation `rel` holds between `xs[i]` and `xs[j]`.
This is an alternative to `List.Sorted` that uses `Fin`-based indexing. -/
def OrderedByIndex {α : Type u} (rel : α → α → Prop) (xs : List α) : Prop :=
  ∀ i j : Fin xs.length, i.val < j.val → rel xs[i] xs[j]

/-- `IncreasingByIndex xs` asserts that `xs[i] < xs[j]` for all `i < j`.
This is a specialization of `OrderedByIndex` with the strict `<` relation. -/
def IncreasingByIndex {α : Type u} [LT α] (xs : List α) : Prop :=
  OrderedByIndex (· < ·) xs

end List

end Specific
