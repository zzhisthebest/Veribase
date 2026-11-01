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

/-- `DecreasingByIndex xs` asserts that `xs[i] ≥ xs[j]` for all `i < j`.
This is a specialization of `OrderedByIndex` with the non-strict `≥` relation. -/
def DecreasingByIndex {α : Type u} [LE α] (xs : List α) : Prop :=
  OrderedByIndex (· ≥ ·) xs

/-! ## Index-based ordering predicate (Nat-based)

`RelOrderedAt` is an alternative formulation of `OrderedByIndex` that uses `Nat`
indices with explicit proofs instead of `Fin`. This formulation appears frequently
when working with list indices where `Fin`-based reasoning is less convenient.
The two are equivalent; use `relOrderedAt_iff_orderedByIndex` to translate. -/

/-- `RelOrderedAt r xs` asserts that for any two `Nat` indices `i < j` in `xs`,
the relation `r` holds between `xs[i]` and `xs[j]`.
This is an alternative formulation of `OrderedByIndex` using `Nat` indices
instead of `Fin`. -/
def RelOrderedAt {α : Type u} (r : α → α → Prop) (xs : List α) : Prop :=
  ∀ i j, (hij : i < j) → (hj : j < xs.length) →
    r (xs.get ⟨i, Nat.lt_trans hij hj⟩) (xs.get ⟨j, hj⟩)

/-- `RelOrderedAt` is equivalent to `OrderedByIndex`. -/
theorem relOrderedAt_iff_orderedByIndex {α : Type u} (r : α → α → Prop) (xs : List α) :
    RelOrderedAt r xs ↔ OrderedByIndex r xs := by
  constructor
  · intro h i j hij
    have hi : i.val < xs.length := Nat.lt_trans hij j.is_lt
    exact h i.val j.val hij j.is_lt
  · intro h i j hij hj
    have hi : i < xs.length := Nat.lt_trans hij hj
    let fi : Fin xs.length := ⟨i, hi⟩
    let fj : Fin xs.length := ⟨j, hj⟩
    exact h fi fj hij

end List

end Specific
