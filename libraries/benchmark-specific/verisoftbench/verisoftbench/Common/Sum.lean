import Mathlib.Data.Sum.Basic

open Sum

/-- `Sum.elim Sum.inl Sum.inr` is equal to the identity function on a sum type. -/
@[simp]
lemma sum_elim_inl_inr_eq_id {α : Type u} {β : Type v} :
    (Sum.elim Sum.inl Sum.inr : (α ⊕ β) → (α ⊕ β)) = id := by
  ext x; cases x <;> rfl
