namespace Specific
namespace Prod

/-! ## Swap pair -/

/-- Swaps the components of two arguments, producing a pair `(y, x)`.
This is equivalent to `(y, x)` but as a named function for readability. -/
def pairSwap {α : Type u} {β : Type v} (x : α) (y : β) : β × α :=
  (y, x)

@[simp]
theorem pairSwap_fst {α : Type u} {β : Type v} (x : α) (y : β) :
    (pairSwap x y).fst = y := by
  rfl

@[simp]
theorem pairSwap_snd {α : Type u} {β : Type v} (x : α) (y : β) :
    (pairSwap x y).snd = x := by
  rfl

/-- When the two arguments have the same type and are unequal, the swapped
pair differs from the original in both components. -/
theorem pairSwap_ne_components {α : Type u} {x y : α} (h_ne : x ≠ y) :
    (pairSwap x y).fst ≠ x ∧ (pairSwap x y).snd ≠ y := by
  constructor
  · intro h_eq
    exact h_ne h_eq.symm
  · intro h_eq
    exact h_ne h_eq

/-- Full specification of `pairSwap` for equal-type arguments:
the components are swapped, and inequality is preserved. -/
theorem pairSwap_same_type_spec {α : Type u} (x y : α) :
    (pairSwap x y).fst = y ∧ (pairSwap x y).snd = x ∧
      (x ≠ y → (pairSwap x y).fst ≠ x ∧ (pairSwap x y).snd ≠ y) := by
  constructor
  · exact pairSwap_fst x y
  constructor
  · exact pairSwap_snd x y
  · intro h_ne
    exact pairSwap_ne_components h_ne

end Prod

end Specific
