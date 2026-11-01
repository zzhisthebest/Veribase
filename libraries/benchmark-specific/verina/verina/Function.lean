namespace Specific
namespace Function

/-! ## Constant function combinators -/

universe u v w

/-- A two-argument constant function that ignores both arguments
and returns the given `value`. -/
def const2 {α : Sort u} {β : Sort v} {γ : Sort w}
    (value : γ) (_ : α) (_ : β) : γ :=
  value

@[simp]
theorem const2_apply {α : Sort u} {β : Sort v} {γ : Sort w}
    (value : γ) (a : α) (b : β) :
    const2 value a b = value := by
  rfl

theorem const2_nat_nonnegative {α : Sort u} {β : Sort v}
    (value : Nat) (a : α) (b : β) :
    const2 value a b ≥ 0 :=
  Nat.zero_le _

theorem const2_nat_le {α : Sort u} {β : Sort v}
    (value bound : Nat) (a : α) (b : β) (h : value ≤ bound) :
    const2 value a b ≤ bound := by
  simpa [const2] using h

/-! ## Indicator function -/

/-- Returns `1` if `x` equals `target`, `0` otherwise. A `Nat`-valued
indicator function for decidable equality. -/
def indicator {α : Type u} [DecidableEq α] (target : α) (x : α) : Nat :=
  if x = target then 1 else 0

@[simp] theorem indicator_self {α : Type u} [DecidableEq α] (a : α) :
    indicator a a = 1 := by
  simp [indicator]

theorem indicator_ne {α : Type u} [DecidableEq α] {a b : α} (h : a ≠ b) :
    indicator a b = 0 := by
  simp [indicator, h.symm]

end Function

end Specific
